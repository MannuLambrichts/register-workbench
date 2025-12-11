import './App.css'

import { useEffect, useMemo, useState } from "react";

// --- Utilities ---
/*
function clamp(n: number, lo: number, hi: number) {
	return Math.min(hi, Math.max(lo, n));
}
*/

function parseNumber(input: string): { ok: true; value: bigint } | { ok: false } {
	if (!input.trim()) return { ok: true, value: 0n };
	const s = input.trim().replaceAll('_', '').toLowerCase();
	try {
		if (s.startsWith('0x')) return { ok: true, value: BigInt(s) };
		if (s.startsWith('0b')) return { ok: true, value: BigInt(s) };
		if (s.startsWith('0o')) return { ok: true, value: BigInt(s) };
		// Allow binary with 1010b or hex with 1Fh suffixes
		if (s.endsWith('b') && /^[01]+b$/.test(s)) return { ok: true, value: BigInt('0b' + s.slice(0, -1)) };
		if (s.endsWith('h') && /^[0-9a-f]+h$/.test(s)) return { ok: true, value: BigInt('0x' + s.slice(0, -1)) };
		// Decimal fallback
		if (/^[+-]?[0-9]+$/.test(s)) return { ok: true, value: BigInt(s) };
		// Hex without prefix
		if (/^[0-9a-f]+$/.test(s)) return { ok: true, value: BigInt('0x' + s) };
	} catch {
		return { ok: false };
	}
	return { ok: false };
}

function toBin(v: bigint, bits: number) {
	const s = v.toString(2);
	return s.padStart(bits, '0');
}

function maskForWidth(width: number): bigint {
	return width >= 64 ? (1n << 64n) - 1n : (1n << BigInt(width)) - 1n;
}

function signedFromUnsigned(u: bigint, width: number): bigint {
	if (width <= 0) return 0n;
	const signBit = 1n << BigInt(width - 1);
	const mod = 1n << BigInt(width);
	return (u & signBit) ? (u - mod) : u;
}

function chunkString(str: string, size: number) {
	const out: string[] = [];
	for (let i = 0; i < str.length; i += size) out.push(str.slice(i, i + size));
	return out;
}

function hexBytesLE(value: bigint, width: number): string[] {
	const bytes = Math.ceil(width / 8);
	const out: string[] = [];
	for (let i = 0; i < bytes; i++) {
		const b = Number((value >> BigInt(8 * i)) & 0xffn);
		out.push(b.toString(16).padStart(2, '0'));
	}
	return out; // little-endian order
}

// Parse simple label spec like: "7:READY,5-3:MODE,0:EN"
function parseLabels(spec: string): Array<{ start: number; end: number; name: string }> {
	const parts = spec.split(',').map(p => p.trim()).filter(Boolean);
	const ranges: Array<{ start: number; end: number; name: string }> = [];
	for (const p of parts) {
		const [lhs, nameRaw] = p.split(':');
		const name = (nameRaw ?? '').trim() || p;
		if (!lhs) continue;
		if (/^[0-9]+-[0-9]+$/.test(lhs)) {
			const [hi, lo] = lhs.split('-').map(n => parseInt(n, 10));
			const start = Math.max(hi, lo);
			const end = Math.min(hi, lo);
			ranges.push({ start, end, name });
		} else if (/^[0-9]+$/.test(lhs)) {
			const b = parseInt(lhs, 10);
			ranges.push({ start: b, end: b, name });
		}
	}
	return ranges;
}

// --- Float helpers ---

function float32ToBits(v: number): bigint {
	const buf = new ArrayBuffer(4);
	const dv = new DataView(buf);
	// Use big-endian consistently for bit layout
	dv.setFloat32(0, v, false);
	const u = dv.getUint32(0, false);
	return BigInt(u >>> 0);
}

function bitsToFloat32(bits: bigint): number {
	const buf = new ArrayBuffer(4);
	const dv = new DataView(buf);
	const masked = Number(bits & ((1n << 32n) - 1n));
	dv.setUint32(0, masked >>> 0, false);
	return dv.getFloat32(0, false);
}

function float64ToBits(v: number): bigint {
	const buf = new ArrayBuffer(8);
	const dv = new DataView(buf);
	dv.setFloat64(0, v, false);
	const hi = dv.getUint32(0, false);
	const lo = dv.getUint32(4, false);
	return (BigInt(hi >>> 0) << 32n) | BigInt(lo >>> 0);
}

function bitsToFloat64(bits: bigint): number {
	const buf = new ArrayBuffer(8);
	const dv = new DataView(buf);
	const hi = Number((bits >> 32n) & 0xffffffffn);
	const lo = Number(bits & 0xffffffffn);
	dv.setUint32(0, hi >>> 0, false);
	dv.setUint32(4, lo >>> 0, false);
	return dv.getFloat64(0, false);
}

function decomposeFloat(bits: bigint, mode: 'f32' | 'f64') {
	const totalBits = mode === 'f32' ? 32 : 64;
	const expBits = mode === 'f32' ? 8 : 11;
	const fracBits = totalBits - 1 - expBits;
	const bias = mode === 'f32' ? 127 : 1023;

	const masked = bits & maskForWidth(totalBits);
	const bitStr = toBin(masked, totalBits);
	const signBit = bitStr[0];
	const expStr = bitStr.slice(1, 1 + expBits);
	const fracStr = bitStr.slice(1 + expBits);

	const expRaw = parseInt(expStr, 2);
	const fracRaw = fracStr === '' ? 0 : parseInt(fracStr, 2);

	const sign = signBit === '0' ? 1 : -1;
	const maxExp = (1 << expBits) - 1;

	let kind = 'normal';
	let exponent: number | '∞' | '-∞' | 'NaN';
	let mantissaDescr: string;

	if (expRaw === 0) {
		if (fracRaw === 0) {
			kind = 'zero';
			exponent = 1 - bias;
			mantissaDescr = '0.0';
		} else {
			kind = 'subnormal';
			exponent = 1 - bias;
			mantissaDescr = '0.' + fracStr;
		}
	} else if (expRaw === maxExp) {
		if (fracRaw === 0) {
			kind = 'infinity';
			exponent = sign > 0 ? '∞' : '-∞';
			mantissaDescr = 'n/a';
		} else {
			kind = 'NaN';
			exponent = 'NaN';
			mantissaDescr = 'n/a';
		}
	} else {
		kind = 'normal';
		exponent = expRaw - bias;
		mantissaDescr = '1.' + fracStr;
	}

	return {
		totalBits,
		expBits,
		fracBits,
		signBit,
		expStr,
		fracStr,
		expRaw,
		exponent,
		kind,
		mantissaDescr,
		bits: masked,
		bitStr,
	};
}

function formatFloat(v: number): string {
	if (Number.isNaN(v)) return 'NaN';
	if (!Number.isFinite(v)) return v > 0 ? 'Infinity' : '-Infinity';
	// Avoid overly long scientific strings
	const s = v.toString();
	return s.length > 18 ? v.toExponential(10) : s;
}

// ---- Expression Calculator (BigInt) ----
// Supported: + - * / % & | ^ << >> ~ and parentheses, with 0x.., 0b.., 0o.., ...h, ...b, decimal.
// Underscores allowed in literals. Unary minus and bitwise not supported.

type NumVal =
	| { kind: 'int'; i: bigint }
	| { kind: 'float'; f: number };

type Tok =
	| { type: 'num'; v: NumVal }
	| { type: 'op'; v: string }
	| { type: 'lpar' }
	| { type: 'rpar' };

// Custom precedence: multiplicative > bitwise AND > additive > shifts > XOR > OR
const OPS: Record<string, { prec: number; assoc: 'L' | 'R'; arity: 1 | 2 }> = {
	'~': { prec: 7, assoc: 'R', arity: 1 },
	'u-': { prec: 7, assoc: 'R', arity: 1 },
	'*': { prec: 6, assoc: 'L', arity: 2 },
	'/': { prec: 6, assoc: 'L', arity: 2 },
	'%': { prec: 6, assoc: 'L', arity: 2 },
	'&': { prec: 6, assoc: 'L', arity: 2 },
	'+': { prec: 5, assoc: 'L', arity: 2 },
	'-': { prec: 5, assoc: 'L', arity: 2 },
	'<<': { prec: 4, assoc: 'L', arity: 2 },
	'>>': { prec: 4, assoc: 'L', arity: 2 },
	'^': { prec: 2, assoc: 'L', arity: 2 },
	'|': { prec: 1, assoc: 'L', arity: 2 },
};

function tokenize(expr: string): Tok[] {
	const s = expr.replace(/_/g, '').trim();
	const toks: Tok[] = [];
	let i = 0;

	const makeInt = (iVal: bigint): NumVal => ({ kind: 'int', i: iVal });
	const makeFloat = (fVal: number): NumVal => ({ kind: 'float', f: fVal });

	while (i < s.length) {
		const ch = s[i];
		if (/\s/.test(ch)) { i++; continue; }

		const rest = s.slice(i);

		// --- Floating-point literals: 1.23, .5, 3., 1.2e-3, .5E+2, etc. (no leading sign here) ---
		const floatMatch = /^(?:\d+\.\d*|\d*\.\d+)(?:[eE][+-]?\d+)?/.exec(rest);
		if (floatMatch) {
			const lit = floatMatch[0];
			const v = Number(lit);
			if (!Number.isFinite(v)) throw new Error('Invalid float literal: ' + lit);
			toks.push({ type: 'num', v: makeFloat(v) });
			i += lit.length;
			continue;
		}

		// --- Prefixed integers: 0x.., 0b.., 0o.. ---
		if (ch === '0' && (s[i + 1]?.toLowerCase() === 'x' || s[i + 1]?.toLowerCase() === 'b' || s[i + 1]?.toLowerCase() === 'o')) {
			const base = s[i + 1].toLowerCase();
			let j = i + 2;
			const re = base === 'x' ? /[0-9a-f]/i : base === 'b' ? /[01]/ : /[0-7]/;
			while (j < s.length && re.test(s[j])) j++;
			const lit = s.slice(i, j);
			toks.push({ type: 'num', v: makeInt(BigInt(lit)) });
			i = j;
			continue;
		}

		// --- Bare hex/dec with optional h/b suffix, or plain decimal ---
		if (/[0-9a-f]/i.test(ch)) {
			let j = i;
			while (j < s.length && /[0-9a-f]/i.test(s[j])) j++;

			// suffixes 10h / 1010b
			if (s[j]?.toLowerCase() === 'h') {
				toks.push({ type: 'num', v: makeInt(BigInt('0x' + s.slice(i, j))) });
				i = j + 1;
				continue;
			}
			if (s[j]?.toLowerCase() === 'b' && /^[01]+$/i.test(s.slice(i, j))) {
				toks.push({ type: 'num', v: makeInt(BigInt('0b' + s.slice(i, j))) });
				i = j + 1;
				continue;
			}

			const raw = s.slice(i, j);

			// hex without prefix (deadbeef)
			if (/[a-f]/i.test(raw)) {
				toks.push({ type: 'num', v: makeInt(BigInt('0x' + raw)) });
				i = j;
				continue;
			}

			// plain decimal integer
			toks.push({ type: 'num', v: makeInt(BigInt(raw)) });
			i = j;
			continue;
		}

		// --- Operators (multi-char first) ---
		const two = s.slice(i, i + 2);
		if (two === '<<' || two === '>>') { toks.push({ type: 'op', v: two }); i += 2; continue; }
		if ('+-*/%&|^~'.includes(ch)) { toks.push({ type: 'op', v: ch }); i++; continue; }

		if (ch === '(') { toks.push({ type: 'lpar' }); i++; continue; }
		if (ch === ')') { toks.push({ type: 'rpar' }); i++; continue; }

		throw new Error('Unexpected character: ' + ch);
	}

	// fix unary operators
	const out: Tok[] = [];
	for (let k = 0; k < toks.length; k++) {
		const t = toks[k];
		if (t.type === 'op' && t.v === '-') {
			const prev = out[out.length - 1];
			if (!prev || prev.type === 'op' || prev.type === 'lpar') out.push({ type: 'op', v: 'u-' });
			else out.push(t);
		} else {
			out.push(t);
		}
	}
	return out;
}

function toRPN(toks: Tok[]): Tok[] {
	const out: Tok[] = [];
	const stack: Tok[] = [];
	for (const t of toks) {
		if (t.type === 'num') out.push(t);
		else if (t.type === 'op') {
			const o1 = t.v;
			while (stack.length) {
				const top = stack[stack.length - 1];
				if (top.type !== 'op') break;
				const o2 = (top as any).v as string;
				const p1 = OPS[o1].prec, p2 = OPS[o2].prec;
				if ((OPS[o1].assoc === 'L' && p1 <= p2) || (OPS[o1].assoc === 'R' && p1 < p2)) {
					out.push(stack.pop() as Tok);
				} else break;
			}
			stack.push(t);
		} else if (t.type === 'lpar') stack.push(t);
		else if (t.type === 'rpar') {
			while (stack.length && stack[stack.length - 1].type !== 'lpar') out.push(stack.pop() as Tok);
			if (!stack.length) throw new Error('Mismatched parentheses');
			stack.pop();
		}
	}
	while (stack.length) {
		const x = stack.pop() as Tok;
		if (x.type === 'lpar' || x.type === 'rpar') throw new Error('Mismatched parentheses');
		out.push(x);
	}
	return out;
}

function evalRPN(rpn: Tok[], widthMask?: bigint): NumVal {
	const st: NumVal[] = [];
	const mask = widthMask ?? undefined;

	const applyMask = (v: NumVal): NumVal => {
		if (mask === undefined) return v;
		if (v.kind === 'int') return { kind: 'int', i: v.i & mask };
		// Masking floats does not make sense here; leave them as-is.
		return v;
	};

	for (const t of rpn) {
		if (t.type === 'num') {
			st.push(applyMask(t.v));
		} else if (t.type === 'op') {
			const op = t.v;

			if (OPS[op].arity === 1) {
				const a = st.pop();
				if (!a) throw new Error('Stack underflow');

				if (op === '~') {
					if (a.kind !== 'int') throw new Error('Bitwise NOT only supported on integers');
					const r: NumVal = { kind: 'int', i: ~a.i };
					st.push(applyMask(r));
				} else if (op === 'u-') {
					const r: NumVal =
						a.kind === 'int'
							? { kind: 'int', i: -a.i }
							: { kind: 'float', f: -a.f };
					st.push(applyMask(r));
				} else {
					throw new Error('Unknown unary op');
				}
			} else {
				const b = st.pop();
				const a = st.pop();
				if (!a || !b) throw new Error('Stack underflow');

				const isBitwise = op === '&' || op === '|' || op === '^' || op === '<<' || op === '>>';

				if (isBitwise) {
					if (a.kind !== 'int' || b.kind !== 'int') {
						throw new Error('Bitwise and shift operators only support integer operands');
					}
					let rInt: bigint;
					switch (op) {
						case '&': rInt = a.i & b.i; break;
						case '|': rInt = a.i | b.i; break;
						case '^': rInt = a.i ^ b.i; break;
						case '<<': rInt = a.i << b.i; break;
						case '>>': rInt = a.i >> b.i; break;
						default: throw new Error('Unknown bitwise op ' + op);
					}
					st.push(applyMask({ kind: 'int', i: rInt }));
					continue;
				}

				// Arithmetic operators: + - * / %
				const aIsFloat = a.kind === 'float';
				const bIsFloat = b.kind === 'float';

				if (!aIsFloat && !bIsFloat) {
					// pure integer arithmetic (BigInt)
					let rInt: bigint;
					switch (op) {
						case '+': rInt = a.i + b.i; break;
						case '-': rInt = a.i - b.i; break;
						case '*': rInt = a.i * b.i; break;
						case '/':
							if (b.i === 0n) throw new Error('Division by zero');
							rInt = a.i / b.i; // integer division as before
							break;
						case '%':
							if (b.i === 0n) throw new Error('Modulo by zero');
							rInt = a.i % b.i;
							break;
						default:
							throw new Error('Unknown arithmetic op ' + op);
					}
					st.push(applyMask({ kind: 'int', i: rInt }));
				} else {
					// At least one operand is float: promote both to JS numbers
					const av = a.kind === 'float' ? a.f : Number(a.i);
					const bv = b.kind === 'float' ? b.f : Number(b.i);
					let rf: number;

					switch (op) {
						case '+': rf = av + bv; break;
						case '-': rf = av - bv; break;
						case '*': rf = av * bv; break;
						case '/':
							if (bv === 0) throw new Error('Division by zero');
							rf = av / bv;
							break;
						case '%':
							if (bv === 0) throw new Error('Modulo by zero');
							rf = av % bv;
							break;
						default:
							throw new Error('Unknown arithmetic op ' + op);
					}

					if (!Number.isFinite(rf)) throw new Error('Float result is not finite');
					st.push({ kind: 'float', f: rf });
				}
			}
		}
	}

	if (st.length !== 1) throw new Error('Invalid expression');
	return st[0];
}

function evalExpression(expr: string, width: number, maskExprToWidth: boolean) {
	try {
		if (!expr.trim()) return { ok: true as const, value: 0n };
		const toks = tokenize(expr);
		const rpn = toRPN(toks);
		const m = maskExprToWidth ? maskForWidth(width) : undefined;
		const val = evalRPN(rpn, m as any); // NumVal

		if (val.kind === 'int') {
			// Integer-only expression: keep previous semantics
			return { ok: true as const, value: val.i, float: Number(val.i) };
		} else {
			// Float expression: interpret the numeric result as f64 IEEE bits
			const bits = (maskExprToWidth && width == 32) ? float32ToBits(val.f) : float64ToBits(val.f);
			return { ok: true as const, value: bits, float: val.f };
		}
	} catch (e: any) {
		return { ok: false as const, error: e?.message ?? String(e) };
	}
}

function safeName(s: string) {
	return s.replace(/[^A-Za-z0-9_]/g, '_').toUpperCase();
}

// --- Component ---

type Calc = { id: number; expr: string };

type MemEntry = { id: number; label: string; value: bigint; created: number };

type Test = { expr: string; expectDec: string };

export default function RegisterWorkbench() {
	const [theme, setTheme] = useState<'dark' | 'light'>(() => {
		if (typeof window === 'undefined') return 'dark';

		const stored = window.localStorage.getItem('registerWorkbenchTheme');
		if (stored === 'light' || stored === 'dark') return stored;

		if (window.matchMedia && window.matchMedia('(prefers-color-scheme: dark)').matches) {
			return 'dark';
		}

		return 'light';
	});

	// Keep theme in sync with system preference (only influences first explicit choice)
	useEffect(() => {
		if (typeof window === 'undefined') return;

		const mq = window.matchMedia('(prefers-color-scheme: dark)');

		// If there is no stored preference yet, update theme when system preference changes
		const stored = window.localStorage.getItem('registerWorkbenchTheme');
		if (stored !== 'light' && stored !== 'dark') {
			const handler = (e: MediaQueryListEvent) => {
				setTheme(e.matches ? 'dark' : 'light');
			};
			mq.addEventListener('change', handler);
			return () => mq.removeEventListener('change', handler);
		}
	}, []);

	// Persist theme in localStorage whenever it changes
	useEffect(() => {
		if (typeof window === 'undefined') return;
		window.localStorage.setItem('registerWorkbenchTheme', theme);
	}, [theme]);



	const [width, setWidth] = useState<number>(32);
	const [maskExprToWidth, setMaskExprToWidth] = useState<boolean>(false);
	const [signedView, setSignedView] = useState<boolean>(false);
	const [input, setInput] = useState<string>('0x2612_2018');
	const [labelSpec, setLabelSpec] = useState<string>(`31-24:RSV, 23:ERR, 22-16:MD, 15:RDY, 8:EN, 7-0:VAL`);

	// Multiple calculator instances
	const [calcs, setCalcs] = useState<Calc[]>([
		{ id: 0, expr: '0x45 & 0b100001 + 9' },
	]);
	const [nextCalcId, setNextCalcId] = useState(1);

	// Calculator memory entries
	const [memory, setMemory] = useState<MemEntry[]>([]);
	const [nextMemId, setNextMemId] = useState(1);

	// ASCII converter
	const [asciiText, setAsciiText] = useState<string>('HELLO');
	const [asciiNums, setAsciiNums] = useState<string>('0x48 0x45 0x4C 0x4C 0x4F');

	// Floating-point converter state
	const [floatMode, setFloatMode] = useState<'f32' | 'f64'>('f32');
	const [floatValueInput, setFloatValueInput] = useState<string>('1.0');
	const [floatBitsInput, setFloatBitsInput] = useState<string>('0x3f800000');

	const parsed = useMemo(() => parseNumber(input), [input]);
	const uval = useMemo(() => {
		if (!parsed.ok) return 0n;
		const v = parsed.value & maskForWidth(width);
		return v;
	}, [parsed, width]);
	const sval = useMemo(() => signedFromUnsigned(uval, width), [uval, width]);

	const binStr = useMemo(() => toBin(uval, width), [uval, width]);
	const labels = useMemo(() => parseLabels(labelSpec), [labelSpec]);

	function setBit(bit: number, on: boolean) {
		const current = uval;
		const nv = on ? (current | (1n << BigInt(bit))) : (current & ~(1n << BigInt(bit)));
		setInput('0x' + nv.toString(16));
	}

	function applyMasks(setMaskStr: string, clrMaskStr: string) {
		const s = parseNumber(setMaskStr);
		const c = parseNumber(clrMaskStr);
		const setMask = s.ok ? (s.value & maskForWidth(width)) : 0n;
		const clrMask = c.ok ? (c.value & maskForWidth(width)) : 0n;
		const nv = (uval | setMask) & ~clrMask & maskForWidth(width);
		setInput('0x' + nv.toString(16));
	}

	function extractField(start: number, len: number): bigint {
		const m = (1n << BigInt(len)) - 1n;
		return (uval >> BigInt(start - len + 1)) & m;
	}
	function insertField(start: number, len: number, val: bigint) {
		const m = ((1n << BigInt(len)) - 1n) << BigInt(start - len + 1);
		const v = (uval & ~m) | ((val << BigInt(start - len + 1)) & m);
		setInput('0x' + (v & maskForWidth(width)).toString(16));
	}

	// Field editor state
	const [fieldHi, setFieldHi] = useState<number>(7);
	const [fieldLo, setFieldLo] = useState<number>(0);
	const fieldLen = Math.min(Math.max(fieldHi - fieldLo + 1, 1), width);
	const [fieldValInput, setFieldValInput] = useState<string>('0');
	const fieldValue = useMemo(() => {
		const start = fieldHi;
		const len = fieldLen;
		const v = extractField(start, len);
		return v;
	}, [uval, fieldHi, fieldLen]);

	// Masks panel local state
	const [setMaskStr, setSetMask] = useState<string>('0');
	const [clrMaskStr, setClrMask] = useState<string>('0');

	const leBytes = useMemo(() => hexBytesLE(uval, width), [uval, width]);
	const beBytes = [...leBytes].reverse();

	const codeGen = useMemo(() => {
		const defs: string[] = [];
		defs.push('#define BIT(n) (1u << (n))');
		defs.push('#define GEN_MASK(hi,lo) (((0xFFFFFFFFu >> (31-((hi))) ) ) & (0xFFFFFFFFu << (lo)))');
		for (const r of labels) {
			if (r.start === r.end) {
				defs.push(`#define ${safeName(r.name)} (BIT(${r.start}))`);
			} else {
				defs.push(`#define ${safeName(r.name)}_MASK ( ((1u<<(${r.start - r.end + 1}))-1u) << (${r.end}) )`);
				defs.push(`#define ${safeName(r.name)}_SET(v) (((v) & ((1u<<(${r.start - r.end + 1}))-1u)) << (${r.end}))`);
				defs.push(`#define ${safeName(r.name)}_GET(x) (((x) >> (${r.end})) & ((1u<<(${r.start - r.end + 1}))-1u))`);
			}
		}
		return defs.join('\n');
	}, [labels]);

	// Calculator self-tests
	const tests: Test[] = [
		{ expr: '0x45 & 0b100001 + 9', expectDec: '10' }, // (0x45 & 0b100001) + 9 = 10 with our precedence
		{ expr: '(1<<3) | 5', expectDec: '13' },
		{ expr: '~0x3 & 0xFF', expectDec: '252' },
		{ expr: '0o77 * 3 - 10', expectDec: String(63 * 3 - 10) },
		{ expr: '1 + 3 & 1', expectDec: '2' }, // 1 + (3 & 1) = 2
	];

	const testResults = useMemo(() => {
		return tests.map(t => {
			try {
				const val = evalExpression(t.expr, 32, true);
				if (!val.ok) return { ...t, ok: false, got: val.error };
				return { ...t, ok: (val.value.toString() === t.expectDec), got: val.value.toString() };
			} catch (e: any) {
				return { ...t, ok: false, got: e?.message ?? String(e) };
			}
		});
	}, []);

	// ASCII converter derived state
	const asciiTextCodes = useMemo(() => {
		const hex: string[] = [];
		const dec: string[] = [];
		for (const ch of asciiText) {
			const code = ch.charCodeAt(0);
			hex.push(code.toString(16).padStart(2, '0'));
			dec.push(code.toString(10));
		}
		return { hex, dec };
	}, [asciiText]);

	const asciiNumsResult = useMemo(() => {
		const tokens = asciiNums.split(/[\s,]+/).filter(Boolean);
		let out = '';
		for (const t of tokens) {
			const p = parseNumber(t);
			if (!p.ok) continue;
			const v = Number(p.value & 0xffn);
			out += String.fromCharCode(v);
		}
		return out;
	}, [asciiNums]);

	// USE THESE
	const floatFromValue = useMemo(() => {
		const trimmed = floatValueInput.trim();
		if (!trimmed) return { ok: false as const, error: 'Empty' };
		const v = Number(trimmed);
		if (!Number.isFinite(v)) return { ok: false as const, error: 'Not a finite number' };
		try {
			if (floatMode === 'f32') {
				const bits = float32ToBits(v);
				return { ok: true as const, bits };
			} else {
				const bits = float64ToBits(v);
				return { ok: true as const, bits };
			}
		} catch (e: any) {
			return { ok: false as const, error: e?.message ?? String(e) };
		}
	}, [floatValueInput, floatMode]);

	// USE THESE
	const floatFromBits = useMemo(() => {
		const trimmed = floatBitsInput.trim();
		if (!trimmed) return { ok: false as const, error: 'Empty' };
		const p = parseNumber(trimmed);
		if (!p.ok) return { ok: false as const, error: 'Invalid bits' };
		try {
			const modeBits = floatMode === 'f32' ? 32 : 64;
			const maskedBits = p.value & maskForWidth(modeBits);
			if (floatMode === 'f32') {
				const val = bitsToFloat32(maskedBits);
				return { ok: true as const, value: val, bits: maskedBits };
			} else {
				const val = bitsToFloat64(maskedBits);
				return { ok: true as const, value: val, bits: maskedBits };
			}
		} catch (e: any) {
			return { ok: false as const, error: e?.message ?? String(e) };
		}
	}, [floatBitsInput, floatMode]);

	const floatLayout = useMemo(() => {
		const modeBits = floatMode === 'f32' ? 32 : 64;
		const mask = maskForWidth(modeBits);
		let bits: bigint | null = null;

		if (floatFromBits.ok) bits = floatFromBits.bits & mask;
		else if (floatFromValue.ok) bits = floatFromValue.bits & mask;

		if (bits === null) return null;
		return decomposeFloat(bits, floatMode);
	}, [floatMode, floatFromBits, floatFromValue]);

	function addCalc() {
		setCalcs(prev => [...prev, { id: nextCalcId, expr: '' }]);
		setNextCalcId(id => id + 1);
	}

	function removeCalc(id: number) {
		setCalcs(prev => (prev.length <= 1 ? prev : prev.filter(c => c.id !== id)));
	}

	function storeToMemory(value: bigint) {
		setMemory(prev => {
			const id = nextMemId;
			setNextMemId(id + 1);
			const label = `M${id}`;
			return [...prev, { id, label, value, created: Date.now() }];
		});
	}

	function useMemoryAsValue(entry: MemEntry) {
		setInput('0x' + (entry.value & maskForWidth(width)).toString(16));
	}

	function insertMemoryIntoFirstCalc(entry: MemEntry) {
		setCalcs(prev => prev.map((c, idx) => {
			if (idx !== 0) return c;
			const hex = '0x' + entry.value.toString(16);
			return { ...c, expr: c.expr ? c.expr + ' ' + hex : hex };
		}));
	}

	function clearMemory() {
		setMemory([]);
		setNextMemId(1);
	}

	return (
		<div className={theme === 'dark' ? 'dark' : ''}>
			<div className="min-h-screen w-full bg-slate-100 text-slate-900 dark:bg-bg dark:text-slate-100">
				{theme === 'dark' ? <div className="app-bg" /> : <div className="app-bg-light" />}
				<div className="app-grid" />

				<div className="mx-auto max-w-6xl px-4 py-8 md:px-6 md:py-10 relative">
					<header className="mb-6 flex flex-col gap-3 md:flex-row md:items-start md:justify-between">
						<div>
							<div className="inline-flex items-center gap-2 rounded-full border border-slate-300/80 bg-white/80 px-3 py-1 text-xs text-slate-700 shadow-soft backdrop-blur-xs dark:border-slate-800 dark:bg-slate-900/70 dark:text-slate-300">
								<span className="h-2 w-2 rounded-full bg-emerald-500 animate-pulse" />
								<span className="font-mono uppercase tracking-[0.15em] text-[10px]">
									Microcontroller Toolkit
								</span>
							</div>
							<h1 className="mt-4 text-2xl md:text-3xl font-semibold tracking-tight text-slate-900 dark:text-slate-50">
								Microcontroller Register Workbench
							</h1>
							<p className="mt-1 text-sm text-slate-600 dark:text-slate-300">
								Convert hex/decimal/binary, compute expressions with memory, inspect bitfields and
								IEEE-754 floats, and generate C-style masks.
							</p>
						</div>

						<button
							onClick={() => setTheme(t => (t === 'dark' ? 'light' : 'dark'))}
							className="self-start inline-flex items-center gap-2 rounded-full border border-slate-300 bg-white/80 px-3 py-1 text-xs font-medium text-slate-700 shadow-sm backdrop-blur-xs hover:bg-slate-100 focus:outline-none focus:ring-2 focus:ring-slate-400 dark:border-slate-700 dark:bg-slate-900/80 dark:text-slate-100 dark:hover:bg-slate-800 dark:focus:ring-slate-600"
						>
							<span className="text-lg">{theme === 'dark' ? '☀️' : '🌙'}</span>
							<span>{theme === 'dark' ? 'Light mode' : 'Dark mode'}</span>
						</button>
					</header>

					<div className="grid gap-6 md:grid-cols-5">
						{/* Left column: main value + calculators + ASCII + floats */}
						<section className="md:col-span-3 space-y-4">
							{/* Main value */}
							<div className="rounded-3xl border border-slate-200/80 bg-white/90 p-4 shadow backdrop-blur-xs dark:border-slate-800/70 dark:bg-slate-900/70">
								<div className="flex items-center justify-between gap-2">
									<div className="font-mono text-xs uppercase tracking-[0.18em] text-slate-500 dark:text-slate-400">
										Main Value
									</div>
								</div>
								<label className="mt-3 block text-xs font-medium text-slate-700 dark:text-slate-300">
									Value (hex / dec / bin)
								</label>
								<div className="mt-2 flex gap-2">
									<input
										className="flex-1 rounded-xl border border-slate-300 bg-white/90 px-3 py-2 font-mono text-sm text-slate-900 placeholder:text-slate-400 focus:outline-none focus:ring-2 focus:ring-brand-500/70 focus:border-brand-500/70 dark:border-slate-700 dark:bg-slate-900/80 dark:text-slate-100 dark:placeholder:text-slate-500"
										value={input}
										onChange={e => setInput(e.target.value)}
										placeholder="0x1F, 31, 0b11111, 1Fh, 11111b"
									/>
								</div>
								<div className="mt-3 grid grid-cols-3 gap-2">
									<div className="rounded-xl border border-slate-200 bg-white/90 p-3 dark:border-slate-800 dark:bg-slate-900/80">
										<div className="text-[11px] font-medium text-slate-500 dark:text-slate-400">
											Unsigned
										</div>
										<div className="mt-1 font-mono text-xs break-all text-slate-900 dark:text-slate-100">
											{parsed.ok ? uval.toString() : '—'}
										</div>
									</div>
									<div className="rounded-xl border border-slate-200 bg-white/90 p-3 dark:border-slate-800 dark:bg-slate-900/80">
										<div className="text-[11px] font-medium text-slate-500 dark:text-slate-400">
											Hex
										</div>
										<div className="mt-1 font-mono text-xs text-slate-900 dark:text-slate-100">
											{parsed.ok ? '0x' + uval.toString(16) : '—'}
										</div>
									</div>
									<div className="rounded-xl border border-slate-200 bg-white/90 p-3 dark:border-slate-800 dark:bg-slate-900/80">
										<div className="text-[11px] font-medium text-slate-500 dark:text-slate-400">
											Binary
										</div>
										<div className="mt-1 font-mono text-[10px] break-words text-slate-900 dark:text-slate-100">
											{parsed.ok ? chunkString(binStr, 4).join('_') : '—'}
										</div>
									</div>
								</div>
								<div className="mt-3 flex flex-wrap items-center gap-3">
									<div className="flex items-center gap-2">
										<span className="text-sm text-slate-700 dark:text-slate-300">Width</span>
										<select
											className="rounded-lg border border-slate-300 bg-white/90 px-2 py-1 text-sm text-slate-900 focus:outline-none focus:ring-2 focus:ring-brand-500/70 dark:border-slate-700 dark:bg-slate-900/80 dark:text-slate-100"
											value={width}
											onChange={e => setWidth(parseInt(e.target.value, 10))}
										>
											{[8, 16, 24, 32, 48, 64].map(w => (
												<option key={w} value={w}>
													{w}
												</option>
											))}
										</select>
									</div>
									<label className="inline-flex items-center gap-2 cursor-pointer text-sm text-slate-700 dark:text-slate-300">
										<input
											type="checkbox"
											className="h-4 w-4 rounded border-slate-300 bg-white text-brand-500 dark:border-slate-700 dark:bg-slate-900"
											checked={signedView}
											onChange={e => setSignedView(e.target.checked)}
										/>
										<span>Show signed</span>
									</label>
									{signedView && (
										<div className="text-sm font-mono px-2 py-1 rounded-lg bg-slate-100 border border-slate-300 text-slate-900 dark:bg-slate-900/90 dark:border-slate-700 dark:text-slate-100">
											{sval.toString()}
										</div>
									)}
								</div>
							</div>

							{/* Expression Calculators */}
							<div className="rounded-3xl border border-slate-200/80 bg-white/90 p-4 shadow backdrop-blur-xs space-y-3 dark:border-slate-800/70 dark:bg-slate-900/70">
								<div className="flex items-center gap-3 flex-wrap">
									<div className="font-mono text-xs uppercase tracking-[0.18em] text-slate-500 dark:text-slate-400">
										Expression Calculators
									</div>
									<label className="inline-flex items-center gap-2 cursor-pointer ml-auto text-xs text-slate-700 dark:text-slate-300">
										<input
											type="checkbox"
											className="h-3.5 w-3.5 rounded border-slate-300 bg-white text-brand-500 dark:border-slate-700 dark:bg-slate-900"
											checked={maskExprToWidth}
											onChange={e => setMaskExprToWidth(e.target.checked)}
										/>
										<span>Mask to {width}-bit</span>
									</label>
									<button
										className="rounded-xl px-3 py-1 text-xs font-medium bg-slate-100 text-slate-800 hover:bg-slate-200 focus:outline-none focus:ring-2 focus:ring-slate-300 dark:bg-slate-800/80 dark:text-slate-100 dark:hover:bg-slate-700/80 dark:focus:ring-slate-600/70"
										onClick={addCalc}
									>
										+ Add calculator
									</button>
								</div>

								<div className="space-y-3">
									{calcs.map((c, idx) => {
										const res = evalExpression(c.expr, width, maskExprToWidth);
										let floatView32: string | null = null;
										let floatView64: string | null = null;
										if (res.ok) {
											if (res.float) {
												floatView32 = formatFloat(bitsToFloat32(float32ToBits(res.float) & maskForWidth(32)));
												floatView64 = formatFloat(bitsToFloat64(float64ToBits(res.float) & maskForWidth(64)));
											} else {
												floatView32 = formatFloat(bitsToFloat32(res.value));
												floatView64 = formatFloat(bitsToFloat64(res.value));
											}
										}

										return (
											<div
												key={c.id}
												className="rounded-2xl border border-slate-200 bg-slate-50 p-3 space-y-2 shadow-soft dark:border-slate-800 dark:bg-slate-900/80"
											>
												<div className="flex items-center gap-2">
													<div className="font-mono text-[11px] uppercase tracking-[0.14em] text-slate-500 dark:text-slate-400">
														Calc {idx + 1}
													</div>
													{calcs.length > 1 && (
														<button
															className="ml-auto text-[11px] px-2 py-0.5 rounded-lg bg-slate-100 text-slate-700 hover:bg-slate-200 focus:outline-none focus:ring-1 focus:ring-slate-300 dark:bg-slate-800/80 dark:text-slate-200 dark:hover:bg-slate-700/80 dark:focus:ring-slate-600/70"
															onClick={() => removeCalc(c.id)}
														>
															Remove
														</button>
													)}
												</div>
												<input
													className="w-full rounded-xl border border-slate-300 bg-white px-3 py-2 font-mono text-sm text-slate-900 placeholder:text-slate-400 focus:outline-none focus:ring-2 focus:ring-brand-500/70 focus:border-brand-500/70 dark:border-slate-700 dark:bg-slate-950/70 dark:text-slate-100 dark:placeholder:text-slate-500"
													value={c.expr}
													onChange={e =>
														setCalcs(prev =>
															prev.map(cc =>
																cc.id === c.id ? { ...cc, expr: e.target.value } : cc,
															),
														)
													}
													placeholder="Examples: 0x45 & 0b100001 + 9, (1<<23) | 5, 3.14 * (1<<8)"
												/>
												{res.ok ? (
													<>
														<div className="grid grid-cols-3 gap-2">
															<div className="rounded-lg border border-slate-200 bg-white p-2 dark:border-slate-800 dark:bg-slate-950/70">
																<div className="text-[11px] text-slate-500 dark:text-slate-400">
																	Decimal
																</div>
																<div className="mt-1 font-mono text-[11px] break-all text-slate-900 dark:text-slate-100">
																	{res.value.toString()}
																</div>
															</div>
															<div className="rounded-lg border border-slate-200 bg-white p-2 dark:border-slate-800 dark:bg-slate-950/70">
																<div className="text-[11px] text-slate-500 dark:text-slate-400">
																	Hex
																</div>
																<div className="mt-1 font-mono text-[11px] text-slate-900 dark:text-slate-100">
																	{'0x' + res.value.toString(16)}
																</div>
															</div>
															<div className="rounded-lg border border-slate-200 bg-white p-2 dark:border-slate-800 dark:bg-slate-950/70">
																<div className="text-[11px] text-slate-500 dark:text-slate-400">
																	Binary
																</div>
																<div className="mt-1 font-mono text-[10px] break-words text-slate-900 dark:text-slate-100">
																	{chunkString(
																		res.value.toString(2).padStart(width, '0'),
																		4,
																	).join('_')}
																</div>
															</div>
														</div>
														<div className="mt-1 grid grid-cols-2 gap-2 text-[11px] text-slate-700 dark:text-slate-300">
															<div className="rounded-lg border border-slate-200 bg-white px-2 py-1 dark:border-slate-800 dark:bg-slate-950/70">
																<div className="text-slate-500 dark:text-slate-400">
																	As f32
																</div>
																<div className="font-mono overflow-hidden text-ellipsis">
																	{floatView32}
																</div>
															</div>
															<div className="rounded-lg border border-slate-200 bg-white px-2 py-1 dark:border-slate-800 dark:bg-slate-950/70">
																<div className="text-slate-500 dark:text-slate-400">
																	As f64
																</div>
																<div className="font-mono overflow-hidden text-ellipsis">
																	{floatView64}
																</div>
															</div>
														</div>
													</>
												) : (
													<div className="text-xs text-red-600 dark:text-red-400">
														{res.error}
													</div>
												)}
												<div className="flex flex-wrap gap-2 mt-1">
													<button
														className="rounded-xl px-3 py-1.5 text-xs font-medium bg-brand-500 text-slate-950 hover:bg-brand-400 focus:outline-none focus:ring-2 focus:ring-brand-500/70 focus:ring-offset-2 focus:ring-offset-slate-50 dark:focus:ring-offset-slate-900"
														onClick={() => {
															if (res.ok)
																setInput(
																	'0x' +
																	(res.value & maskForWidth(width)).toString(16),
																);
														}}
													>
														Use as Value
													</button>
													<button
														className="rounded-xl px-3 py-1.5 text-xs font-medium bg-slate-100 text-slate-800 hover:bg-slate-200 focus:outline-none focus:ring-2 focus:ring-slate-300 dark:bg-slate-800/80 dark:text-slate-100 dark:hover:bg-slate-700/80 dark:focus:ring-slate-600/70 dark:focus:ring-offset-slate-900 focus:ring-offset-2"
														onClick={() => {
															if (res.ok) storeToMemory(res.value);
														}}
													>
														Store in Memory
													</button>
												</div>
											</div>
										);
									})}
								</div>

								{/* Memory panel */}
								<div className="mt-3 rounded-2xl border border-slate-200 bg-slate-50 p-3 dark:border-slate-800 dark:bg-slate-900/80">
									<div className="flex items-center gap-2">
										<div className="font-mono text-[11px] uppercase tracking-[0.16em] text-slate-500 dark:text-slate-400">
											Memory
										</div>
										<button
											className="ml-auto text-[11px] px-2 py-0.5 rounded-lg bg-slate-100 text-slate-700 hover:bg-slate-200 focus:outline-noneFocus:ring-1 focus:ring-slate-300 disabled:opacity-40 dark:bg-slate-800/80 dark:text-slate-200 dark:hover:bg-slate-700/80 dark:focus:ring-slate-600/70"
											onClick={clearMemory}
											disabled={memory.length === 0}
										>
											Clear
										</button>
									</div>
									{memory.length === 0 ? (
										<div className="mt-1 text-xs text-slate-500 dark:text-slate-400">
											Empty. Use <span className="font-mono">Store in Memory</span> on a
											calculator result.
										</div>
									) : (
										<div className="mt-2 space-y-1 text-xs">
											{memory.map(m => (
												<div
													key={m.id}
													className="flex flex-wrap items-center gap-2 rounded-lg border border-slate-200 bg-white px-2 py-1 dark:border-slate-800 dark:bg-slate-950/70"
												>
													<div className="font-mono text-[11px] px-1 py-0.5 rounded bg-slate-100 text-slate-800 border border-slate-300 dark:bg-slate-900 dark:text-slate-100 dark:border-slate-700">
														{m.label}
													</div>
													<div className="font-mono text-slate-800 dark:text-slate-200">
														<span className="text-slate-500 dark:text-slate-400">
															dec
														</span>{' '}
														{m.value.toString()}
													</div>
													<div className="font-mono text-slate-800 dark:text-slate-200">
														<span className="text-slate-500 dark:text-slate-400">
															hex
														</span>{' '}
														0x{m.value.toString(16)}
													</div>
													<div className="ml-auto flex gap-1">
														<button
															className="text-[11px] px-2 py-0.5 rounded bg-slate-100 text-slate-700 hover:bg-slate-200 focus:outline-none focus:ring-1 focus:ring-slate-300 dark:bg-slate-800/80 dark:text-slate-100 dark:hover:bg-slate-700/80 dark:focus:ring-slate-600/70"
															onClick={() => useMemoryAsValue(m)}
														>
															Use as Value
														</button>
														<button
															className="text-[11px] px-2 py-0.5 rounded bg-slate-100 text-slate-700 hover:bg-slate-200 focus:outline-none focus:ring-1 focus:ring-slate-300 dark:bg-slate-800/80 dark:text-slate-100 dark:hover:bg-slate-700/80 dark:focus:ring-slate-600/70"
															onClick={() => insertMemoryIntoFirstCalc(m)}
														>
															Insert into Calc 1
														</button>
													</div>
												</div>
											))}
										</div>
									)}
								</div>
							</div>

							{/* ASCII Converter */}
							<div className="rounded-3xl border border-slate-200/80 bg-white/90 p-4 shadow backdrop-blur-xs space-y-3 dark:border-slate-800/70 dark:bg-slate-900/70">
								<div className="font-mono text-xs uppercase tracking-[0.18em] text-slate-500 dark:text-slate-400">
									ASCII Converter
								</div>
								<div className="grid md:grid-cols-2 gap-3">
									<div>
										<label className="text-xs font-medium text-slate-700 dark:text-slate-300">
											Text → codes
										</label>
										<textarea
											className="mt-1 w-full h-20 rounded-xl border border-slate-300 bg-white px-3 py-2 text-sm font-mono text-slate-900 placeholder:text-slate-400 focus:outline-none focus:ring-2 focus:ring-brand-500/70 dark:border-slate-700 dark:bg-slate-950/70 dark:text-slate-100 dark:placeholder:text-slate-500"
											value={asciiText}
											onChange={e => setAsciiText(e.target.value)}
										/>
										<div className="mt-2 text-xs text-slate-700 dark:text-slate-300">
											<div className="text-slate-500 dark:text-slate-400">Hex bytes</div>
											<div className="mt-0.5 font-mono break-words text-slate-900 dark:text-slate-100">
												{asciiTextCodes.hex.join(' ') || '—'}
											</div>
											<div className="mt-2 text-slate-500 dark:text-slate-400">
												Decimal codes
											</div>
											<div className="mt-0.5 font-mono break-words text-slate-900 dark:text-slate-100">
												{asciiTextCodes.dec.join(' ') || '—'}
											</div>
										</div>
									</div>
									<div>
										<label className="text-xs font-medium text-slate-700 dark:text-slate-300">
											Codes → text
										</label>
										<textarea
											className="mt-1 w-full h-20 rounded-xl border border-slate-300 bg-white px-3 py-2 text-sm font-mono text-slate-900 placeholder:text-slate-400 focus:outline-none focus:ring-2 focus:ring-brand-500/70 dark:border-slate-700 dark:bg-slate-950/70 dark:text-slate-100 dark:placeholder:text-slate-500"
											value={asciiNums}
											onChange={e => setAsciiNums(e.target.value)}
											placeholder="0x41 0x42 67 0b1000001"
										/>
										<div className="mt-2 text-xs text-slate-600 dark:text-slate-400">
											Interprets tokens using the same parser (0x.., 0b.., decimal). Values are
											masked to 0xFF.
										</div>
										<div className="mt-1 text-sm text-slate-800 dark:text-slate-200">
											<span className="text-slate-500 dark:text-slate-400">Result:</span>{' '}
											<span className="font-mono text-slate-900 dark:text-slate-100">
												{asciiNumsResult || '—'}
											</span>
										</div>
									</div>
								</div>
							</div>

							{/* Floating-point Registers */}
							<div className="rounded-3xl border border-slate-200/80 bg-white/90 p-4 shadow backdrop-blur-xs space-y-3 dark:border-slate-800/70 dark:bg-slate-900/70">
								<div className="flex items-center gap-3">
									<div className="font-mono text-xs uppercase tracking-[0.18em] text-slate-500 dark:text-slate-400">
										Floating-point Registers
									</div>
									<select
										className="ml-auto rounded-lg border border-slate-300 bg-white px-2 py-1 text-xs text-slate-900 focus:outline-none focus:ring-2 focus:ring-brand-500/70 dark:border-slate-700 dark:bg-slate-950/80 dark:text-slate-100"
										value={floatMode}
										onChange={e => setFloatMode(e.target.value as 'f32' | 'f64')}
									>
										<option value="f32">32-bit (float)</option>
										<option value="f64">64-bit (double)</option>
									</select>
								</div>
								<div className="grid md:grid-cols-2 gap-3">
									{/* Value → Bits */}
									<div className="space-y-2">
										<div className="text-xs font-medium text-slate-700 dark:text-slate-300">
											Value → bits
										</div>
										<input
											className="w-full rounded-lg border border-slate-300 bg-white px-2 py-1 font-mono text-sm text-slate-900 placeholder:text-slate-400 focus:outline-none focus:ring-2 focus:ring-brand-500/70 dark:border-slate-700 dark:bg-slate-950/80 dark:text-slate-100 dark:placeholder:text-slate-500"
											value={floatValueInput}
											onChange={e => setFloatValueInput(e.target.value)}
											placeholder="e.g. 1.0, -0.5, 3.1415926"
										/>
										{floatFromValue.ok ? (
											<div className="text-xs space-y-1 text-slate-800 dark:text-slate-200">
												<div>
													<span className="text-slate-500 dark:text-slate-400">
														Bits (hex):{' '}
													</span>
													<span className="font-mono text-slate-900 dark:text-slate-100">
														0x
														{floatFromValue.bits
															.toString(16)
															.padStart(floatMode === 'f32' ? 8 : 16, '0')}
													</span>
												</div>
												<div>
													<span className="text-slate-500 dark:text-slate-400">
														Bits (bin):{' '}
													</span>
													<span className="font-mono break-words text-slate-900 dark:text-slate-100">
														{chunkString(
															toBin(
																floatFromValue.bits &
																maskForWidth(
																	floatMode === 'f32' ? 32 : 64,
																),
																floatMode === 'f32' ? 32 : 64,
															),
															4,
														).join('_')}
													</span>
												</div>
											</div>
										) : (
											<div className="text-xs text-red-600 dark:text-red-400">
												{floatFromValue.error}
											</div>
										)}
									</div>

									{/* Bits → Value */}
									<div className="space-y-2">
										<div className="text-xs font-medium text-slate-700 dark:text-slate-300">
											Bits → value
										</div>
										<input
											className="w-full rounded-lg border border-slate-300 bg-white px-2 py-1 font-mono text-sm text-slate-900 placeholder:text-slate-400 focus:outline-none focus:ring-2 focus:ring-brand-500/70 dark:border-slate-700 dark:bg-slate-950/80 dark:text-slate-100 dark:placeholder:text-slate-500"
											value={floatBitsInput}
											onChange={e => setFloatBitsInput(e.target.value)}
											placeholder={
												floatMode === 'f32'
													? 'e.g. 0x3f800000'
													: 'e.g. 0x3ff0000000000000'
											}
										/>
										{floatFromBits.ok ? (
											<div className="text-xs space-y-1 text-slate-800 dark:text-slate-200">
												<div>
													<span className="text-slate-500 dark:text-slate-400">
														Value:{' '}
													</span>
													<span className="font-mono text-slate-900 dark:text-slate-100">
														{formatFloat(floatFromBits.value)}
													</span>
												</div>
												<div>
													<span className="text-slate-500 dark:text-slate-400">
														Bits (hex):{' '}
													</span>
													<span className="font-mono text-slate-900 dark:text-slate-100">
														0x
														{floatFromBits.bits
															.toString(16)
															.padStart(floatMode === 'f32' ? 8 : 16, '0')}
													</span>
												</div>
											</div>
										) : (
											<div className="text-xs text-red-600 dark:text-red-400">
												{floatFromBits.error}
											</div>
										)}
									</div>
								</div>

								{/* Sign / exponent / mantissa breakdown */}
								<div className="rounded-2xl border border-slate-200 bg-slate-50 p-3 text-xs space-y-2 dark:border-slate-800 dark:bg-slate-950/80">
									<div className="font-mono text-[11px] uppercase tracking-[0.16em] text-slate-500 dark:text-slate-400">
										Bit layout
									</div>
									{floatLayout ? (
										<>
											<div className="font-mono break-words text-slate-900 dark:text-slate-100">
												<span className="text-slate-500 dark:text-slate-400">sign</span>{' '}
												<span className="px-1 rounded bg-slate-100 border border-slate-300 dark:bg-slate-900 dark:border-slate-700">
													{floatLayout.signBit}
												</span>{' '}
												<span className="ml-2 text-slate-500 dark:text-slate-400">
													exp
												</span>{' '}
												<span className="px-1 rounded bg-amber-50 border border-amber-200 dark:bg-amber-950/40 dark:border-amber-800/60">
													{chunkString(floatLayout.expStr, 4).join('_')}
												</span>{' '}
												<span className="ml-2 text-slate-500 dark:text-slate-400">
													mant
												</span>{' '}
												<span className="px-1 rounded bg-sky-50 border border-sky-200 dark:bg-sky-950/40 dark:border-sky-800/60">
													{chunkString(floatLayout.fracStr, 4).join('_')}
												</span>
											</div>
											<div className="space-y-1 text-slate-800 dark:text-slate-200">
												<div>
													Exponent raw:{' '}
													<span className="font-mono text-slate-900 dark:text-slate-100">
														{floatLayout.expRaw}
													</span>
												</div>
												<div>
													Exponent (unbiased):{' '}
													<span className="font-mono text-slate-900 dark:text-slate-100">
														{String(floatLayout.exponent)}
													</span>
												</div>
												<div>
													Kind:{' '}
													<span className="font-mono text-slate-900 dark:text-slate-100">
														{floatLayout.kind}
													</span>
												</div>
												{floatLayout.kind === 'normal' ||
													floatLayout.kind === 'subnormal' ? (
													<div>
														Mantissa (conceptual):{' '}
														<span className="font-mono text-slate-900 dark:text-slate-100">
															{floatLayout.mantissaDescr}
														</span>
													</div>
												) : (
													<div>
														Mantissa:{' '}
														<span className="font-mono text-slate-900 dark:text-slate-100">
															{floatLayout.mantissaDescr}
														</span>
													</div>
												)}
											</div>
										</>
									) : (
										<div className="text-slate-600 dark:text-slate-400">
											Enter a value or bits to see sign / exponent / mantissa layout.
										</div>
									)}
								</div>
							</div>
						</section>

						{/* Right column: bit labels, bitfields, masks, endian, codegen, tests, help */}
						<section className="md:col-span-2 space-y-4">
							{/* Bit Labels */}
							<div className="rounded-3xl border border-slate-200/80 bg-white/90 p-4 shadow backdrop-blur-xs dark:border-slate-800/70 dark:bg-slate-900/70">
								<div className="flex items-center gap-2">
									<div className="font-mono text-xs uppercase tracking-[0.18em] text-slate-500 dark:text-slate-400">
										Bit Labels
									</div>
								</div>
								<textarea
									className="mt-2 w-full h-18 rounded-xl border border-slate-300 bg-white px-3 py-2 font-mono text-sm text-slate-900 placeholder:text-slate-400 focus:outline-none focus:ring-2 focus:ring-brand-500/70 dark:border-slate-700 dark:bg-slate-950/80 dark:text-slate-100 dark:placeholder:text-slate-500"
									value={labelSpec}
									onChange={e => setLabelSpec(e.target.value)}
									placeholder="7:READY,5-3:MODE,0:EN"
								/>
								<div className="mt-3 grid grid-cols-4 sm:grid-cols-8 md:grid-cols-8 lg:grid-cols-8 gap-2">
									{Array.from({ length: width }).map((_, i) => {
										const bit = width - 1 - i;
										const isSet = ((uval >> BigInt(bit)) & 1n) === 1n;
										const label = labels.find(
											r => bit <= r.start && bit >= r.end,
										);
										return (
											<button
												key={bit}
												onClick={() => setBit(bit, !isSet)}
												className={`group rounded-xl border px-1.5 py-1.5 text-left text-xs shadow-soft transition ${isSet
														? 'bg-emerald-50 border-emerald-200 text-emerald-900 dark:bg-emerald-950/40 dark:border-emerald-800/70 dark:text-emerald-100'
														: 'bg-slate-50 border-slate-200 text-slate-800 dark:bg-slate-950/60 dark:border-slate-800/80 dark:text-slate-200'
													}`}
											>
												<div className="text-[10px] text-slate-500 group-hover:text-slate-700 dark:text-slate-500 dark:group-hover:text-slate-300">
													bit {bit}
												</div>
												<div
													className="font-semibold truncate"
													title={label?.name ?? ''}
												>
													{label?.name ?? (isSet ? '1' : '0')}
												</div>
											</button>
										);
									})}
								</div>
							</div>

							{/* Bitfield Editor */}
							<div className="rounded-3xl border border-slate-200/80 bg-white/90 p-4 shadow backdrop-blur-xs space-y-3 dark:border-slate-800/70 dark:bg-slate-900/70">
								<div className="font-mono text-xs uppercase tracking-[0.18em] text-slate-500 dark:text-slate-400">
									Bitfields
								</div>
								<div>
									<div className="grid sm:grid-cols-2 gap-2">
										<div>
											<label className="text-xs font-medium text-slate-700 dark:text-slate-300">
												Field hi (bit)
											</label>
											<input
												type="number"
												className="mt-1 w-full rounded-lg border border-slate-300 bg-white px-2 py-1 text-sm text-slate-900 placeholder:text-slate-400 focus:outline-none focus:ring-2 focus:ring-brand-500/70 dark:border-slate-700 dark:bg-slate-950/80 dark:text-slate-100 dark:placeholder:text-slate-500"
												value={fieldHi}
												onChange={e =>
													setFieldHi(
														Math.min(
															Math.max(parseInt(e.target.value || '0', 10), 0),
															width - 1,
														),
													)
												}
											/>
										</div>
										<div>
											<label className="text-xs font-medium text-slate-700 dark:text-slate-300">
												Field lo (bit)
											</label>
											<input
												type="number"
												className="mt-1 w-full rounded-lg border border-slate-300 bg-white px-2 py-1 text-sm text-slate-900 placeholder:text-slate-400 focus:outline-none focus:ring-2 focus:ring-brand-500/70 dark:border-slate-700 dark:bg-slate-950/80 dark:text-slate-100 dark:placeholder:text-slate-500"
												value={fieldLo}
												onChange={e =>
													setFieldLo(
														Math.min(
															Math.max(parseInt(e.target.value || '0', 10), 0),
															width - 1,
														),
													)
												}
											/>
										</div>
									</div>

									<div className="flex items-start gap-3 mt-1">
										<div className="text-[11px] font-medium text-slate-500 dark:text-slate-400">
											len ={' '}
											<span className="font-mono text-slate-900 dark:text-slate-100">
												{fieldLen}
											</span>
										</div>
										<div className="text-[11px] font-medium text-slate-500 dark:text-slate-400">
											current ={' '}
											<span className="font-mono text-slate-900 dark:text-slate-100">
												{parsed.ok ? '0x' + fieldValue.toString(16) : '—'}
											</span>{' '}
											(
											<span className="font-mono text-slate-900 dark:text-slate-100">
												{fieldValue.toString()}
											</span>
											)
										</div>
									</div>
								</div>
								<div className="flex items-end gap-2 flex-wrap">
									<input
										className="w-48 rounded-lg border border-slate-300 bg-white px-2 py-1 font-mono text-sm text-slate-900 placeholder:text-slate-400 focus:outline-none focus:ring-2 focus:ring-brand-500/70 dark:border-slate-700 dark:bg-slate-950/80 dark:text-slate-100 dark:placeholder:text-slate-500"
										value={fieldValInput}
										onChange={e => setFieldValInput(e.target.value)}
										placeholder="value (hex/dec/bin)"
									/>
									<button
										className="rounded-xl px-3 py-1.5 text-xs font-medium bg-brand-500 text-slate-950 hover:bg-brand-400 focus:outline-none focus:ring-2 focus:ring-brand-500/70 focus:ring-offset-2 focus:ring-offset-slate-50 dark:focus:ring-offset-slate-900"
										onClick={() => {
											const p = parseNumber(fieldValInput);
											if (!p.ok) return;
											const len = fieldLen;
											const max = (1n << BigInt(len)) - 1n;
											insertField(fieldHi, len, p.value & max);
										}}
									>
										Set field
									</button>
								</div>
							</div>

							{/* Masks */}
							<div className="rounded-3xl border border-slate-200/80 bg-white/90 p-4 shadow backdrop-blur-xs space-y-2 dark:border-slate-800/70 dark:bg-slate-900/70">
								<div className="font-mono text-xs uppercase tracking-[0.18em] text-slate-500 dark:text-slate-400">
									Masks
								</div>
								<div className="grid sm:grid-cols-2 gap-2">
									<div>
										<label className="text-xs font-medium text-slate-700 dark:text-slate-300">
											Set mask
										</label>
										<input
											className="mt-1 w-full rounded-lg border border-slate-300 bg-white px-2 py-1 font-mono text-sm text-slate-900 placeholder:text-slate-400 focus:outline-none focus:ring-2 focus:ring-brand-500/70 dark:border-slate-700 dark:bg-slate-950/80 dark:text-slate-100 dark:placeholder:text-slate-500"
											value={setMaskStr}
											onChange={e => setSetMask(e.target.value)}
											placeholder="e.g. 0xF0"
										/>
									</div>
									<div>
										<label className="text-xs font-medium text-slate-700 dark:text-slate-300">
											Clear mask
										</label>
										<input
											className="mt-1 w-full rounded-lg border border-slate-300 bg-white px-2 py-1 font-mono text-sm text-slate-900 placeholder:text-slate-400 focus:outline-none focus:ring-2 focus:ring-brand-500/70 dark:border-slate-700 dark:bg-slate-950/80 dark:text-slate-100 dark:placeholder:text-slate-500"
											value={clrMaskStr}
											onChange={e => setClrMask(e.target.value)}
											placeholder="e.g. 0b1111"
										/>
									</div>
								</div>
								<div className="flex gap-2 mt-1 flex-wrap">
									<button
										className="rounded-xl px-3 py-1.5 text-xs font-medium bg-slate-100 text-slate-800 hover:bg-slate-200 focus:outline-none focus:ring-2 focus:ring-slate-300 focus:ring-offset-2 focus:ring-offset-slate-50 dark:bg-slate-800/80 dark:text-slate-100 dark:hover:bg-slate-700/80 dark:focus:ring-slate-600/70 dark:focus:ring-offset-slate-900"
										onClick={() => applyMasks(setMaskStr, '0')}
									>
										Apply Set
									</button>
									<button
										className="rounded-xl px-3 py-1.5 text-xs font-medium bg-slate-100 text-slate-800 hover:bg-slate-200 focus:outline-none focus:ring-2 focus:ring-slate-300 focus:ring-offset-2 focus:ring-offset-slate-50 dark:bg-slate-800/80 dark:text-slate-100 dark:hover:bg-slate-700/80 dark:focus:ring-slate-600/70 dark:focus:ring-offset-slate-900"
										onClick={() => applyMasks('0', clrMaskStr)}
									>
										Apply Clear
									</button>
									<button
										className="rounded-xl px-3 py-1.5 text-xs font-medium bg-brand-500 text-slate-950 hover:bg-brand-400 focus:outline-none focus:ring-2 focus:ring-brand-500/70 focus:ring-offset-2 focus:ring-offset-slate-50 dark:focus:ring-offset-slate-900"
										onClick={() => applyMasks(setMaskStr, clrMaskStr)}
									>
										Apply Both
									</button>
								</div>
							</div>

							{/* Endianness */}
							<div className="rounded-3xl border border-slate-200/80 bg-white/90 p-4 shadow backdrop-blur-xs dark:border-slate-800/70 dark:bg-slate-900/70">
								<div className="font-mono text-xs uppercase tracking-[0.18em] text-slate-500 dark:text-slate-400 mb-1">
									Endian View
								</div>
								<div className="grid grid-cols-2 gap-4 text-sm">
									<div>
										<div className="text-slate-600 dark:text-slate-400">
											Little-endian bytes
										</div>
										<div className="text-slate-600 dark:text-slate-400 text-xs">
											(LSB→MSB)
										</div>
										<div className="mt-2 flex flex-wrap gap-1 font-mono text-xs">
											{leBytes.map((b, i) => (
												<span
													key={i}
													className="rounded-lg px-2 py-1 bg-slate-50 border border-slate-200 text-slate-900 dark:bg-slate-950/80 dark:border-slate-800 dark:text-slate-100"
												>
													{b}
												</span>
											))}
										</div>
									</div>
									<div>
										<div className="text-slate-600 dark:text-slate-400">
											Big-endian bytes
										</div>
										<div className="text-slate-600 dark:text-slate-400 text-xs">
											(MSB→LSB)
										</div>
										<div className="mt-2 flex flex-wrap gap-1 font-mono text-xs">
											{beBytes.map((b, i) => (
												<span
													key={i}
													className="rounded-lg px-2 py-1 bg-slate-50 border border-slate-200 text-slate-900 dark:bg-slate-950/80 dark:border-slate-800 dark:text-slate-100"
												>
													{b}
												</span>
											))}
										</div>
									</div>
								</div>
							</div>

							{/* Codegen */}
							<div className="rounded-3xl border border-slate-200/80 bg-white/90 p-4 shadow backdrop-blur-xs dark:border-slate-800/70 dark:bg-slate-900/70">
								<div className="flex items-center justify-between gap-2">
									<div className="font-mono text-xs uppercase tracking-[0.18em] text-slate-500 dark:text-slate-400">
										C Macros / Snippets
									</div>
									<button
										className="rounded-lg px-2 py-1 text-xs font-medium bg-slate-100 text-slate-700 hover:bg-slate-200 focus:outline-none focus:ring-1 focus:ring-slate-300 dark:bg-slate-800/80 dark:text-slate-100 dark:hover:bg-slate-700/80 dark:focus:ring-slate-600/70"
										onClick={() => navigator.clipboard.writeText(codeGen)}
									>
										Copy
									</button>
								</div>
								<pre className="mt-2 p-3 rounded-2xl bg-slate-50 border border-slate-200 overflow-auto text-xs text-slate-900 dark:bg-slate-950/80 dark:border-slate-800 dark:text-slate-100">
									<code>{codeGen}</code>
								</pre>
							</div>

							{/* Calculator Self-tests */}
							<div className="rounded-3xl border border-slate-200/80 bg-white/90 p-4 shadow backdrop-blur-xs dark:border-slate-800/70 dark:bg-slate-900/70">
								<div className="font-mono text-xs uppercase tracking-[0.18em] text-slate-500 dark:text-slate-400">
									Calculator Self-tests
								</div>
								<p className="text-[11px] text-slate-600 mt-1 dark:text-slate-400">
									Precedence (custom): multiplicative &gt; bitwise AND &gt; additive &gt; shifts
									&gt; XOR &gt; OR.
								</p>
								<div className="mt-2 space-y-1 text-sm">
									{testResults.map((t, i) => (
										<div
											key={i}
											className={`flex items-center justify-between rounded-lg border px-2 py-1 text-[11px] ${t.ok
													? 'border-emerald-300/70 bg-emerald-50 text-emerald-900 dark:border-emerald-700/70 dark:bg-emerald-950/40 dark:text-emerald-100'
													: 'border-red-300/70 bg-red-50 text-red-900 dark:border-red-700/70 dark:bg-red-950/40 dark:text-red-100'
												}`}
										>
											<div className="font-mono mr-2 truncate">{t.expr}</div>
											<div className="font-mono">
												expected {t.expectDec}, got {t.got} {t.ok ? '✓' : '✗'}
											</div>
										</div>
									))}
								</div>
							</div>

							{/* Help */}
							<div className="rounded-3xl border border-slate-200/80 bg-white/90 p-4 shadow backdrop-blur-xs text-sm text-slate-800 space-y-2 dark:border-slate-800/70 dark:bg-slate-900/70 dark:text-slate-200">
								<div className="font-mono text-xs uppercase tracking-[0.18em] text-slate-500 dark:text-slate-400">
									Tips
								</div>
								<ul className="list-disc pl-5 space-y-1 text-xs text-slate-700 dark:text-slate-300">
									<li>
										Inputs accept <span className="font-mono">0x..</span>,{' '}
										<span className="font-mono">0b..</span>,{' '}
										<span className="font-mono">...h</span>,{' '}
										<span className="font-mono">...b</span> and underscores.
									</li>
									<li>
										Use multiple calculators for different expressions; results can be stored in
										memory and reused.
									</li>
									<li>
										Calculator results are also decoded as{' '}
										<span className="font-mono">f32</span> and{' '}
										<span className="font-mono">f64</span> using their bit patterns.
									</li>
									<li>
										Memory values can feed back into the main value or be inserted into Calculator
										1.
									</li>
									<li>
										ASCII converter is useful for debugging registers that hold characters (e.g.,
										UART data or ID strings).
									</li>
									<li>
										Toggle bits directly; use <em>Masks</em> to set/clear many bits at once.
									</li>
									<li>
										Define labels like <span className="font-mono">23:ERR, 22-16:MODE</span> to
										annotate fields. Code macros update automatically.
									</li>
									<li>Endian view shows how the value maps to bytes for the selected width.</li>
									<li>
										The floating-point section lets you move between values and IEEE-754 bit
										layouts, and breaks out sign / exponent / mantissa.
									</li>
								</ul>
							</div>
						</section>
					</div>
				</div>
			</div>
		</div>
	);
}