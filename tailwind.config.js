/** @type {import('tailwindcss').Config} */
export default {
	content: [
		"./index.html",
		"./src/**/*.{js,ts,jsx,tsx}",
	],
	darkMode: 'class',
	theme: {
		extend: {
			fontFamily: {
				sans: ['system-ui', 'SF Pro Text', 'ui-sans-serif', 'sans-serif'],
				mono: ['JetBrains Mono', 'SF Mono', 'ui-monospace', 'Menlo', 'monospace'],
			},
			colors: {
				bg: {
					DEFAULT: '#020617', // slate-950-ish
					soft: '#020617',    // alias for convenience
				},
				panel: {
					DEFAULT: '#020617',
					soft: '#020617',
				},
				brand: {
					50: '#ecfeff',
					100: '#cffafe',
					200: '#a5f3fc',
					300: '#67e8f9',
					400: '#22d3ee',
					500: '#a1ddf0',
					600: '#0891b2',
					700: '#0e7490',
					800: '#155e75',
					900: '#164e63',
				},
			},
			borderRadius: {
				'2xl': '1.25rem',
				'3xl': '1.75rem',
			},
			boxShadow: {
				'panel': '0 18px 45px rgba(15,23,42,0.75)',
				'panel-soft': '0 12px 30px rgba(15,23,42,0.55)',
			},
			backdropBlur: {
				'xs': '2px',
			},
		},
	},
	plugins: [],
}

