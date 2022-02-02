import { defineWindiSetup } from '@slidev/types'

// extending the builtin windicss configurations

const sizeBase = 2

export default defineWindiSetup(() => ({
	shortcuts: {
		// 'bg-main': 'bg-white text-[#181818] dark:bg-[#121212] dark:text-[#ddd]',
	},
	theme: {
		// fontSize: {
		// 	'xs': `${sizeBase * 0.75}rem`,
		// 	'sm': `${sizeBase * 0.875}rem`,
		// 	'tiny': `${sizeBase * 0.875}rem`,
		// 	'base': `${sizeBase * 1}rem`,
		// 	'lg': `${sizeBase * 1.125}rem`,
		// 	'xl': `${sizeBase * 1.25}rem`,
		// 	'2xl': `${sizeBase * 1.5}rem`,
		// 	'3xl': `${sizeBase * 1.875}rem`,
		// 	'4xl': `${sizeBase * 2.25}rem`,
		// 	'5xl': `${sizeBase * 3}rem`,
		// 	'6xl': `${sizeBase * 4}rem`,
		// 	'7xl': `${sizeBase * 5}rem`,
		// },

		extend: {
			// // fonts can be replaced here, remember to update the web font links in `index.html`
			// fontFamily: {
			// 	sans: 'ui-sans-serif,system-ui,-apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,"Helvetica Neue",Arial,"Noto Sans",sans-serif,"Apple Color Emoji","Segoe UI Emoji","Segoe UI Symbol","Noto Color Emoji"',
			// 	mono: '"Fira Code", monospace',
			// },
		},
	},
}))
