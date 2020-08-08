// rollup.config.js
import babel from '@rollup/plugin-babel';
import resolve from '@rollup/plugin-node-resolve';
import commonjs from '@rollup/plugin-commonjs';
import postcss from 'rollup-plugin-postcss';
import peerDepsExternal from 'rollup-plugin-peer-deps-external';
import typescript from 'rollup-plugin-typescript2';
import svg from 'rollup-plugin-svg'

export default {
  input: './src/index.ts',

  output: [
    {
      name: 'comlib',
      sourcemap: true,
      file: './lib/index.js',
      format: 'umd',
      globals: { react: 'React' },
    },
  ],

  plugins: [
    typescript(/*{ plugin options }*/),
    peerDepsExternal(),
    svg(),
    postcss({
      extract: false,
      modules: true
    }),
    babel({ exclude: 'node_modules/**' }),
    resolve(),
    commonjs(),
  ],
  external: ['react', 'react-dom'],
};


