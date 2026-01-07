import { defineConfig } from 'vite'
import react from '@vitejs/plugin-react'
import fs from 'node:fs'
import path from 'node:path'

function copyDirSync(srcDir, destDir) {
  if (!fs.existsSync(srcDir)) return;
  fs.mkdirSync(destDir, { recursive: true });
  for (const entry of fs.readdirSync(srcDir, { withFileTypes: true })) {
    const srcPath = path.join(srcDir, entry.name);
    const destPath = path.join(destDir, entry.name);
    if (entry.isDirectory()) {
      copyDirSync(srcPath, destPath);
    } else if (entry.isFile()) {
      fs.copyFileSync(srcPath, destPath);
    }
  }
}

// https://vitejs.dev/config/
export default defineConfig({
  plugins: [
    react(),
    {
      name: 'copy-chisel-generated',
      apply: 'build',
      closeBundle() {
        const root = process.cwd();
        const srcGenerated = path.join(root, 'chisel', 'generated');
        const outGenerated = path.join(root, 'dist', 'generated');
        copyDirSync(srcGenerated, outGenerated);
      }
    }
  ],
  base: './', // For relative paths in deployment
  server: {
    proxy: {
      '/api': {
        target: 'http://localhost:3001',
        changeOrigin: true,
        secure: false,
      }
    }
  },
  // `vite preview` should emulate static hosting (GitHub Pages): no backend proxy.
  preview: {
    proxy: {}
  },
  build: {
    outDir: 'dist',
    assetsDir: 'assets',
  }
})
