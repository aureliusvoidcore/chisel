
import { chromium } from 'playwright';
import { spawn } from 'child_process';
import net from 'node:net';
import http from 'node:http';

async function getFreePort() {
  return await new Promise((resolve, reject) => {
    const server = net.createServer();
    server.unref();
    server.on('error', reject);
    server.listen(0, '127.0.0.1', () => {
      const address = server.address();
      if (!address || typeof address === 'string') {
        server.close(() => reject(new Error('Failed to acquire free TCP port')));
        return;
      }
      const { port } = address;
      server.close(() => resolve(port));
    });
  });
}

async function waitForHttpOk(url, timeoutMs = 15_000) {
  const start = Date.now();
  // eslint-disable-next-line no-constant-condition
  while (true) {
    try {
      const status = await new Promise((resolve, reject) => {
        const req = http.get(url, (res) => {
          res.resume();
          resolve(res.statusCode ?? 0);
        });
        req.on('error', reject);
      });
      if (status >= 200 && status < 500) return;
    } catch {
      // keep polling
    }

    if (Date.now() - start > timeoutMs) {
      throw new Error(`Timed out waiting for server at ${url}`);
    }
    await new Promise((resolve) => setTimeout(resolve, 250));
  }
}

async function test() {
  console.log('Starting server...');
  const port = await getFreePort();
  const server = spawn(
    'npx',
    ['vite', 'preview', '--host', '127.0.0.1', '--port', String(port), '--strictPort'],
    { stdio: ['ignore', 'pipe', 'pipe'] },
  );
  server.stdout?.on('data', (d) => process.stdout.write(d));
  server.stderr?.on('data', (d) => process.stderr.write(d));

  const baseUrl = `http://127.0.0.1:${port}/`;
  await waitForHttpOk(baseUrl);

  console.log('Launching browser...');
  const browser = await chromium.launch();
  const page = await browser.newPage();

  page.on('console', msg => console.log('PAGE LOG:', msg.text()));
  const pageErrors = [];
  page.on('pageerror', err => {
    pageErrors.push(String(err));
    console.log('PAGE ERROR:', err);
  });

  const notFoundUrls = [];
  page.on('response', (res) => {
    if (res.status() === 404) {
      notFoundUrls.push(res.url());
    }
  });

  try {
    console.log('Navigating to page...');
    await page.goto(baseUrl);
    
    // Wait for potential errors
    await page.waitForTimeout(2000);
    
    const errorOverlay = await page.$('#global-error-overlay');
    if (errorOverlay && await errorOverlay.isVisible()) {
        const text = await errorOverlay.innerText();
        if (text) {
            console.error('Global Error Overlay detected:', text);
            process.exit(1);
        }
    }

    console.log('Checking for root element...');
    const root = await page.$('#root');
    if (root) {
        console.log('Root element found.');
    } else {
        console.error('Root element NOT found.');
        process.exit(1);
    }

    // Ensure the UI can perform static "Elaborate" (loads dist/generated/<module>/<module>.sv)
    console.log('Clicking Elaborate...');
    await page.getByRole('button', { name: 'Elaborate' }).click();

    // Wait for the compiler success log line in the UI.
    await page.waitForFunction(
      () => document.body && document.body.innerText.includes('[Compiler] ✓ SystemVerilog generated'),
      { timeout: 25_000 }
    );

    // Monaco renders editor text into .view-lines; assert a module declaration exists.
    const monacoTexts = await page.evaluate(() => {
      const editors = Array.from(document.querySelectorAll('.monaco-editor'));
      return editors
        .map((ed) => ed.querySelector('.view-lines')?.innerText || '')
        .filter((t) => t && t.trim().length > 0);
    });
    const svCandidate = monacoTexts.find((t) => /\bmodule\b\s+\w+/m.test(t));
    if (!svCandidate) {
      console.error('No Monaco editor contained a SystemVerilog module declaration after Elaborate.');
      process.exit(1);
    }

    if (pageErrors.length) {
      console.error('Page errors detected:', pageErrors);
      process.exit(1);
    }
    if (notFoundUrls.length) {
      console.error('404s detected:', notFoundUrls);
      process.exit(1);
    }

  } catch (e) {
    console.error('Test failed:', e);
    process.exit(1);
  } finally {
    await browser.close();
    server.kill();
  }
}

test();
