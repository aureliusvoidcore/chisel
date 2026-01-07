---
layout: default
title: Formal Verification
---

## Formal Verification

This page is the hub for the site’s formal verification tooling and curated guides.

### Tools

- CVC5 Web (WASM): <a class="button" href="{{ site.baseurl }}/pages/formal-verification/cvc5">Open Advanced Interface</a>
- ABC Web (WASM): <a class="button" href="{{ site.baseurl }}/pages/formal-verification/abc">Open Formal Harness (PDR/BMC/CEC)</a>
- HW-CBMC Web (WASM): <a class="button" href="{{ site.baseurl }}/pages/formal-verification/hwcbmc">Open BMC for Verilog</a>

### Blog

- <a class="button" href="{{ site.baseurl }}/pages/formal-verification/how-to-verify">How to (formally) verify</a>
- <a class="button" href="{{ site.baseurl }}/pages/formal-verification/chisel-assertions">Chisel assertions for formal verification</a>

### Local LLM (Browser, CPU-only)

- In-browser assistant: [Local LLM (CPU/WASM)](/pages/formal-verification-llm.html)
- Runs entirely on the visitor’s machine. First use downloads model weights from Hugging Face and caches them in the browser.
- Start with a small model (e.g., LaMini-Flan-T5 248M). Large 7B–20B models are not practical on CPU in-browser due to memory/download constraints.
