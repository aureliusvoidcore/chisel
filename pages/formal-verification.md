---
layout: default
title: Formal Verification
---

## Formal Verification

This section collects property specifications, model checking workflows, and SAT/SMT encodings.

### Tools

- CVC5 Web (WASM): <a class="button" href="{{ site.baseurl }}/pages/formal-verification/cvc5">Open Advanced Interface</a>
 - ABC Web (WASM): <a class="button" href="{{ site.baseurl }}/pages/formal-verification/abc">Open Formal Harness (PDR/BMC/CEC)</a>
 - HW-CBMC Web (WASM): <a class="button" href="{{ site.baseurl }}/pages/formal-verification/hwcbmc">Open BMC for Verilog</a>

### Local LLM (Browser, CPU-only)

- Try our in-browser assistant: [Local LLM (CPU/WASM)](/pages/formal-verification-llm.html)
- Runs entirely on the visitor’s machine. First use downloads model weights from Hugging Face and caches them in the browser.
- Start with a small model (e.g., LaMini-Flan-T5 248M). Large 7B–20B models are not practical on CPU in-browser due to memory/download constraints.

### Property example (SVA)

```systemverilog
// Assume-Guarantee sketch
property safe_handshake;
  @(posedge clk) disable iff (!rst_n)
    req |=> ##[1:3] gnt;
endproperty
assert property (safe_handshake);
```

### SMT snippet (Z3)

```smt2
(set-logic QF_BV)
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(assert (= (bvadd a b) #x2a))
(check-sat)
(get-model)
```

### Reference

- <a class="button" href="{{ site.baseurl }}/pages/formal-verification/how-to-verify">How to (formally) verify</a>
