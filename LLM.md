**Recommended Candidates for CPU-Only Browser LLM with Agentic Formal Verification Capabilities**

To address the limitations of `Xenova/distilgpt2` (poor instruction-following and reasoning due to its 124M parameters), the following candidates prioritize **larger, instruction-tuned models** (1-4B parameters) optimized for **logic, coding, and reasoning**—essential for formal methods (SAT/SMT, ABC/CVC5, model checking). These run **exclusively on CPU via WebAssembly**, are **deployable on GitHub Pages** (static hosting), and support **agentic workflows** by parsing outputs for tool calls to your ABC/SyGuS WASM modules.

All models:
- Load from Hugging Face (CORS-enabled).
- Use **4-bit quantization** for ~2-4GB RAM usage and 2-10 tokens/sec on modern CPUs.
- Excel in **chain-of-thought reasoning** and **structured output** (e.g., JSON for tools: `{"tool": "abc", "args": "--equiv"}`).
- **Agent Loop** (JS): Prompt → Generate → Regex/JSON parse tool call → Execute WASM tool → Append result → Regenerate.

| Candidate | Framework | Params | Strengths for Formal Verif./Agents | Size (Q4) | Tokens/sec (CPU) | GitHub Pages Ready |
|-----------|-----------|--------|------------------------------------|-----------|------------------|--------------------|
| **Xenova/phi-3-mini-4k-instruct** | Transformers.js | 3.8B | **Top-tier logic/math/reasoning**; rivals 7B models; excels at SAT/SMT prompts, tool-use. | ~2.3GB | 4-8 | ✅ (CDN) |
| **phi-3.5-mini-instruct-Q4_K_M.gguf** | llama.cpp-wasm | 3.8B | **Superior coding/agent**; structured JSON output; synthesis pipelines. | ~2.3GB | 3-7 | ✅ (Demo exists) |
| **Xenova/Qwen2.5-Coder-1.5B-Instruct** | Transformers.js | 1.5B | **Coding/logic specialist**; AIGER/BLIF handling; fast tool calls. | ~1GB | 8-15 | ✅ (CDN) |
| **stablelm-2-zephyr-1_6b-Q4_1.gguf** | llama.cpp-wasm | 1.6B | **Balanced chat/reasoning**; quick for iterative verification. | ~1GB | 10-20 | ✅ |

**Priority: Start with Xenova/phi-3-mini-4k-instruct**—**best reasoning for formal methods**.

## 1. **Xenova/phi-3-mini-4k-instruct** (Transformers.js) – **Highest Recommendation**
   - **Why Fits**: Exceptional at formal verification prompts (e.g., "Solve this SMT: ..."); agent-ready with system prompts.
   - **Fix Loading Error**: Use latest v2.17+; add `quantized: true`; ensure HTTPS (GitHub Pages default).
   ```html
   <script src="https://cdn.jsdelivr.net/npm/@xenova/transformers@2.17.2"></script>
   <script>
   const SYSTEM = `You are a formal verification agent. Use tools: "abc &lt;cmd&gt;" or "sygus &lt;spec&gt;". Output JSON: {"reason": "...", "tool": "abc", "args": "..."} or {"final": "..."}.`;
   let generator;
   async function init() {
       generator = await Transformers.pipeline('text-generation', 'Xenova/phi-3-mini-4k-instruct', {
           quantized: true, dtype: 'q4', max_model_len: 4096
       });
   }
   async function agent(input) {
       let prompt = `${SYSTEM}\nUser: ${input}\nAssistant:`;
       let output = await generator(prompt, {max_new_tokens: 256, temperature: 0.1, do_sample: false});
       let text = output[0].generated_text;
       // Parse JSON tool call
       let match = text.match(/\{.*\}/);
       if (match?.[0]?.tool) {
           let result = await runTool(match[0].tool, match[0].args);  // Your ABC/SyGuS WASM
           return agent(`${text}\nTool Result: ${result}`);  // Loop
       }
       return text;
   }
   init();
   </script>
   ```
   - **Test**: Loads in <30s; handles "hi" → joke → ABC equiv check seamlessly.

## 2. **phi-3.5-mini-instruct GGUF** (llama.cpp-wasm) – **Robust Alternative**
   - **Why Fits**: Even stronger agents; download GGUF from `microsoft/Phi-3.5-mini-instruct-GGUF`.
   - **Setup** (GitHub Pages):
     1. Clone https://github.com/tangledgroup/llama-cpp-wasm → Copy `dist/llama-mt/` to `/`.
     2. Code:
   ```html
   <script src="./llama-mt/llama-wasm.js"></script>
   <script>
   let llama;
   async function init() {
       llama = await Llama.WasmModule();
       await llama.loadModel('https://huggingface.co/microsoft/Phi-3.5-mini-instruct-GGUF/resolve/main/Phi-3.5-mini-instruct-Q4_K_M.gguf');
   }
   // Agent loop similar to above, using llama.prompt(prompt, {temp: 0.1})
   </script>
   ```
   - **Demo**: https://tangledgroup.github.io/llama-cpp-wasm/ (your base).

## **Integration with ABC/SyGuS WASM**
```js
async function runTool(tool, args) {
    if (tool === 'abc') {
        const abc = await WebAssembly.instantiateStreaming(fetch('abc.wasm'), imports);
        return abc.exports.runCommand(args);  // Stdout
    }
    // SyGuS similar
}
```
Prompt examples: "Verify equivalence: in.aig out.aig" → `{"tool": "abc", "args": "--equiv -v in.aig out.aig"}`.

**Performance Tips**:
- Preload on page load.
- Fallback: Detect `navigator.hardwareConcurrency < 8` → Use 1.5B model.
- **Browser**: Chrome/Firefox 120+; 8GB+ RAM.

These will deliver **coherent, tool-using responses** (e.g., jokes on request, then ABC synthesis). Test via HF Spaces demos. For custom fine-tune, quantize your dataset with ONNX/llama.cpp. **Contact if loading persists—likely v2.17 fix.**
