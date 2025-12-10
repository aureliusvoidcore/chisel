### Architecture Overview

The 2026 Formal Verification Tool for Chisel Designs, provisionally named "ChiselForge," is designed as a fully client-side web application that empowers hardware engineers to define, analyze, and formally verify Chisel-based digital designs directly in the browser. Drawing inspiration from the elegance and intuitiveness of Apple's ecosystem—where form and function converge seamlessly—this tool prioritizes a clean, minimalist interface that eliminates unnecessary complexity while delivering powerful, productive workflows. It integrates WebAssembly (Wasm) ports of essential components to ensure low-latency, secure execution without server dependencies, aligning with a philosophy of "usefulness above all" by enabling instant feedback loops for iterative design and verification.

At its core, ChiselForge leverages the provided GitHub repository (https://github.com/aureliusvoidcore/chisel) as a foundational blueprint, adapting its Chisel modules, build system, and EBMC integration into a browser-native environment. The architecture is modular, extensible, and optimized for performance, incorporating Scala.js for Chisel compilation, a Wasm-compiled CIRCT/firtool for intermediate representations, and the given Wasm EBMC binary for bounded model checking. Additional plugins, built on CIRCT's MLIR (Multi-Level Intermediate Representation) and LIR (Low-Level IR) capabilities, provide advanced analysis features such as dataflow graphing and proof optimization suggestions.

The system operates entirely in the browser using modern web technologies: React for the UI framework (with hooks for state management), Monaco Editor for code editing (extended with Chisel-specific syntax highlighting and autocompletion), and Cytoscape.js for visualizations. Web Workers handle compute-intensive tasks like compilation and verification to maintain UI responsiveness. Data persistence uses IndexedDB for project storage, allowing offline use and seamless resumption.

Key architectural components include:

1. **Frontend Layer (User Interface and Interaction):**
   - Built with React and Tailwind CSS for a responsive, adaptive layout that scales from desktop to tablet (mobile support is secondary, focusing on professional workflows).
   - State management via Redux for global project data, ensuring synchronization across panes.
   - Event-driven architecture: User actions (e.g., code edits, button clicks) trigger pipelines in Web Workers.

2. **Compilation Pipeline (Chisel to SystemVerilog):**
   - **Chisel Processing:** Utilizes Scala.js to run Chisel 7.4.0 (or later) in the browser. The repository's Chisel modules (e.g., Adder, ShiftRegister, PWMLEDAXI) are pre-bundled as Scala.js libraries. User-defined Chisel code is compiled to FIRRTL (Flexible Intermediate Representation for RTL) using an in-browser SBT equivalent (a lightweight Scala.js runner that emulates sbt tasks like `compile` and `runMain` for VerilogGenerator.scala).
   - **FIRRTL to SystemVerilog Conversion:** A Wasm-compiled version of CIRCT/firtool (version 1.137.0 or equivalent) processes FIRRTL. Fixed options from the repository's firtool_config.txt (e.g., --verification-flavor=inline, --preserve-values=named) are applied by default, with user-configurable overrides for property preservation and optimization.
   - **Configuration Integration:** Adapts the repository's menuconfig-style system into a graphical interface, generating equivalent .config.mk and generation_config.json files in memory for the pipeline.

3. **Analysis Plugins (LIR/CIRCT Extensions):**
   - **Dataflow Analysis:** A CIRCT-based plugin (compiled to Wasm) analyzes the RTLIL output (generated via firtool's RTLIL export option). It computes dataflow graphs, highlighting dependencies, critical paths, and potential proof bottlenecks (e.g., high fanout signals that may complicate induction proofs).
   - **Proof Definition Assistance:** An MLIR pass plugin suggests LTL properties based on module structure, drawing from the repository's examples (e.g., assumptions/assertions in ShiftRegister). It integrates with the editor for auto-insertion of Chisel LTL constructs like AssertProperty and AssumeProperty.
   - **Performance Optimization:** Plugins evaluate proof strategies (e.g., k-induction vs. IC3/PDR) and recommend parameters, such as bound depths, based on design complexity metrics.

4. **Verification Engine (EBMC Integration):**
   - The provided Wasm EBMC binary is invoked directly on the generated SystemVerilog and SVA properties. Scripts like run_formal.sh and inline_verification.py from the repository are ported to JavaScript/Wasm equivalents, handling post-processing and algorithm selection (default, k-induction, IC3).
   - Supports layered properties (via chisel3.layer.block) with inline or bind modes, defaulting to inline for reliability as per repository guidance.
   - Outputs detailed logs, proof statuses (proved, falsified, unbounded), and counterexamples, visualized in the UI.

5. **Backend Emulation (Client-Side Only):**
   - No server is required; all operations use Wasm and JavaScript. Heavy tasks (e.g., firtool execution) run in dedicated Web Workers to prevent UI blocking.
   - Error handling is robust, with diagnostics mapped back to Chisel source lines for intuitive debugging.
   - Extensibility: Plugins are loaded as Wasm modules, allowing future additions like Yosys integration for synthesis previews.

This architecture ensures a productive flow: From Chisel code entry to verification results in under 10 seconds for typical designs (assuming modern hardware), fostering rapid iteration akin to software development tools.

### Interface Design: A Vision of Elegance and Productivity

The interface embodies Steve Jobs' ethos—simple yet profound, where every pixel serves a purpose, and technology fades into the background to amplify human creativity. It features a fresh, modern aesthetic: A dark-mode default with subtle gradients (inspired by macOS Ventura but evolved for 2026), high-contrast typography (system sans-serif fonts like SF Pro), and fluid animations (using Framer Motion) for transitions. The layout is divided into resizable panes with drag handles, adapting intelligently to screen size via CSS Grid. Colors are purposeful: Neutral grays for backgrounds, vibrant blues/greens for success states, and reds for errors, ensuring accessibility (WCAG 2.1 compliance).

The design prioritizes "push-button" simplicity for core workflows while offering depth for experts, with progressive disclosure (e.g., tooltips, expandable sections) to avoid overwhelming novices. It's understandable through intuitive icons (from Lucide Icons), contextual help overlays, and a guided onboarding tour. Technologically advanced elements include real-time collaboration via WebRTC (for team reviews), AI-assisted code completion (powered by a lightweight Wasm LLM for Chisel suggestions), and immersive visualizations that feel "alive."

#### Main Layout and Navigation
- **Top Bar (Header):** A slim, fixed navigation bar with the ChiselForge logo (a stylized anvil forging a circuit), project name (editable), and actions: New Project, Open/Save (from IndexedDB or export to ZIP), Share (generates a serialized link), and Help (contextual docs). On the right: A global "Verify" button—prominent, rounded, with a pulsing animation when ready—triggers the full pipeline with one click. Adjacent toggles for dark/light mode and settings (e.g., theme, editor preferences).
- **Sidebar (Left Pane, 20% width):** A collapsible panel for project structure. It displays a file tree (Chisel sources, generated artifacts like FIRRTL/Verilog), module selector (pre-loaded from repository examples like PWMLED or user-added), and configuration wizard. The wizard replaces menuconfig with a modern form: Accordion sections for Module Selection, Verification Mode (dropdown: Default, K-Induction, IC3), Property Layers (checkboxes with previews), Signal Preservation (slider: None to All, with warnings), and Randomization (toggle). Changes auto-save and preview impacts (e.g., "This may increase proof time by 20%").
- **Central Editor Pane (60% width):** The heart of the app—a full-featured Monaco Editor customized for Chisel. It supports syntax highlighting, linting (via Scala.js-integrated Chisel parser), autocompletion (e.g., suggesting LTL properties), and inline diagnostics (errors underlined with hover explanations). Multi-tab support for multiple files (e.g., main.scala, utils.scala). Advanced features: A "Property Builder" overlay (activated by right-click) for dragging-and-dropping assertions/assumptions from a palette, inspired by visual programming tools but grounded in text. Real-time preview of generated FIRRTL snippets in a mini-pane below.
- **Right Analysis and Output Pane (20% width, expandable):** Split into tabs for dynamic content:
  - **Dataflow Tab:** Visualizes the RTLIL graph using Cytoscape.js—nodes as signals/modules, edges as dependencies, with zoom/pan and highlighting (e.g., click a node to jump to code). Plugins analyze for bottlenecks, displaying metrics like fanout depth and suggesting optimizations (e.g., "Partition this submodule for faster proofs").
  - **Verification Tab:** Post-"Verify" results appear here. A clean dashboard shows overall status (e.g., "All 15 Properties Proved" in bold green), a table of properties (columns: Name, Type, Status, Bound, Time), and expandable sections for logs/counterexamples. Counterexamples render as waveform viewers (using WaveDrom in SVG) for intuitive debugging.
  - **Console Tab:** Raw logs from compilation/verification, searchable and filterable, with copy-to-clipboard buttons.
- **Bottom Status Bar:** Displays real-time feedback (e.g., "Compiling Chisel... 45%"), warnings (e.g., "PRESERVE=all may cause type errors"), and quick actions (e.g., "Re-run with K-Induction").

#### Productive Flow and Advanced Features
- **Push-Button Workflow:** Start with a template (e.g., load ShiftRegister from repo). Edit code in the editor. Configure in sidebar (defaults to repository's recommended settings). Click "Verify"—the app orchestrates the pipeline: Chisel to FIRRTL (Scala.js), FIRRTL to SV/RTLIL (Wasm firtool), analysis (plugins), then EBMC (Wasm). Results populate panes instantly, with notifications (e.g., toast messages) for completion.
- **Technological Advancements:** 
  - **AI Integration:** A subtle "Assist" button in the editor uses a Wasm-based model to suggest proofs or refactor code (e.g., "Add assumption for clock stability?").
  - **Visualization Freshness:** Dataflow graphs are interactive 3D (using Three.js for optional rotation), feeling "new" and immersive.
  - **Collaboration:** Real-time co-editing with cursors and chat, secured via end-to-end encryption.
  - **Extensibility:** A plugin marketplace (in-app) for community CIRCT passes, loaded as Wasm modules.
- **Usefulness and Understandability:** Every feature solves a pain point—e.g., auto-mapping EBMC errors to Chisel lines reduces debugging time. The interface is fresh: No cluttered menus; instead, contextual actions (e.g., hover a property in code to see verification preview). It's respectful of the user's time, with keyboard shortcuts (e.g., Ctrl+Enter for Verify) and undo/redo across the app.

This design ensures ChiselForge is not merely a tool but an extension of the engineer's mind—elegant, powerful, and transformative, worthy of Steve Jobs' approval.
