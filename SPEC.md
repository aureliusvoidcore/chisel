# Site Specification

This repository hosts a GitHub Pages site built with Jekyll. The site is organized as a set of section pages and interactive, in-browser tools for formal verification and hardware development.

## Structure

- Shared layout and navigation: `_layouts/default.html`
- Section pages: `pages/`
- WebAssembly tool front-ends:
  - ABC: `abc_build/` and `/pages/formal-verification/abc`
  - cvc5: `assets/cvc5/` and `/pages/formal-verification/cvc5`
  - HW-CBMC/EBMC: `hwcbmc_build/` and `/pages/formal-verification/hwcbmc`
  - ChiselForge: `chisel_forge/` and `/chisel_forge/dist/`

## Local development

Prerequisites: Ruby and Bundler.

```sh
bundle install
bundle exec jekyll serve
```

Visit `http://127.0.0.1:4000`.

## Content guidelines

- Prefer concise, technical language.
- Keep section pages as hubs: link out to tool UIs and focused guides.
- Avoid code snippets that are not tied to a tool or a specific guide.
