# aureliusvoidcore.github.io

This is the source for the GitHub Pages user site at:

https://aureliusvoidcore.github.io

The site is built with Jekyll; layouts live under `_layouts/` and pages under `pages/`.

The published site is organized as a set of section pages (e.g., Formal Verification, FPGA, SystemC, Mathematics) with interactive WebAssembly tools under `pages/`.

## Local development

Prerequisites: Ruby and Bundler.

1) Install gems

```sh
# optional: if Bundler is missing
gem install bundler

# install project dependencies
bundle install
```

2) Build the site

```sh
bundle exec jekyll build
```

3) Serve locally

```sh
bundle exec jekyll serve
# Visit http://localhost:4000
```

## Themes

The site includes multiple visual themes selectable from the on-page Appearance panel:

- Default
- Neon
- Matrix
- Spectrum
- Laser
- Amber Terminal
- Synth
- ROG Crimson
- Windows 98
- Amiga Workbench
- Macintosh Classic
- High-effects theme

The high-effects theme has additional styling in `assets/css/doom.css`, scoped to `body.theme-doom` so other themes are unaffected. The base theme system and animations are driven by `assets/js/main.js` and `assets/css/main.css`.

Notes
- This repo is the root/base of the user site, so `baseurl` is empty and `url` is set to https://aureliusvoidcore.github.io in `_config.yml`.
- Site structure overview:
	- Layouts: `_layouts/`
	- Pages: `pages/`
	- Interactive apps: `abc_build/`, `hwcbmc_build/`, `chisel_forge/`

## WebAssembly integrations

This site includes in-browser interfaces for formal tools compiled to WebAssembly:

- ABC (Berkeley) – `/pages/formal-verification/abc` (artifacts in `abc_build/`)
- CVC5 – `/pages/formal-verification/cvc5` (artifacts in `assets/cvc5/`)
- HW-CBMC (experimental) – `/pages/formal-verification/hwcbmc` (artifacts in `hwcbmc_build/`)

To build HW-CBMC for WASM locally (experimental), see:

- `scripts/build_hwcbmc_wasm.sh` – attempts an Emscripten build and places outputs in `hwcbmc_build/`
- `scripts/verify_hwcbmc_assets.sh` – checks that `hwcbmc.js`/`.wasm` and the wrapper are present

Note: HW-CBMC depends on CBMC and various libraries; a browser-targeted build may require patching or disabling unsupported features. The UI expects a modularized Emscripten module exported as `HWCBMCModule`.

