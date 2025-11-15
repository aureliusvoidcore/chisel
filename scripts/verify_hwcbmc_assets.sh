#!/usr/bin/env bash
set -euo pipefail

# Lightweight verification of hw-cbmc WebAssembly build artifacts.
# Does not execute the module (requires browser), but checks presence and metadata.

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_DIR="$ROOT_DIR/hwcbmc_build"

echo "[verify] root    : $ROOT_DIR"
echo "[verify] out dir : $OUT_DIR"

JS="$OUT_DIR/hwcbmc.js"
WASM="$OUT_DIR/hwcbmc.wasm"
WRAP="$OUT_DIR/hwcbmc-wrapper.js"
IC3_MARKER="$OUT_DIR/ic3_enabled.txt"

fail() { echo "[verify] ERROR: $*" >&2; exit 1; }

[ -f "$JS" ]   || fail "Missing hwcbmc.js"
[ -f "$WASM" ] || fail "Missing hwcbmc.wasm"
[ -f "$WRAP" ] || fail "Missing hwcbmc-wrapper.js"

echo "[verify] files present"
ls -lh "$JS" "$WASM" "$WRAP" | sed 's/^/[verify] /'

# IC3 presence (optional)
if [ -f "$IC3_MARKER" ]; then
	echo "[verify] IC3 marker present (ic3_enabled.txt) — IC3 engine built in."
else
	echo "[verify] IC3 marker not found — build likely excludes IC3." 
fi

# Quick sanity check for Emscripten modularized loader and export name
# Newer Emscripten versions do not include the literal string "MODULARIZE" in the output,
# so detect modularization by the factory wrapper pattern and export name.
if ! grep -qE "var[[:space:]]+HWCBMCModule[[:space:]]*=" "$JS"; then
	fail "hwcbmc.js does not appear to be modularized (factory 'var HWCBMCModule = ...' not found)"
fi
grep -q "HWCBMCModule" "$JS" || fail "EXPORT_NAME HWCBMCModule not found in hwcbmc.js"

# Optional: ensure wasm is non-trivial in size (e.g., > 1MB)
WASM_SIZE=$(stat -c%s "$WASM" 2>/dev/null || stat -f%z "$WASM")
if [ "${WASM_SIZE:-0}" -lt 1000000 ]; then
	echo "[verify] WARNING: wasm looks unusually small ($WASM_SIZE bytes)."
fi

echo "[verify] OK: hwcbmc wasm assets look consistent."

# Warn if WASM/JS contain embedded absolute host paths (privacy leak)
if grep -aEq "/home/|/Users/|/var/folders" "$JS" "$WASM"; then
	echo "[verify] WARNING: Detected absolute-looking host paths inside hwcbmc assets." >&2
	echo "          Consider rebuilding with debug info disabled (-g0) and prefix mapping:" >&2
	echo "            CXXFLAGS=\"${CXXFLAGS:-} -g0 -fdebug-prefix-map=$ROOT_DIR=.\"" >&2
	echo "          (these are now the defaults in scripts/build_hwcbmc_wasm.sh)" >&2
fi

