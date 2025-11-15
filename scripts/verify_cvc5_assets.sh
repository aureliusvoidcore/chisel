#!/usr/bin/env bash
set -euo pipefail
SITE_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
ASSETS_DIR="$SITE_ROOT/assets/cvc5"
JS="$ASSETS_DIR/cvc5.js"
WASM="$ASSETS_DIR/cvc5.wasm"

missing=0
if [[ ! -f "$JS" ]]; then echo "Missing: $JS"; missing=1; fi
if [[ ! -f "$WASM" ]]; then echo "Missing: $WASM"; missing=1; fi
if [[ $missing -eq 1 ]]; then exit 1; fi

echo "Sizes:"; ls -lh "$JS" "$WASM"

if command -v sha256sum >/dev/null; then
  echo "SHA256:"; sha256sum "$JS" "$WASM"
fi

if ! grep -q "MODULARIZE" "$JS"; then
  echo "Warning: cvc5.js may not be built with -s MODULARIZE" >&2
fi

if grep -qE "emscripten_resize_heap|ALLOW_MEMORY_GROWTH" "$JS"; then
  echo "Memory growth: ENABLED (heuristic)"
else
  echo "Warning: Memory growth may be DISABLED. Consider rebuilding with -s ALLOW_MEMORY_GROWTH=1 and a larger -s INITIAL_MEMORY." >&2
fi

echo "[✓] cvc5 assets look present."

# Check for embedded absolute paths in JS/WASM assets that might leak local usernames or build roots.
if grep -aEq "/home/|/Users/|/var/folders" "$JS" "$WASM"; then
  echo "Warning: Detected absolute-looking host paths embedded in cvc5 assets." >&2
  echo "         Consider rebuilding cvc5 with debug info disabled and path remapping, e.g.:" >&2
  echo "           ./configure.sh --wasm=JS --static --static-binary --auto-download \
                 --wasm-flags='-s MODULARIZE -s ALLOW_MEMORY_GROWTH=1 -s INITIAL_MEMORY=268435456 -g0'" >&2
  echo "           (and use -fdebug-prefix-map=[4m/your/build/root[0m=. in CXXFLAGS if needed)" >&2
fi
