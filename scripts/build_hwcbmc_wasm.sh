#!/usr/bin/env bash
set -euo pipefail

# Build hw-cbmc / ebmc as WebAssembly using Emscripten.
#
# This script expects:
#   - emcc/em++ available on PATH (activate emsdk before running)
#   - repo root as current working directory (aureliusvoidcore.github.io)
#   - cloned hw-cbmc sources in ./hw-cbmc (git submodule)
#
# Environment options:
#   HWCBMC_WASM_FORCE_CLEAN=1   Force cleaning CBMC libs and EBMC objects before build (default: 0)
#   HWCBMC_WASM_ENABLE_IC3=1    Include IC3 engine in the build (default: 0 to keep binary size smaller)
#   HWCBMC_WASM_LENIENT_LINK=1  Allow undefined symbols at link time (default: 0)
#
# Output:
#   - hwcbmc_build/hwcbmc.js
#   - hwcbmc_build/hwcbmc.wasm

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
HWCBMC_SRC_DIR="$ROOT_DIR/hw-cbmc"
OUT_DIR="$ROOT_DIR/hwcbmc_build"

mkdir -p "$OUT_DIR"

echo "[hwcbmc] root    : $ROOT_DIR"
echo "[hwcbmc] sources : $HWCBMC_SRC_DIR"
echo "[hwcbmc] out dir : $OUT_DIR"

if ! command -v em++ >/dev/null 2>&1; then
	echo "error: em++ not found on PATH. Please activate emsdk first." >&2
	exit 1
fi

# Ensure CBMC submodule is present
if [ ! -d "$HWCBMC_SRC_DIR/lib/cbmc/.git" ]; then
	echo "[hwcbmc] CBMC submodule not initialized; attempting to init/update"
	git -C "$HWCBMC_SRC_DIR" submodule update --init || {
		echo "error: failed to init CBMC submodule" >&2; exit 1; }
fi

# Ensure Minisat is available (CBMC target will download if needed)
if [ ! -d "$HWCBMC_SRC_DIR/lib/cbmc/minisat-2.2.1" ] && [ ! -d "$HWCBMC_SRC_DIR/lib/cbmc/src/minisat" ]; then
	echo "[hwcbmc] downloading Minisat2 for CBMC"
	make -C "$HWCBMC_SRC_DIR/lib/cbmc/src" minisat2-download || {
		echo "error: minisat2 download failed" >&2; exit 1; }
fi

# Optional clean: set HWCBMC_WASM_FORCE_CLEAN=1 to force a full clean. Default: skip to preserve build cache/time.
if [[ "${HWCBMC_WASM_FORCE_CLEAN:-0}" == "1" ]]; then
	echo "[hwcbmc] forcing clean of previous build artifacts"
	make -C "$HWCBMC_SRC_DIR/src" clean || true
	make -C "$HWCBMC_SRC_DIR/lib/cbmc/src" clean || true
else
	echo "[hwcbmc] skipping clean (incremental build)"
fi

echo "[hwcbmc] configuring WebAssembly build (single-file ebmc binary)"

# We reuse the existing ebmc object files / libraries but link them via em++.
# This is a pragmatic best-effort build; some features (external SMT solvers,
# filesystem assumptions, multi-process) may be stubbed for the browser.

EBMC_DIR="$HWCBMC_SRC_DIR/src/ebmc"

if [ ! -d "$EBMC_DIR" ]; then
	echo "error: ebmc directory not found at $EBMC_DIR" >&2
	exit 1
fi

echo "[hwcbmc] building static libs / objects with native toolchain first"
echo "[hwcbmc] pre-generating files with native toolchain (for headers/inc)"

# Some directories generate headers using small helper binaries (e.g., file_converter).
# Build those helpers natively to generate the artifacts, then switch to emscripten.
for gen_dir in "$HWCBMC_SRC_DIR/lib/cbmc/src/ansi-c" "$HWCBMC_SRC_DIR/lib/cbmc/src/cpp"; do
	echo "[hwcbmc] generating files in ${gen_dir} (native)"
	make -C "$gen_dir" generated_files -j"$(nproc)" || true
done

echo "[hwcbmc] compiling required libraries with Emscripten toolchain"

export CC=emcc CXX=em++ AR=emar RANLIB=emranlib
# Global compile flags for emscripten builds. Do NOT define LOCAL_IREP_IDS here to avoid conflicts
# with per-directory Makefiles (src/common) that already define it.
# Add -g0 to strip debug info and -fdebug-prefix-map to avoid embedding absolute build paths.
export CXXFLAGS="${CXXFLAGS:-} -g0 -fdebug-prefix-map=$ROOT_DIR=. -DHAVE_MINISAT2 -I$HWCBMC_SRC_DIR/src"

echo "[hwcbmc] purging stale objects for SVA-aware rebuild (ebmc + verilog + temporal + netlist)"
for purge in src/ebmc src/verilog src/temporal-logic src/trans-netlist src/trans-word-level; do
	find "$HWCBMC_SRC_DIR/$purge" -maxdepth 1 -name '*.o' -delete 2>/dev/null || true
done

# Ensure util library (which defines the irep id symbols) is rebuilt with LOCAL_IREP_IDS.
echo "[hwcbmc] rebuilding util with LOCAL_IREP_IDS for extended irep ids (SVA)"
make -C "$HWCBMC_SRC_DIR/lib/cbmc/src/util" clean || true
# Clang's preprocessor may not accept a string-literal macro for #include; use angle-bracket form.
# We escape '<' and '>' so shells/make do not treat them as redirections.
UTIL_CXXFLAGS="${CXXFLAGS} -DLOCAL_IREP_IDS=\\<hw_cbmc_irep_ids.h\\>"
make -C "$HWCBMC_SRC_DIR/lib/cbmc/src/util" CXXFLAGS="$UTIL_CXXFLAGS" -j"$(nproc)" || { echo "error: failed rebuilding util with extended ids" >&2; exit 1; }

# Build core cbmc libraries (util first due to dependency chain)
for dir in big-int langapi analyses linking pointer-analysis solvers goto-programs goto-symex ansi-c cpp json json-symtab-language xmllang statement-list; do
	echo "[hwcbmc] building lib/cbmc/src/$dir"
	make -C "$HWCBMC_SRC_DIR/lib/cbmc/src/$dir" -j"$(nproc)" || { echo "error: failed building $dir" >&2; exit 1; }
done

# Build ebmc dependency libs in src (hardware specific)
for dir in temporal-logic trans-netlist trans-word-level aiger vhdl smvlang verilog; do
	echo "[hwcbmc] building src/$dir"
	make -C "$HWCBMC_SRC_DIR/src/$dir" -j"$(nproc)" || { echo "error: failed building $dir" >&2; exit 1; }
done

ENABLE_IC3=${HWCBMC_WASM_ENABLE_IC3:-0}
if [[ "$ENABLE_IC3" == "1" ]]; then
    echo "[hwcbmc] building src/ic3 (IC3 engine + Minisat)"
    # Clean any native-built objects first to ensure emscripten toolchain is used
    find "$HWCBMC_SRC_DIR/src/ic3" -maxdepth 1 -name '*.o' -delete 2>/dev/null || true
    find "$HWCBMC_SRC_DIR/src/ic3/minisat" -type f -name '*.o' -delete 2>/dev/null || true

    # Compile Minisat sources needed by IC3
    em++ -c -MMD -MP -std=c++17 -O2 ${CXXFLAGS} -I"$HWCBMC_SRC_DIR/lib/cbmc/src" -I"$HWCBMC_SRC_DIR/src/ic3/minisat" -I"$HWCBMC_SRC_DIR/src/ic3/minisat/minisat" \
	    -o "$HWCBMC_SRC_DIR/src/ic3/minisat/minisat/core/Solver.o" \
	    "$HWCBMC_SRC_DIR/src/ic3/minisat/minisat/core/Solver.cc"
    em++ -c -MMD -MP -std=c++17 -O2 ${CXXFLAGS} -I"$HWCBMC_SRC_DIR/lib/cbmc/src" -I"$HWCBMC_SRC_DIR/src/ic3/minisat" -I"$HWCBMC_SRC_DIR/src/ic3/minisat/minisat" \
	    -o "$HWCBMC_SRC_DIR/src/ic3/minisat/minisat/simp/SimpSolver.o" \
	    "$HWCBMC_SRC_DIR/src/ic3/minisat/minisat/simp/SimpSolver.cc"

    # Compile IC3 engine sources
    IC3_INC=(
	    -I"$HWCBMC_SRC_DIR/src/ic3"
	    -I"$HWCBMC_SRC_DIR/src/ic3/build_prob"
	    -I"$HWCBMC_SRC_DIR/src/ic3/seq_circ"
	    -I"$HWCBMC_SRC_DIR/src/ic3/minisat"
	    -I"$HWCBMC_SRC_DIR/lib/cbmc/src"
	    -I"$HWCBMC_SRC_DIR/src"
    )

    for f in "$HWCBMC_SRC_DIR"/src/ic3/*.cc; do
	em++ -c -MMD -MP -std=c++17 -O2 ${CXXFLAGS} -DLOCAL_IREP_IDS=\<hw_cbmc_irep_ids.h\> "${IC3_INC[@]}" -o "${f%.cc}.o" "$f" || {
		    echo "error: failed compiling IC3 source $f" >&2; exit 1; }
    done

	# Compile IC3 build_prob problem generation sources
	for f in "$HWCBMC_SRC_DIR"/src/ic3/build_prob/*.cc; do
		em++ -c -MMD -MP -std=c++17 -O2 ${CXXFLAGS} -DLOCAL_IREP_IDS=\<hw_cbmc_irep_ids.h\> "${IC3_INC[@]}" -o "${f%.cc}.o" "$f" || {
			echo "error: failed compiling IC3 build_prob source $f" >&2; exit 1; }
	done

	# Compile sequential circuit representation sources (seq_circ)
	for f in "$HWCBMC_SRC_DIR"/src/ic3/seq_circ/*.cc; do
		em++ -c -MMD -MP -std=c++17 -O2 ${CXXFLAGS} -DLOCAL_IREP_IDS=\<hw_cbmc_irep_ids.h\> "${IC3_INC[@]}" -o "${f%.cc}.o" "$f" || {
			echo "error: failed compiling IC3 seq_circ source $f" >&2; exit 1; }
	done
else
    echo "[hwcbmc] IC3 disabled (set HWCBMC_WASM_ENABLE_IC3=1 to enable)."
fi


echo "[hwcbmc] compiling ebmc sources to WebAssembly"
pushd "$EBMC_DIR" >/dev/null

# Provide a minimal EBMC version unit, as upstream Makefile may generate this in native builds
EBMC_VER_SRC="$OUT_DIR/ebmc_version.cpp"
cat > "$EBMC_VER_SRC" <<'EOF'
extern const char *EBMC_VERSION = "hw-cbmc wasm";
EOF

EM_FLAGS=(
	-std=c++17
	-O2
	-g0
	-DHAVE_MINISAT2
	-s MODULARIZE=1
	-s EXPORT_NAME=HWCBMCModule
	-s ENVIRONMENT=web,worker
	-s ALLOW_MEMORY_GROWTH=1
	-s WASM_BIGINT=1
	# Keep the runtime alive across multiple callMain invocations
	-s EXIT_RUNTIME=0
	-s ASSERTIONS=1
	# Ensure filesystem is linked and accessible from JS (Module.FS)
	-s FILESYSTEM=1
	-s FORCE_FILESYSTEM=1
	-s EXPORTED_RUNTIME_METHODS=[FS,callMain]
	# ensure extended irep ids are visible when compiling ebmc sources directly
	-DLOCAL_IREP_IDS=\<hw_cbmc_irep_ids.h\>
)

# If IC3 is enabled, add a compile-time define so the UI can optionally detect it (and we will also drop a marker file later).
if [[ "$ENABLE_IC3" == "1" ]]; then
	EM_FLAGS+=( -DHWCBMC_HAS_IC3=1 )
fi

if [[ "${HWCBMC_WASM_LENIENT_LINK:-0}" == "1" ]]; then
    EM_FLAGS+=( -s ERROR_ON_UNDEFINED_SYMBOLS=0 )
fi

em++ "${EM_FLAGS[@]}" \
	-I"$HWCBMC_SRC_DIR/lib/cbmc/src" -I"$HWCBMC_SRC_DIR/src" \
	-o "$OUT_DIR/hwcbmc.js" \
	"$EBMC_VER_SRC" \
	main.cpp \
	ebmc_base.cpp ebmc_languages.cpp ebmc_parse_options.cpp ebmc_properties.cpp ebmc_solver_factory.cpp \
	format_hooks.cpp instrument_past.cpp instrument_buechi.cpp k_induction.cpp \
	liveness_to_safety.cpp live_signal.cpp netlist.cpp neural_liveness.cpp \
	output_file.cpp output_smv_word_level.cpp output_verilog.cpp property_checker.cpp \
	random_traces.cpp ranking_function.cpp report_results.cpp show_formula_solver.cpp \
	show_properties.cpp show_trans.cpp tautology_check.cpp transition_system.cpp waveform.cpp \
	completeness_threshold.cpp diameter.cpp diatest.cpp dimacs_writer.cpp bdd_engine.cpp bmc.cpp \
	../temporal-logic/*.o ../trans-netlist/*.o ../trans-word-level/*.o ../aiger/*.o ../vhdl/*.o ../smvlang/*.o ../verilog/*.o \
	$( [[ "$ENABLE_IC3" != "1" ]] && echo wasm_stubs.cpp ) \
	$( [[ "$ENABLE_IC3" == "1" ]] && echo ../ic3/*.o ../ic3/build_prob/*.o ../ic3/seq_circ/*.o ../ic3/minisat/minisat/core/Solver.o ../ic3/minisat/minisat/simp/SimpSolver.o ) \
	cegar/abstract.cpp cegar/bmc_cegar.cpp cegar/latch_ordering.cpp cegar/refine.cpp cegar/simulate.cpp cegar/verify.cpp \
	"$HWCBMC_SRC_DIR/lib/cbmc/src/util/util.a" \
	"$HWCBMC_SRC_DIR/lib/cbmc/src/big-int/big-int.a" \
	"$HWCBMC_SRC_DIR/lib/cbmc/src/langapi/langapi.a" \
	"$HWCBMC_SRC_DIR/lib/cbmc/src/goto-programs/goto-programs.a" \
	"$HWCBMC_SRC_DIR/lib/cbmc/src/solvers/solvers.a" \
	"$HWCBMC_SRC_DIR/lib/cbmc/src/json/json.a" \
	"$HWCBMC_SRC_DIR/lib/cbmc/src/ansi-c/ansi-c.a" \
	"$HWCBMC_SRC_DIR/lib/cbmc/src/cpp/cpp.a" \
	"$HWCBMC_SRC_DIR/lib/cbmc/src/goto-symex/goto-symex.a" \
	"$HWCBMC_SRC_DIR/lib/cbmc/src/pointer-analysis/pointer-analysis.a" \
	"$HWCBMC_SRC_DIR/lib/cbmc/src/analyses/analyses.a" \
	"$HWCBMC_SRC_DIR/lib/cbmc/src/xmllang/xmllang.a" \
	"$HWCBMC_SRC_DIR/lib/cbmc/src/linking/linking.a" \
	|| { echo "error: em++ linking for WebAssembly failed" >&2; exit 1; }

popd >/dev/null

if [[ "$ENABLE_IC3" == "1" ]]; then
	echo "[hwcbmc] built $OUT_DIR/hwcbmc.js and $OUT_DIR/hwcbmc.wasm (IC3 included)"
	echo "ic3" > "$OUT_DIR/ic3_enabled.txt"
else
	echo "[hwcbmc] built $OUT_DIR/hwcbmc.js and $OUT_DIR/hwcbmc.wasm (IC3 excluded)"
fi
