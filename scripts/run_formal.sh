#!/bin/bash
set -e

MODULE=$1
MODE=${2:-default}
# Use EBMC_BIN env var if set, otherwise default to 'ebmc'
EBMC_BIN=${EBMC_BIN:-ebmc}
GENERATED_DIR="generated/$MODULE"
SV_FILE="$GENERATED_DIR/$MODULE.sv"

if [ ! -f "$SV_FILE" ]; then
    echo "Error: Generated file $SV_FILE not found."
    exit 1
fi

echo "Preparing to run formal verification on $MODULE..."

# Extract layer defines
# Use awk to extract the second field (macro name) to avoid capturing comments
DEFINES=""
LAYERS=$(grep "^\s*\`ifdef layer" "$SV_FILE" | awk '{print $2}')

for layer in $LAYERS; do
    DEFINES="$DEFINES -D $layer"
done

echo "Detected layers: $LAYERS"

CMD="$EBMC_BIN --systemverilog $SV_FILE $DEFINES --bound 10"

if [ "$MODE" == "k-induction" ]; then
    CMD="$CMD --k-induction"
elif [ "$MODE" == "ic3" ]; then
    CMD="$CMD --ic3"
fi

echo "Running EBMC command:"
echo "$CMD"

$CMD
