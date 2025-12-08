#!/usr/bin/env bash

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"
TOOLS_DIR="$PROJECT_ROOT/tools"
SBT_VERSION="1.10.5"

echo "Chisel Sandbox Setup"
echo "===================="
echo ""

if [ -d "$TOOLS_DIR/sbt" ]; then
    echo "SBT already installed in $TOOLS_DIR/sbt"
    echo "To reinstall, remove the tools directory first: rm -rf tools"
    exit 0
fi

echo "Installing SBT $SBT_VERSION locally..."
mkdir -p "$TOOLS_DIR"
cd "$TOOLS_DIR"

echo "Downloading SBT..."
curl -fL "https://github.com/sbt/sbt/releases/download/v${SBT_VERSION}/sbt-${SBT_VERSION}.tgz" -o sbt.tgz

echo "Extracting SBT..."
tar xzf sbt.tgz
rm sbt.tgz

echo ""
echo "Setup complete!"
echo ""
echo "SBT installed to: $TOOLS_DIR/sbt"
echo ""
echo "To use this environment:"
echo "  1. Install direnv if not already installed"
echo "  2. Run: direnv allow"
echo "  3. Enter the directory to auto-load the environment"
echo ""
echo "Or manually:"
echo "  export PATH=\"$TOOLS_DIR/sbt/bin:\$PATH\""
