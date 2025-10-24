#!/bin/bash

# Install Polly CLI for local development
# This creates a symlink in ~/.bun/bin so you can use 'polly' globally

set -e

SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
PROJECT_ROOT="$( cd "$SCRIPT_DIR/.." && pwd )"
CLI_PATH="$PROJECT_ROOT/packages/polly/cli/polly.ts"

# Ensure ~/.bun/bin exists
mkdir -p ~/.bun/bin

# Create symlink
ln -sf "$CLI_PATH" ~/.bun/bin/polly

# Make it executable
chmod +x "$CLI_PATH"

echo "✓ Polly CLI installed!"
echo ""
echo "Make sure ~/.bun/bin is in your PATH:"
echo "  export PATH=\"\$HOME/.bun/bin:\$PATH\""
echo ""
echo "Add this to your ~/.zshrc or ~/.bashrc to make it permanent."
echo ""
echo "You can now use: polly <command>"
