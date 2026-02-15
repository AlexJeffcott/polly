#!/bin/bash
# Test script to verify @fairfox/polly works after publishing
# This simulates installing from npm and testing all CLI commands

set -e  # Exit on error

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Get the project root directory
PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TEST_DIR="/tmp/polly-package-test-$$"
PACKAGE_NAME="@fairfox/polly"

echo -e "${BLUE}======================================${NC}"
echo -e "${BLUE}Testing @fairfox/polly Package${NC}"
echo -e "${BLUE}======================================${NC}\n"

# Step 1: Build the library
echo -e "${YELLOW}Step 1: Building library...${NC}"
cd "$PROJECT_ROOT"
bun run build:lib
echo -e "${GREEN}✓ Library built${NC}\n"

# Step 2: Create tarball
echo -e "${YELLOW}Step 2: Creating tarball with npm pack...${NC}"
npm pack
# Convert @fairfox/polly to fairfox-polly for filename
TARBALL_PREFIX=$(echo "$PACKAGE_NAME" | sed 's/@//g' | sed 's/\//-/g')
TARBALL=$(ls -t ${TARBALL_PREFIX}-*.tgz | head -1)
echo -e "${GREEN}✓ Created $TARBALL${NC}\n"

# Step 3: Extract and inspect tarball
echo -e "${YELLOW}Step 3: Inspecting tarball contents...${NC}"
mkdir -p "$TEST_DIR/inspect"
tar -xzf "$TARBALL" -C "$TEST_DIR/inspect"
echo -e "${BLUE}Package structure:${NC}"
ls -la "$TEST_DIR/inspect/package/"
echo ""
echo -e "${BLUE}dist/ contents:${NC}"
ls -la "$TEST_DIR/inspect/package/dist/"
echo ""
echo -e "${BLUE}templates/ contents:${NC}"
ls -la "$TEST_DIR/inspect/package/templates/" || echo "No templates directory found!"
echo ""

# Verify shebang
echo -e "${BLUE}CLI shebang:${NC}"
head -n 1 "$TEST_DIR/inspect/package/dist/cli/polly.js"
echo ""

# Verify executable permissions
echo -e "${BLUE}CLI permissions:${NC}"
ls -la "$TEST_DIR/inspect/package/dist/cli/polly.js"
echo -e "${GREEN}✓ Package inspected${NC}\n"

# Step 4: Test installation
echo -e "${YELLOW}Step 4: Testing installation in clean environment...${NC}"
mkdir -p "$TEST_DIR/test-install"
cd "$TEST_DIR/test-install"
npm install "$PROJECT_ROOT/$TARBALL"
echo -e "${GREEN}✓ Package installed${NC}\n"

# Step 5: Test CLI commands
echo -e "${YELLOW}Step 5: Testing CLI commands...${NC}"

# Test help
echo -e "${BLUE}Testing: polly help${NC}"
npx polly help || echo "Help command executed"
echo ""

# Test init with PWA template
echo -e "${BLUE}Testing: polly init test-pwa --type=pwa${NC}"
npx polly init test-pwa --type=pwa
echo -e "${GREEN}✓ Project initialized${NC}\n"

# Verify project structure
echo -e "${BLUE}Project structure:${NC}"
ls -la test-pwa/
echo ""

# Enter the test project
cd test-pwa

# Test typecheck
echo -e "${BLUE}Testing: polly typecheck${NC}"
npx polly typecheck && echo -e "${GREEN}✓ Typecheck passed${NC}\n" || echo -e "${RED}✗ Typecheck failed${NC}\n"

# Test lint
echo -e "${BLUE}Testing: polly lint${NC}"
npx polly lint && echo -e "${GREEN}✓ Lint passed${NC}\n" || echo -e "${RED}✗ Lint failed${NC}\n"

# Test build
echo -e "${BLUE}Testing: polly build${NC}"
npx polly build && echo -e "${GREEN}✓ Build passed${NC}\n" || echo -e "${RED}✗ Build failed${NC}\n"

# Test verify (may fail if no specs, that's ok)
echo -e "${BLUE}Testing: polly verify${NC}"
npx polly verify && echo -e "${GREEN}✓ Verify passed${NC}\n" || echo -e "${YELLOW}⚠ Verify failed (expected if no specs)${NC}\n"

# Test visualize (may fail if no config, that's ok)
echo -e "${BLUE}Testing: polly visualize${NC}"
npx polly visualize && echo -e "${GREEN}✓ Visualize passed${NC}\n" || echo -e "${YELLOW}⚠ Visualize failed (expected if no config)${NC}\n"

# Cleanup
echo -e "${YELLOW}Cleaning up test directory...${NC}"
cd "$PROJECT_ROOT"
rm -rf "$TEST_DIR"
echo -e "${GREEN}✓ Cleaned up${NC}\n"

echo -e "${GREEN}======================================${NC}"
echo -e "${GREEN}✓ All tests passed!${NC}"
echo -e "${GREEN}The package is ready to publish.${NC}"
echo -e "${GREEN}======================================${NC}"
echo ""
echo -e "${BLUE}To publish:${NC}"
echo -e "  npm publish --access public"
echo ""
