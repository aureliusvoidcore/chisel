#!/bin/bash
# Start both frontend and backend servers for development

set -e

# Colors for output
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
RED='\033[0;31m'
NC='\033[0m' # No Color

# Check for --fresh_start flag
if [[ "$1" == "--fresh_start" ]]; then
    echo -e "${RED}🔥 FRESH START: Killing all existing processes...${NC}"
    
    # Kill all node/npm processes related to this project
    pkill -f "vite" 2>/dev/null || true
    pkill -f "node.*dev" 2>/dev/null || true
    pkill -f "npm.*dev" 2>/dev/null || true
    pkill -f "npm.*start" 2>/dev/null || true
    pkill -f "chisel.*server" 2>/dev/null || true
    
    # Kill specific ports
    lsof -ti:3001 | xargs -r kill -9 2>/dev/null || true
    lsof -ti:5173 | xargs -r kill -9 2>/dev/null || true
    lsof -ti:5174 | xargs -r kill -9 2>/dev/null || true
    lsof -ti:5175 | xargs -r kill -9 2>/dev/null || true
    
    # Clear log files
    > /tmp/server.log
    > /tmp/server_new.log
    
    echo -e "${GREEN}✓ All processes killed and logs cleared${NC}"
    echo ""
    sleep 1
fi

echo -e "${BLUE}╔═══════════════════════════════════════════════════════╗${NC}"
echo -e "${BLUE}║           ChiselForge Development Setup               ║${NC}"
echo -e "${BLUE}╚═══════════════════════════════════════════════════════╝${NC}"
echo ""

# Initialize and setup chisel submodule
echo -e "${INFO_COLOR}Checking chisel submodule...${NC}"
if [ ! -d "chisel/.git" ]; then
    echo "Initializing chisel submodule..."
    git submodule update --init --recursive
fi

# Setup chisel tools if not already done
if [ ! -d "chisel/tools/sbt" ]; then
    echo -e "${INFO_COLOR}Setting up Chisel tools (first time only)...${NC}"
    (cd chisel && make setup)
fi

# Check if backend dependencies are installed
if [ ! -d "server/node_modules" ]; then
    echo -e "${BLUE}📦 Installing backend dependencies...${NC}"
    (cd server && npm install)
fi

# Check if frontend dependencies are installed
if [ ! -d "node_modules" ]; then
    echo -e "${BLUE}📦 Installing frontend dependencies...${NC}"
    npm install
fi

echo ""
echo -e "${GREEN}✓ All dependencies installed${NC}"
echo ""
echo -e "${BLUE}🚀 Starting servers...${NC}"
echo ""

# Start backend in background
echo -e "${BLUE}Starting backend server on http://localhost:3001${NC}"
# Ensure CHISEL_ROOT and EBMC_BIN are set for backend
# CHISEL_ROOT should point to the sibling chisel repo
export CHISEL_ROOT="$(realpath ../chisel)"
export EBMC_BIN="${EBMC_BIN:-ebmc}"
# Log backend output to /tmp/server.log for quick tailing
(cd server && PORT=3001 CHISEL_ROOT="$CHISEL_ROOT" EBMC_BIN="$EBMC_BIN" npm start > /tmp/server.log 2>&1) &
BACKEND_PID=$!

# Wait a moment for backend to start
sleep 2

# Start frontend
echo -e "${BLUE}Starting frontend dev server...${NC}"
# Point frontend to backend API explicitly
export VITE_API_URL="http://localhost:3001/api"
# Log frontend dev server to /tmp/server_new.log
npm run dev > /tmp/server_new.log 2>&1 &
FRONTEND_PID=$!

echo ""
echo -e "${GREEN}╔═══════════════════════════════════════════════════════╗${NC}"
echo -e "${GREEN}║              ChiselForge is Running!                  ║${NC}"
echo -e "${GREEN}╚═══════════════════════════════════════════════════════╝${NC}"
echo ""
echo -e "Frontend: ${BLUE}http://localhost:5173${NC}"
echo -e "Backend:  ${BLUE}http://localhost:3001${NC}"
echo ""
echo -e "${YELLOW}Press Ctrl+C to stop all servers${NC}"
echo ""

# Wait for Ctrl+C
trap "echo '' && echo 'Stopping servers...' && kill $BACKEND_PID $FRONTEND_PID 2>/dev/null; exit 0" INT

echo -e "${BLUE}Logs:${NC}"
echo -e "  Backend:  /tmp/server.log"
echo -e "  Frontend: /tmp/server_new.log"

# Keep script running
wait
