#!/usr/bin/env bash
# Scan the repository for tokens, secrets, and sensitive data that should not be in git history.
# Usage: ./scripts/scan-secrets.sh [--history]   (--history scans all git history, not just working tree)

set -euo pipefail

RED='\033[0;31m'
YELLOW='\033[0;33m'
GREEN='\033[0;32m'
NC='\033[0m'

SCAN_HISTORY=false
if [[ "${1:-}" == "--history" ]]; then
  SCAN_HISTORY=true
fi

ISSUES=0

report() {
  local level="$1" msg="$2"
  if [[ "$level" == "error" ]]; then
    echo -e "${RED}  FOUND${NC}  $msg"
    ISSUES=$((ISSUES + 1))
  elif [[ "$level" == "warn" ]]; then
    echo -e "${YELLOW}  WARN ${NC}  $msg"
  fi
}

scan_content() {
  local label="$1" pattern="$2" exclude="${3:-}"
  local grep_args=(-rn --include='*.ts' --include='*.js' --include='*.json' --include='*.yml' --include='*.yaml' --include='*.md' --include='*.sh' --include='*.env*' --include='*.toml' --include='*.cfg')
  grep_args+=(--exclude-dir=node_modules --exclude-dir=.bun --exclude-dir=dist --exclude-dir=out --exclude-dir=coverage --exclude-dir=.git)

  local results
  if [[ -n "$exclude" ]]; then
    results=$(grep -E "${grep_args[@]}" "$pattern" . 2>/dev/null | grep -vE "$exclude" || true)
  else
    results=$(grep -E "${grep_args[@]}" "$pattern" . 2>/dev/null || true)
  fi

  if [[ -n "$results" ]]; then
    report "error" "$label"
    echo "$results" | head -10 | sed 's/^/         /'
    local count
    count=$(echo "$results" | wc -l | tr -d ' ')
    if [[ "$count" -gt 10 ]]; then
      echo "         ... and $((count - 10)) more"
    fi
  fi
}

scan_history_content() {
  local label="$1" pattern="$2"
  local results
  results=$(git log -p --all -S "$pattern" --diff-filter=A -- ':(exclude)node_modules' 2>/dev/null | head -20 || true)
  if [[ -n "$results" ]]; then
    report "error" "$label (in git history)"
    echo "$results" | head -5 | sed 's/^/         /'
  fi
}

echo ""
echo "Scanning for secrets and sensitive data..."
echo "==========================================="
echo ""

# --- AWS Credentials ---
echo "Checking: AWS credentials"
scan_content "AWS Access Key ID" 'AKIA[0-9A-Z]{16}'
scan_content "AWS Secret Key" 'aws_secret_access_key\s*=' 'example|EXAMPLE|placeholder|your-'

# --- API Keys & Tokens ---
echo "Checking: API keys & tokens"
scan_content "GitHub Token" 'gh[pousr]_[A-Za-z0-9_]{36,}' 'example|mock|test|placeholder'
scan_content "OpenAI API Key" 'sk-[A-Za-z0-9]{20,}' 'test|mock|spec|\.test\.'
scan_content "Anthropic API Key" 'sk-ant-[A-Za-z0-9_-]{20,}'
scan_content "Slack Token" 'xox[bpors]-[A-Za-z0-9-]{10,}'
scan_content "Discord Token" '[MN][A-Za-z\d]{23,}\.[\w-]{6}\.[\w-]{27}'
scan_content "NPM Token" 'npm_[A-Za-z0-9]{36}'
scan_content "Heroku API Key" 'heroku.*[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}'

# --- Private Keys ---
echo "Checking: Private keys & certificates"
scan_content "Private Key Header" '-----BEGIN (RSA |DSA |EC |OPENSSH |PGP )?PRIVATE KEY' 'example|test|mock'

# Check for PEM files tracked by git
pem_files=$(git ls-files '*.pem' 2>/dev/null || true)
if [[ -n "$pem_files" ]]; then
  report "error" "PEM files tracked by git:"
  echo "$pem_files" | sed 's/^/         /'
fi

# --- Passwords & Secrets in Code ---
echo "Checking: Hardcoded passwords & secrets"
scan_content "Hardcoded password" '(password|passwd|pwd)\s*[:=]\s*["\x27][^"\x27]{8,}' 'example|placeholder|\.test\.|test\.ts|type|interface|schema|\?\s*string'
scan_content "Hardcoded secret" '(secret|SECRET)(_KEY|_TOKEN)?\s*[:=]\s*["\x27][^"\x27]{8,}' 'example|placeholder|test|mock|type|interface|schema'
scan_content "Hardcoded API key assignment" '(api_key|apiKey|API_KEY)\s*[:=]\s*["\x27][A-Za-z0-9+/=_-]{16,}' 'example|placeholder|test|mock|type|interface|schema|process\.env'

# --- .env files ---
echo "Checking: Environment files"
env_tracked=$(git ls-files '.env' '.env.local' '.env.*.local' '**/.env' '**/.env.local' 2>/dev/null || true)
if [[ -n "$env_tracked" ]]; then
  report "error" ".env files tracked by git:"
  echo "$env_tracked" | sed 's/^/         /'
fi

# --- Database connection strings ---
echo "Checking: Connection strings"
scan_content "Database URL with credentials" '(mysql|postgres|postgresql|mongodb|redis):\/\/[^:]+:[^@]+@' 'example|localhost|placeholder|test'

# --- JWT / Bearer tokens ---
echo "Checking: Tokens in code"
scan_content "Hardcoded JWT" 'eyJ[A-Za-z0-9_-]{10,}\.eyJ[A-Za-z0-9_-]{10,}\.' 'test|mock|example'
scan_content "Hardcoded Bearer token" 'Bearer\s+[A-Za-z0-9_-]{20,}' 'test|mock|example|placeholder'

# --- Git history scan (optional, slower) ---
if $SCAN_HISTORY; then
  echo ""
  echo "Scanning git history (this may take a while)..."
  echo "================================================="
  scan_history_content "AWS Key in history" "AKIA"
  scan_history_content "Private key in history" "BEGIN.*PRIVATE KEY"
  scan_history_content "GitHub token in history" "ghp_"
  scan_history_content "OpenAI key in history" "sk-ant-"
fi

# --- Summary ---
echo ""
echo "==========================================="
if [[ $ISSUES -eq 0 ]]; then
  echo -e "${GREEN}No secrets or sensitive data found.${NC}"
else
  echo -e "${RED}Found $ISSUES issue(s) that should be reviewed.${NC}"
  echo "Fix these before committing or publishing."
fi
echo ""
exit $ISSUES
