#!/usr/bin/env bash

set -euo pipefail

download()
{
  if command -v wget >/dev/null 2>&1; then
    wget -q -O "$2" "$1"
  elif command -v curl >/dev/null 2>&1; then
    curl -fsSL "$1" -o "$2"
  else
    echo "Cannot download the Eunoia formatter: install wget or curl." >&2
    exit 1
  fi
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CVC5_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
CPC_DIR="$CVC5_DIR/proofs/eo/cpc"

# This is the Ethos commit that introduced the Eunoia formatter.
ETHOS_VERSION="0330141912777fe568df2be6c4a465aef58241ad"
FORMATTER_URL="https://raw.githubusercontent.com/cvc5/ethos/$ETHOS_VERSION/contrib/eo_format.py"
FORMATTER="$(mktemp "${TMPDIR:-/tmp}/cvc5-eo-format.XXXXXX")"
trap 'rm -f "$FORMATTER"' EXIT

download "$FORMATTER_URL" "$FORMATTER"

# Formatting includes recursively would reach the generated rewrite signatures.
# List all other files explicitly and disable recursive include processing.
find "$CPC_DIR" -type f -name '*.eo' \
  ! -path "$CPC_DIR/rules/Rewrites.eo" \
  ! -path "$CPC_DIR/expert/rules/RewritesExpert.eo" \
  -exec python3 "$FORMATTER" --no-recursive {} +
