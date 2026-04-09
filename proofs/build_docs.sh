#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$ROOT_DIR"

DOCS_DIR="docs"
MODULE_DOCS_DIR="$DOCS_DIR/md"
COMBINED_DOC="$DOCS_DIR/CatagiProofs.md"
HTML_DOC="$DOCS_DIR/CatagiProofs.html"
PDF_DOC="$DOCS_DIR/CatagiProofs.pdf"

mkdir -p "$MODULE_DOCS_DIR"

lake build
lake exe mdgen CatagiProofs "$MODULE_DOCS_DIR"

{
  printf '# Categories for AGI -- Lean 4 Formalization\n\n'
  printf 'Complete proofs with Mathlib\n\n'
  printf -- '---\n\n'

  while IFS= read -r import_line; do
    module_name="${import_line#import CatagiProofs.}"
    cat "$MODULE_DOCS_DIR/$module_name.md"
    printf '\n\n'
  done < <(grep '^import CatagiProofs\.' CatagiProofs.lean)
} > "$COMBINED_DOC"

pandoc "$COMBINED_DOC" \
  --standalone \
  --toc \
  --toc-depth=2 \
  --metadata title="Categories for AGI -- Lean 4 Formalization" \
  -o "$HTML_DOC"

pandoc "$COMBINED_DOC" \
  --standalone \
  --toc \
  --toc-depth=2 \
  --pdf-engine=xelatex \
  -V mainfont="Arial Unicode MS" \
  -V monofont="Arial Unicode MS" \
  -V mathfont="STIX Two Math" \
  --metadata title="Categories for AGI -- Lean 4 Formalization" \
  -o "$PDF_DOC"
