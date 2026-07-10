#!/usr/bin/env bash
# Verify the mechanization's axiom footprint.
#
# Builds theories/Extraction/Assumptions.v (which runs `Print Assumptions` on
# every headline theorem) and fails if any axiom other than the expected ones
# appears.  Expected axioms:
#   - Eqdep.Eq_rect_eq.eq_rect_eq   (from dependent case analysis)
# The REPL name-recovery lemmas (not audited here) additionally use the standard
# primitive string/integer axioms; the core metatheory audited here does not.
#
# Usage:  ./check-assumptions.sh
# Exit 0 = clean; exit 1 = an unexpected axiom (or an admitted goal) was found.
set -euo pipefail
cd "$(dirname "$0")"

# Force a fresh compile so Print Assumptions output is emitted (not cached).
rm -f _build/default/theories/Extraction/Assumptions.vo
touch theories/Extraction/Assumptions.v

log=$(mktemp)
dune build theories/Extraction/Assumptions.vo >"$log" 2>&1 || { cat "$log"; exit 1; }

# Any "Print Assumptions" line naming an axiom other than eq_rect_eq is a
# regression.  We whitelist the eq_rect_eq lines and the boilerplate, then flag
# anything left that looks like an axiom declaration ("name : ...").
unexpected=$(grep -E "^[A-Za-z_][A-Za-z0-9_.']* :" "$log" \
  | grep -v "Eqdep.Eq_rect_eq.eq_rect_eq" || true)

# Also fail on any stray admitted-goal marker in the sources.
admits=$(grep -rn "Admitted" theories/ || true)

if [ -n "$unexpected" ] || [ -n "$admits" ]; then
  echo "FAIL: unexpected assumptions or admits found."
  [ -n "$unexpected" ] && { echo "--- unexpected axioms ---"; echo "$unexpected"; }
  [ -n "$admits" ] && { echo "--- Admitted goals ---"; echo "$admits"; }
  rm -f "$log"
  exit 1
fi

echo "OK: development is admit-free; only Eqdep.Eq_rect_eq.eq_rect_eq appears."
grep -c "Closed under the global context" "$log" | xargs echo "  fully axiom-free theorems:"
rm -f "$log"
