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
# Exit 0 = clean; exit 1 = an unexpected axiom or proof-hole command was found.
set -euo pipefail
cd "$(dirname "$0")"

log=$(mktemp)
audit_tmp=""
cleanup() {
  rm -f "$log"
  [ -z "$audit_tmp" ] || rm -rf "$audit_tmp"
}
trap cleanup EXIT

# Under `dune test`, dependencies are already present in the sandbox and a
# nested Dune invocation would deadlock. Outside a sandbox, first ask Dune to
# build the query and its dependencies. In both cases, compile a temporary copy
# directly so Print Assumptions output is fresh without touching source files or
# deleting build artifacts.
if [ "${BLAME_AUDIT_DIRECT:-0}" = 1 ]; then
  theory_root=theories
else
  dune build theories/Extraction/Assumptions.vo >"$log" 2>&1 \
    || { cat "$log"; exit 1; }
  theory_root=_build/default/theories
fi

audit_tmp=$(mktemp -d)
cp theories/Extraction/Assumptions.v "$audit_tmp/AssumptionsAudit.v"
rocq compile \
  -Q "$theory_root/CoC" CoC \
  -Q "$theory_root/BlameFOmega" BlameFOmega \
  -Q "$theory_root/Extraction" Extraction \
  "$audit_tmp/AssumptionsAudit.v" >"$log" 2>&1 \
  || { cat "$log"; exit 1; }

# Any "Print Assumptions" line naming an axiom other than eq_rect_eq is a
# regression.  We whitelist the eq_rect_eq lines and the boilerplate, then flag
# anything left that looks like an axiom declaration ("name : ...").
unexpected=$(grep -E "^[A-Za-z_][A-Za-z0-9_.']* :" "$log" \
  | grep -v '^Eqdep\.Eq_rect_eq\.eq_rect_eq :' || true)

# Reject proof-hole commands and new axiom-like declarations anywhere in the
# mechanized theories. A leading Rocq attribute is allowed before declarations.
proof_holes=$(rg -n -i --glob '*.v' \
  '(^|[[:space:]])(admit|admitted|abort)[[:space:]]*\.' theories || true)
axiom_declarations=$(rg -n --glob '*.v' \
  '^\s*(#\[[^]]+\]\s*)*((Local|Global)\s+)?(Axiom|Axioms|Parameter|Parameters|Conjecture|Conjectures)\s+[A-Za-z_]' \
  theories || true)

if [ -n "$unexpected" ] || [ -n "$proof_holes" ] || [ -n "$axiom_declarations" ]; then
  echo "FAIL: unexpected assumptions, proof holes, or axiom declarations found."
  [ -n "$unexpected" ] && { echo "--- unexpected axioms ---"; echo "$unexpected"; }
  [ -n "$proof_holes" ] && { echo "--- proof-hole commands ---"; echo "$proof_holes"; }
  [ -n "$axiom_declarations" ] && { echo "--- axiom declarations ---"; echo "$axiom_declarations"; }
  exit 1
fi

echo "OK: audited theorems use only Eqdep.Eq_rect_eq.eq_rect_eq; source hygiene is clean."
closed_count=$(grep -c "Closed under the global context" "$log" || true)
echo "  fully axiom-free theorems: $closed_count"
