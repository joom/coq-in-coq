#!/usr/bin/env bash
# Reproduce the stock-extraction experiment reported in the paper.
#
# Each ex_<name>.v is an idiomatic-CIC port of examples/<name>.v: real
# Inductive declarations, and genuine Fixpoint/match definitions (including
# large eliminations such as El : U -> Set) where the bare-PTS example had to
# axiomatize the inductive kit.  Compiling a port runs Rocq's stock OCaml
# extraction into ex_<name>.ml; we then count unsafe casts (Obj.magic) and
# unsafe interface types (Obj.t) in each result.
#
# Finally, driver.ml is a well-typed OCaml client of ex_fin.ml that calls the
# bounds-checked lookup out of bounds (the length index was erased, so OCaml
# cannot reject the call) and segfaults.
#
# Usage: ./run.sh          (requires rocq >= 9.0 and ocamlopt)
set -uo pipefail
cd "$(dirname "$0")"

echo "== extracting all ports =="
for f in ex_*.v; do
  if rocq compile -w -extraction-default-directory "$f" >/dev/null 2>&1; then
    echo "OK   $f"
  else
    echo "FAIL $f"
  fi
done

echo
echo "== Obj.magic casts inserted per extracted module =="
for f in ex_*.ml; do
  echo "$f: $(grep -c 'Obj\.magic' "$f")"
done

echo
echo "== Obj.t (aliased __) exposed in extracted interfaces =="
echo "   (lines mentioning __ in each .mli, other than the alias declaration"
echo "    itself; __ as a bare erased-proof constant is harmless, __ as a"
echo "    constructor field or in a function type is an untyped interface)"
for f in ex_*.mli; do
  hits=$(grep -n '__' "$f" | grep -v '^\([0-9]*\):type __ = Obj\.t$' || true)
  if [ -n "$hits" ]; then
    echo "--- $f"
    echo "$hits"
  fi
done

echo
echo "== segfault demo: well-typed OCaml client, out-of-bounds nth =="
ocamlopt ex_fin.mli ex_fin.ml driver.ml -o driver
./driver
status=$?
echo "driver exit status: $status  (139 = SIGSEGV)"
