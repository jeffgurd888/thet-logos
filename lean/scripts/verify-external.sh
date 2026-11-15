#!/usr/bin/env bash
# verify-external.sh — one-command EXTERNAL verification kit for the
# thet-logos corpus (ACMD). Written for an outside checker who has
# cloned this repository and trusts nothing in it, including this
# script's expectations.
#
# WHAT IT CHECKS (each line of the verdict sheet is PASS, FAIL, or
# MANUAL — never anything softer):
#   1. Toolchain: the Lean version that actually runs here vs the
#      repo's own pin (lean/lean-toolchain).
#   2. Builds: a targeted build of every module named in the axiom-
#      fence registry (lean/scripts/axiom-fence.txt), then the root
#      build. Both must exit 0.
#   3. Zero-sorry scan: the repo's own gate (scripts/check_no_sorry.py)
#      over every Lean source file; observed file count vs the count
#      published in the README.
#   4. Census recount by the HOUSE METHOD OF RECORD (below); observed
#      recount vs the recount published in the README.
#   5. Ledger size: the number of record files under
#      epistemic-ledger/records/ vs the count published in the README.
#   6. Headline axiom audit: a sample of headline declarations read
#      from the fence registry at runtime (the FIRST and LAST registry
#      groups — the seed landmarks and the newest shipment's
#      capstone), checked with `#print axioms`; each must depend on
#      no axioms outside {propext, Classical.choice, Quot.sound}.
#   7. (OPTIONAL, --fence) the full axiom fence: every registered
#      headline (1220 at the time this script was written — the count
#      is read from the registry at runtime, not assumed), via the
#      repo's own runner (scripts/run_axiom_fence.py). Costs roughly
#      15–20 minutes and ~36 GB of artifact I/O. OFF by default.
#
# HONESTY RULES (the point of the kit):
#   * Every "published" figure is READ AT RUNTIME from the repo's own
#     public record (the README's current-state block). Nothing a
#     check compares against is hardcoded here. If a figure cannot be
#     extracted from the README, or cannot be observed mechanically,
#     the sheet prints MANUAL ("compare manually") instead of faking
#     a check.
#   * The chain census (a cumulative sum over the integration chain)
#     and the module count are NOT mechanically derivable from a
#     clone's file tree; the sheet prints the published values for
#     manual comparison and says so.
#   * Exit code is 0 iff no mechanical check FAILED. MANUAL lines do
#     not fail the run; they mark the edge of what a script can see.
#
# THE HOUSE METHOD OF RECORD (census recount), replicated exactly:
#   * File set: every *.lean file under lean/ThetLogos/. (579 files
#     when this script was written; the count is observed, not
#     assumed. The library root file lean/ThetLogos.lean is import
#     lines only — it carries no declarations and sits outside the
#     counted set, as it does in the house gates.)
#   * Each file is comment/string-stripped with the repo's own
#     stripper — this script IMPORTS strip_noncode from
#     scripts/check_no_sorry.py rather than reimplementing it, so the
#     stripping cannot drift from the house gate.
#   * Count lines whose stripped text matches ^(theorem|lemma) at
#     column 0. (Attribute-prefixed declarations such as
#     `@[simp] theorem ...` on one line are NOT counted by this
#     method; 21 of them are part of the located chain/recount gap
#     disclosed in the README.)
#   * Subtract the FROZEN PRE-LEDGER REMAINDER, 669. This constant is
#     part of the METHOD (frozen at the 2026-11-03 census
#     restatement, ledger record census-restatement-2026-11-03, and
#     re-validated at every integration since); it is not a measured
#     figure and it is not read from the README. The comparison
#     target — the published recount — IS read from the README.
#
# USAGE:
#   scripts/verify-external.sh [--fence] [--root DIR]
# Run it from anywhere; it locates the repo root relative to itself
# unless --root names another checkout (e.g. a second clone you want
# this copy of the script to audit).
#
# REQUIREMENTS: bash, python3, git (optional, for the HEAD line), and
# the Lean toolchain manager (elan) on PATH — the script prepends
# ~/.elan/bin itself, since non-login shells often lack it.

set -u
export PATH="$HOME/.elan/bin:$PATH"

FENCE=0
ROOT=""
while [ $# -gt 0 ]; do
  case "$1" in
    --fence) FENCE=1; shift ;;
    --root) ROOT="$2"; shift 2 ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
done

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
if [ -z "$ROOT" ]; then
  ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
fi
LEAN_DIR="$ROOT/lean"
README="$ROOT/README.md"
REGISTRY="$LEAN_DIR/scripts/axiom-fence.txt"

FAILURES=0
declare -a SHEET
note() { SHEET+=("$1"); }
fail() { FAILURES=$((FAILURES + 1)); }

echo "== thet-logos external verification =="
echo "repo root: $ROOT"
if git -C "$ROOT" rev-parse --short HEAD >/dev/null 2>&1; then
  echo "HEAD: $(git -C "$ROOT" rev-parse HEAD)"
fi
echo

# ---------- published figures, read from the README at runtime ----
# The README's current-state block carries the published numbers in
# fixed prose shapes. If a shape is not found, the figure degrades
# to MANUAL — the script never invents a target.
pub() { # pub <grep-pattern> -> first number in the first match, or empty
  grep -oE "$1" "$README" 2>/dev/null | head -1 | \
    grep -oE '[0-9][0-9,]*' | head -1 | tr -d ','
}
PUB_CHAIN=$(pub 'Census [0-9,]+ theorem declarations')
PUB_MODULES=$(grep -oE 'theorem declarations / [0-9,]+ modules' "$README" 2>/dev/null | head -1 | grep -oE '[0-9,]+' | tail -1 | tr -d ',')
PUB_RECOUNT=$(grep -oE 'declaration-true recount [0-9,]+' "$README" 2>/dev/null | head -1 | grep -oE '[0-9,]+' | tail -1 | tr -d ',')
PUB_FILES=$(grep -oE 'Zero sorrys across [0-9,]+ files' "$README" 2>/dev/null | head -1 | grep -oE '[0-9,]+' | tail -1 | tr -d ',')
PUB_FENCE=$(grep -oE 'Axiom fence [0-9,]+ / [0-9,]+' "$README" 2>/dev/null | head -1 | grep -oE '[0-9,]+' | head -1 | tr -d ',')
PUB_LEDGER=$(grep -oE 'Epistemic ledger: [0-9,]+ records' "$README" 2>/dev/null | head -1 | grep -oE '[0-9,]+' | tail -1 | tr -d ',')

# ---------- 1. toolchain -------------------------------------------
PIN=$(cat "$LEAN_DIR/lean-toolchain" 2>/dev/null | tr -d '[:space:]')
PIN_VER="${PIN##*:}"        # e.g. v4.35.0-rc3
PIN_NUM="${PIN_VER#v}"      # e.g. 4.35.0-rc3 (lean --version prints no leading v)
OBS_VER=""
if command -v lake >/dev/null 2>&1; then
  OBS_VER=$(cd "$LEAN_DIR" && lake env lean --version 2>/dev/null | grep -oE '[0-9]+\.[0-9]+\.[0-9]+(-[A-Za-z0-9.]+)?' | head -1)
fi
if [ -n "$OBS_VER" ] && [ "$OBS_VER" = "$PIN_NUM" ]; then
  note "PASS  toolchain            observed $OBS_VER = pinned $PIN_VER (lean/lean-toolchain)"
elif [ -n "$OBS_VER" ]; then
  note "FAIL  toolchain            observed $OBS_VER, pinned $PIN_VER — results below are not about the pinned corpus"
  fail
else
  note "MANUAL toolchain           could not run Lean (pin: $PIN); is elan installed?"
  fail
fi

# ---------- 2. dependency cache + builds ----------------------------
echo "-- lake exe cache get (dependency oleans; a fresh tree unpacks"
echo "   the pinned Mathlib cache here — a build before this step"
echo "   would silently become a from-source Mathlib build)"
(cd "$LEAN_DIR" && lake exe cache get) >/tmp/verify-external-cache.log 2>&1
if [ $? -eq 0 ]; then
  note "PASS  cache get            pinned dependency cache obtained (log: /tmp/verify-external-cache.log)"
else
  note "FAIL  cache get            see /tmp/verify-external-cache.log — without the cache the builds below are not the pinned check"
  fail
fi

# Targeted build: every module the fence registry imports.
mapfile -t REG_MODULES < <(grep -E '^import ' "$REGISTRY" | awk '{print $2}' | sort -u)
echo "-- targeted build: ${#REG_MODULES[@]} registry modules"
(cd "$LEAN_DIR" && lake build "${REG_MODULES[@]}") >/tmp/verify-external-build-targeted.log 2>&1
if [ $? -eq 0 ]; then
  note "PASS  targeted build       ${#REG_MODULES[@]} registry modules built (log: /tmp/verify-external-build-targeted.log)"
else
  note "FAIL  targeted build       see /tmp/verify-external-build-targeted.log"
  fail
fi

echo "-- root build"
(cd "$LEAN_DIR" && lake build) >/tmp/verify-external-build-root.log 2>&1
if [ $? -eq 0 ]; then
  note "PASS  root build           library root builds clean (log: /tmp/verify-external-build-root.log)"
else
  note "FAIL  root build           see /tmp/verify-external-build-root.log"
  fail
fi

# ---------- 3. zero-sorry scan (the repo's own gate) ----------------
SORRY_OUT=$(cd "$LEAN_DIR" && python3 scripts/check_no_sorry.py ThetLogos 2>&1)
SORRY_RC=$?
OBS_FILES=$(echo "$SORRY_OUT" | grep -oE '[0-9]+ files scanned' | grep -oE '[0-9]+' | head -1)
if [ $SORRY_RC -eq 0 ]; then
  if [ -n "$PUB_FILES" ] && [ -n "$OBS_FILES" ] && [ "$OBS_FILES" = "$PUB_FILES" ]; then
    note "PASS  zero-sorry scan      no code-position sorry in $OBS_FILES files = published $PUB_FILES files"
  elif [ -n "$PUB_FILES" ]; then
    note "FAIL  zero-sorry scan      no sorry found, but file count observed ${OBS_FILES:-unknown} != published $PUB_FILES"
    fail
  else
    note "PASS  zero-sorry scan      no code-position sorry in $OBS_FILES files (published count not extractable from README)"
  fi
else
  note "FAIL  zero-sorry scan      $SORRY_OUT"
  fail
fi

# ---------- 4. census recount (house method of record) --------------
CENSUS_OUT=$(cd "$LEAN_DIR" && python3 - <<'PYEOF'
import re, sys
sys.path.insert(0, 'scripts')
from pathlib import Path
from check_no_sorry import strip_noncode
pat = re.compile(r'^(theorem|lemma)\b')
files = sorted(Path('ThetLogos').rglob('*.lean'))
total = 0
for f in files:
    code = strip_noncode(f.read_text(encoding='utf-8', errors='replace'))
    total += sum(1 for line in code.splitlines() if pat.match(line))
FROZEN_PRE_LEDGER_REMAINDER = 669  # part of the method; see header
print(f"{len(files)} {total} {total - FROZEN_PRE_LEDGER_REMAINDER}")
PYEOF
)
OBS_C_FILES=$(echo "$CENSUS_OUT" | awk '{print $1}')
OBS_C_TOTAL=$(echo "$CENSUS_OUT" | awk '{print $2}')
OBS_RECOUNT=$(echo "$CENSUS_OUT" | awk '{print $3}')
if [ -n "$PUB_RECOUNT" ] && [ -n "$OBS_RECOUNT" ]; then
  if [ "$OBS_RECOUNT" = "$PUB_RECOUNT" ]; then
    note "PASS  census recount       observed $OBS_RECOUNT (stripped col-0 total $OBS_C_TOTAL over $OBS_C_FILES files, minus frozen remainder 669) = published recount $PUB_RECOUNT"
  else
    note "FAIL  census recount       observed $OBS_RECOUNT (stripped total $OBS_C_TOTAL over $OBS_C_FILES files, minus 669) != published recount $PUB_RECOUNT"
    fail
  fi
else
  note "MANUAL census recount      observed recount ${OBS_RECOUNT:-unknown}; published recount not extractable from README — compare manually"
fi
if [ -n "$PUB_CHAIN" ]; then
  note "MANUAL chain census        published chain $PUB_CHAIN theorems / ${PUB_MODULES:-?} modules — a cumulative integration-chain sum, NOT derivable from a file tree; compare manually (the recount above is the derivable figure)"
else
  note "MANUAL chain census        published chain figure not extractable from README — compare manually"
fi

# ---------- 5. ledger size ------------------------------------------
OBS_LEDGER=$(ls "$ROOT"/epistemic-ledger/records/*.json 2>/dev/null | wc -l | tr -d ' ')
if [ -n "$PUB_LEDGER" ] && [ "$OBS_LEDGER" = "$PUB_LEDGER" ]; then
  note "PASS  ledger size          observed $OBS_LEDGER record files = published $PUB_LEDGER records"
elif [ -n "$PUB_LEDGER" ]; then
  note "FAIL  ledger size          observed $OBS_LEDGER record files != published $PUB_LEDGER records"
  fail
else
  note "MANUAL ledger size        observed $OBS_LEDGER record files; published count not extractable from README — compare manually"
fi

# ---------- 6. headline axiom audit (registry sample) ---------------
# Sample rule (mechanical, read from the registry at runtime): every
# declaration in the FIRST registry group (the seed landmarks) and
# every declaration in the LAST registry group (the newest
# shipment's capstone), with those groups' imports.
read -r -d '' HEADLINE_PY <<'PYEOF' || true
import re, subprocess, sys, tempfile
from pathlib import Path
reg = Path('scripts/axiom-fence.txt').read_text(encoding='utf-8').splitlines()
groups, cur = [], None
for raw in reg:
    line = raw.strip()
    if line.startswith('import '):
        cur = (line, []); groups.append(cur)
    elif line and not line.startswith('#') and cur is not None:
        cur[1].append(line)
sample = [groups[0]] + ([groups[-1]] if len(groups) > 1 else [])
imports = [g[0] for g in sample]
decls = [d for _, ds in sample for d in ds]
src = "\n".join(imports) + "\n\n" + "\n".join(f"#print axioms {d}" for d in decls) + "\n"
with tempfile.NamedTemporaryFile('w', suffix='.lean', dir='/tmp', delete=False) as fh:
    fh.write(src); path = fh.name
proc = subprocess.run(['lake', 'env', 'lean', path], capture_output=True, text=True)
out = proc.stdout + proc.stderr
if proc.returncode != 0:
    print("AUDIT-ERROR"); print(out[:2000]); sys.exit(0)
FENCE = {'propext', 'Classical.choice', 'Quot.sound'}
results = {}
# '#print axioms' line-wraps the axiom list for long declaration
# names ('... depends on axioms: [propext,\n Classical.choice,\n
# Quot.sound]'), so a single-line regex misses wrapped reports and
# false-fails clean declarations. Parse the way the tree's own
# fence runner (run_axiom_fence.py) does: a literal per-declaration
# search over the whole output, capturing up to the closing
# bracket across line breaks.
for d in decls:
    m = re.search(re.escape(f"'{d}' depends on axioms: [") + r"([^\]]*)\]", out)
    if m:
        results[d] = [a.strip() for a in m.group(1).split(',') if a.strip()]
    elif f"'{d}' does not depend on any axioms" in out:
        results[d] = []
bad = []
for d in decls:
    hit = results.get(d)
    if hit is None:
        bad.append(f"{d}: no #print axioms output")
    elif not set(hit) <= FENCE:
        bad.append(f"{d}: {hit}")
print(f"checked {len(decls)} declarations from {len(sample)} registry groups")
if bad:
    print("AUDIT-FAIL"); [print(b) for b in bad]
else:
    print("AUDIT-PASS")
    for d in decls:
        hit = results.get(d, [])
        print(f"{d}: [{', '.join(hit) if hit else 'no axioms'}]")
PYEOF
AUDIT_OUT=$(cd "$LEAN_DIR" && python3 -c "$HEADLINE_PY" 2>&1)
if echo "$AUDIT_OUT" | grep -q "AUDIT-PASS"; then
  note "PASS  headline axiom audit $(echo "$AUDIT_OUT" | head -1); every sampled headline on the standard three axioms or fewer (details: rerun captures in /tmp; sample = first + last fence-registry groups)"
  echo "$AUDIT_OUT" | tail -n +3 | sed 's/^/      /'
elif echo "$AUDIT_OUT" | grep -q "AUDIT-FAIL"; then
  note "FAIL  headline axiom audit $(echo "$AUDIT_OUT" | head -1)"
  echo "$AUDIT_OUT" | grep -A20 "AUDIT-FAIL" | sed 's/^/      /'
  fail
else
  note "FAIL  headline axiom audit audit itself errored: $(echo "$AUDIT_OUT" | head -2 | tr '\n' ' ')"
  fail
fi

# ---------- 7. optional full fence ----------------------------------
if [ $FENCE -eq 1 ]; then
  echo "-- full axiom fence (this is the slow one: ~15–20 min, ~36 GB I/O)"
  (cd "$LEAN_DIR" && python3 scripts/run_axiom_fence.py) >/tmp/verify-external-fence.log 2>&1
  if [ $? -eq 0 ]; then
    note "PASS  full axiom fence     every registered headline within the standard three axioms (log: /tmp/verify-external-fence.log; published figure: ${PUB_FENCE:-not extractable})"
  else
    note "FAIL  full axiom fence     see /tmp/verify-external-fence.log"
    fail
  fi
else
  note "MANUAL full axiom fence    not run (default). Published figure: ${PUB_FENCE:-not extractable} / ${PUB_FENCE:-?}. Run with --fence to check all registered headlines (~15–20 min, ~36 GB I/O)."
fi

# ---------- verdict sheet -------------------------------------------
echo
echo "================= VERDICT SHEET ================="
printf '%s\n' "${SHEET[@]}"
echo "================================================="
if [ $FAILURES -eq 0 ]; then
  echo "OVERALL: no mechanical check FAILED (MANUAL lines mark the"
  echo "edge of mechanical checking — they are invitations, not passes)."
  exit 0
else
  echo "OVERALL: $FAILURES check(s) FAILED — see logs above. A failure"
  echo "here is a finding; file it via the external-review template."
  exit 1
fi
