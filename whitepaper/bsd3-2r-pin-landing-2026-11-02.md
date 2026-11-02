# BSD3-2R — PIN LANDING (2026-11-02)

**Brick:** BSD3-2R pin (NEW ENTRY under the relabeling rule).
**Decision of record:** Jeff, 2026-11-01 22:33 EST — "1 re-pin."
**Module:** `ThetLogos/BSDRefinedE3Repin.lean` (new file; the dead
`ThetLogos/BSDRefinedE3Pin.lean` is UNEDITED).
**Count:** strict 0 / defs 3.
**Build:** `lake build ThetLogos.BSDRefinedE3Repin` GREEN on build 1.
**Axioms:** defs-only pin; no theorems, no `#print axioms` surface.

## What the pin carries

Three defs, frozen:

1. `NagellLutzCriterionE3R` — the CORRECTED Nagell–Lutz seam for
   E3 = LMFDB 11.a1 (`y² + y = x³ − x² − 10x − 20`, Weierstrass
   coefficients ⟨0, −1, 1, −10, −20⟩, Δ = −11⁵, |Δ| = 161051): the
   divisibility quantity is the general form (2y + a₁x + a₃)² ∣ Δ,
   which for E3 (a₁ = 0, a₃ = 1) is (2y + 1)², with the 2y + 1 = 0
   disjunct as the exact 2-torsion case:

   `∀ x y : ℚ, E3.IsOn x y → E3.toAffine.IsTorsion x y → ∃ xi yi : ℤ,
   x = xi ∧ y = yi ∧ (2 * yi + 1 = 0 ∨ (2 * yi + 1) ^ 2 ∣ 161051)`

2. `E3TorsionCardSeam : Prop := Nat.card
   (AddCommGroup.torsion E3.toAffine.Point) = 5` — |tors| = 5 enters
   ONLY as this named hypothesis. It is NOT carried as a T4 value;
   the value 5 is to be derived by the sweep brick, conditional on
   `NagellLutzCriterionE3R`.

3. `BSDRefinedE3R` — the rank-0 refined (B1) statement over the
   corrected seam, reusing `E3RankZeroSeam`, `E3ShaFiniteSeam`,
   `E3LValue`, `E3PeriodValue`, `E3TamagawaValue` unchanged from the
   dead pin's module; the regulator slot is the literal `1` and the
   torsion slot the literal `5` (which enters the conclusion only
   through the card-seam hypothesis); conclusion
   `|Lval − refinedRHS sha ΩE3 1 tam 5| ≤ 5e-3 ∧ sha = 1`. Sha is
   quantified, not named: the identification sha = 1 is the
   statement's conclusion to be proved at assembly grade (B1's
   licence is existence + the analytic side only).

## Why the old seam died (cited on the pin's face)

K-BSD3-2c (dossier `whitepaper/bsd3-2-kill-2026-11-02.md`): the old
pin's frozen `NagellLutzCriterionE3` (yi = 0 ∨ yi² ∣ 161051) is FALSE
for E3. Witness (5, 5), exact order 5: (2y + 1)² at the four nonzero
torsion points is 121 or 14641, both dividing 161051; the y-squares
25, 36, 3600, 3721 divide nothing. The old criterion is the a₃ = 0
special case; E3 has a₃ = 1. The E1/E2 instances of the old form
stand untouched (verified true for their curves).

## Kills registered on the pin

- **K-BSD3-2R-a** — reading sha = 1, the BSD formula, or any
  rank-0 BSD content for 11.a1 out of this pin: the pin seats the
  corrected statement only; nothing is proved until the sweep and
  assembly bricks land.
- **K-BSD3-2R-b** — any other Nagell–Lutz form for E3 in this line,
  or any edit reviving the dead pin: the (2y + 1) form is the unique
  licensed correction; the old pin stays dead in the record.
- **K-BSD3-2R-c** — armed on the sweep brick: if discharging
  `E3TorsionCardSeam` from `NagellLutzCriterionE3R` needs a stronger
  form than the corrected criterion, the brick STOPS and reports;
  no in-flight strengthening.
- **K-BSD3-2R-d** — the 5e-3 tolerance and the imported L-value /
  period windows stay as registered here and in the dead pin's
  record; no landing may silently tighten or loosen them.

## Verdict

**LANDED (pin).** The corrected E3 statement exists in the tree with
its kills armed. The sweep brick (discharge of the card seam from
the corrected criterion) and the assembly brick (B1 assembly over
the new seam) follow as separate bricks.

**NO CLAIM. Parts of the Clay BSD statement closed by this landing:
0. Dials 0/4.**

**Census after landing: 12,592 strict / 13,090 total / 440 counted
modules** (increment +0 strict / +3 defs / +1 module over the
12,592 / 13,087 / 439 close at CLS-2G; whole-tree raw count differs
by the documented non-chain remainder — see
`whitepaper/double-check-sweep-2026-10-18.md`).
