# Track 1 Closure (Route A) — dossier (landed 2026-10-23)

**Module:** `lean/ThetLogos/Track1Closure.lean` (625 lines as built;
38 strict theorem/lemma declarations, 38 attribute-inclusive,
3 defs, 0 sorry/admit).
**Charter:** `whitepaper/track1-closure-scoping-2026-10-23.md`.
**Commission:** Jeff, 2026-10-23 00:45 EDT ("let's finish the
Standard model") — the attack on the loud-statement trigger fixed
the same night (Track 1 closes ⟺ one representation carries
faithfulness + hypercharge ratios + the spectral-triple
compatibilities together at T1).
**Parent verification:** in-tree targeted build exit 0 on the
candidate and again on the shipped text; parent recount
(38/38/3/0) matches the builder's; `#print axioms` on the
headlines — exactly `[propext, Classical.choice, Quot.sound]`.

## Verdict: T1 STANDS; T2 KILLED; T3 KILLED — Track 1 does NOT close via Route A

- **T1 — STANDS (T1).** π₀'s own opposite `rho0 := piOp ∘ pi0` is
  constructed from the landed real structure and its laws proved:
  `rho0_eq_J_conj` (the J-form identification), `rho0_afMul`
  (opposite-product law), `rho0_one`, `rho0_zero`, `rho0_afStar`
  (star-compatibility), `rho0_grading_even`. Species stated
  exactly: multiplicative, opposite-order; no additivity claimed
  (proved incompatible with the hypercharge seat, landed).
- **T2 — KILLED (T1).** Order-zero for the pair (π₀, ρ°) fails on
  explicit witnesses, entries recomputed against ρ° directly:
  `(pi0 a₀ * rho0 b₀)(0,1) = I` vs `(rho0 b₀ * pi0 a₀)(0,1) = −I`
  (`order_zero_killed`, `order_zero_fails_universal`). Mechanism:
  π₀'s ℍ acts on the lepton doublet while ρ° seats the ℂ-dressed
  conjugate `λ̄ • q̄ᴴ` on the same slots, and the two do not
  commute.
- **T3 — KILLED (T1), with an exact identity.** First-order for
  the pair against the landed finite Dirac `DF_oneGen` fails by
  formula, not by witness alone: for all real Yukawas,
  `[[DF_oneGen, pi0 a₀], rho0 b₀](0,9) = −(1 + I)·(ye : ℂ)`
  (`DF_first_order_entry_09`; `first_order_killed` at ye = 1).
  The defect is proportional to the electron Yukawa: it vanishes
  only where the interaction does.
- **T4 — assembled; does NOT stand whole.** `track1_package_routeA`
  conjoins T1 + grading + J-identification + J-compatibility
  (`DF_oneGen_J_compat` stands) **and both kills**;
  `track1_not_closed_routeA` proves the closure conjunction
  false. **Per K-TC3, the loud statement does not fire.**

## A correction to the charter, on the record

The charter framed the landed `pi0_order_zero_fails` as a test
against "Option A's `piOp`, a different construction's opposite,"
and commissioned ρ° as an untested pairing. That premise was
wrong, and this module proves it: `piOp` is a matrix-level
combinator (`UJ * Mᵀ * UJ`), not built from π, and by
`conjTranspose_map_star` it is verbatim the J-conjugate action —
so the landed §7 test was already the own-opposite test.
The correction is recorded here and on the module's face, at the
same rank as the verdicts: the scoping error was the parent's,
the proof that it was an error is T1, and both kills were
recomputed against ρ° itself rather than inherited.

## What Track 1's remaining content now is

Restated from the kills' shape: no multiplicative-species
representation carrying the hypercharge seat pairs with its
canonical J-opposite through order-zero and first-order on this
finite space. Closure, if it exists, is **Route B** — a different
seat assignment, a modified opposite construction, or an enlarged
finite space — to be scoped from these counterexamples under a
new charter (Route B is priced in the closure charter, NOT
commissioned). SM-Match Track 1 remains **PARTIAL**, its standing
content now: faithfulness and the hypercharge seat discharged
(PreOptionA), additivity proved incompatible, and the
order-zero/first-order pairing killed for the canonical opposite.

## Fences held

K-TC1 (finite only; `DF_oneGen` is the landed finite Dirac; no
manifold factor, no continuum), K-TC2 (inputs untouched —
hypercharge table still T2-cited; triplication/masses/couplings
unmoved), K-TC3 (loud statement does not fire), K-TC4 (landed
files unmodified; landed verdicts cited). One numerical
observation from the build's scratch work is labeled NOT a theorem
wherever it appears: the same witnesses give the same (0,9) entry
for `smDirac` with a Majorana block — the Lean kill is stated for
`DF_oneGen` only.

## Census

Program: **3,807 strict / 3,856 attribute-inclusive, 135 counted
modules** (was 3,769 / 3,818 / 134).
