# SHELF-1d LANDING DOSSIER — 2026-11-01

**Item:** SHELF-1d (semigroup convergence: Trotter–Kato), per the
SHELF rotation and the coordinator pack (`pack-shelf-1d.md`).
With this landing the SHELF-1 line's registered seats are all
worked: 1a PARTIAL, 1b FULL, 1c PARTIAL, 1d PARTIAL (this).

**Status: PARTIAL at the pre-named general Trotter–Kato seam;
FULL at both bounded seats.**

**Artifact:** `lean/ThetLogos/SemigroupConvergence.lean` —
strict 17, defs 1. Verified by the coordinator in the main tree
(build green, 2723 jobs); all 10 headlines on exactly
`[propext, Classical.choice, Quot.sound]`.

## What landed

- **Lie–Trotter at the bounded commuting seat (FULL, stated
  honestly):** with `Commute A B` stated exactly, the product
  formula collapses to the exact finite identity
  `(trotterFactor A B s)^n = exp((n • s) • (A + B))`
  (`trotter_pow_exact`); at step t/n the approximants are constant
  in n ≥ 1 and equal `expSemigroup (A + B)` at t
  (`lie_trotter_commuting`, `lie_trotter_tendsto`). Landed as the
  exact identity it is — no limit machinery dressed around a
  collapse. Read-back: sum-of-generators splitting through
  SHELF-1a's `expSemigroup`; SHELF-6's bounded operators inherit
  it by instantiation.
- **Trotter–Kato at the bounded seat (FULL, norm form):**
  operator-norm generator convergence implies resolvent
  operator-norm convergence at rate `C²·‖Aseq n − A‖`
  (`tk_resolvent_opNorm_le`, `tk_resolvent_tendsto`, pure algebra
  from SHELF-1a's `ResolventSpec`) and semigroup operator-norm
  convergence uniformly on compact intervals
  (`tk_semigroup_uniform_on_Icc`), via a new algebra-level
  Duhamel estimate with NO commutation between the exponents:
  `‖exp X − exp Y‖ ≤ Real.exp (max ‖X‖ ‖Y‖) · ‖X − Y‖`
  (`exp_sub_exp_norm_le`).

## The seam (PARTIAL, named exactly)

General Trotter–Kato — STRONG resolvent convergence of unbounded
generators ⟹ STRONG semigroup convergence — is NOT proved. The
missing steps are named: the pin owns no Chernoff approximation
theorem, no Post–Widder formula, and no Laplace/resolvent-integral
formula (the last is SHELF-1a's named remainder, still open).
Noncommuting Lie–Trotter is likewise not landed (it needs the
same Chernoff second-order estimate; SHELF-1b's `duhamel_estimate`
assumes commutation). Also noted on the face: no unbounded seat
consumes the norm form yet (Yosida approximants converge only
strongly on the domain).

Pin quirk recorded by the builder (verified by minimal repro):
in v4.35.0-rc3 a one-step `calc` followed by further tactics in an
enclosing block fails to parse; multi-step calcs are fine. This
explains the corpus's uniform multi-step-calc style.

## Fences

NO CLAIM — no Millennium problem is claimed solved or advanced.
Dials 0/4.

**Census after landing: 10,887 strict / 10,993 total / 368 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
