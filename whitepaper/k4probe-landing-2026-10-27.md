# κ₄ Probe — Both Uncovered Seats Clean: No Negative Direction at Order β⁴

*Landing dossier, 2026-10-27. Module:
`lean/ThetLogos/PlaneCrossingKappa4Probe.lean`
(strict 51, defs 22; zero placeholders, zero
`native_decide`; main-tree build green, 3,117 jobs,
parent-verified; headline axiom sets exactly
`[propext, Classical.choice, Quot.sound]`). **Parts of
the Clay Yang–Mills statement closed by this landing:
0.** The β2 core's pre-registered refutation probe
has run: at the two seats never before probed, the
β⁴ dependent coefficient κ₄^dep has **no negative
eigenvalue**. β2 (𝒜 ⪰ 0 at general (G, ρ)) is
therefore NOT refuted at order β⁴ — and, with equal
emphasis, not one inch proved.*

## The seats and the verdicts

- **(C₃, faithful complex character, d = 1), N = 2 —
  PASS.** The plaquette factor is identified in Lean
  end-to-end (`FC3_eq`): of the 16 sign patterns only
  two survive the stratum integral. The class kernel
  is Φ₁ = (3/16)I − (1/16)J, spectrum {0, 3/16, 3/16}
  — PSD, rank **two** (positive in both nontrivial
  character directions, where the S₃ seat's face block
  was rank one), zero exactly on constants; the form
  is (729/16)·Σ(φₐ−φ_b)² ≥ 0, machine-checked
  (`FC3_form_nonneg`). The pair block
  Ψ₁ = (5/64)(3I − J) is likewise PSD with margins
  exactly zero.
- **(S₃, std), N = 2, same-site-pair extras included —
  PASS.** The face block recomputes to SBP-1's
  Φ₂ = w wᵀ, w = (1/8, 0, −1/16) — a perfect square,
  rank one, character evaluation diag(0, 0, 6561).
  The extras (the pair block Ψ₂) are the surprise in
  the other direction: in the character basis their
  evaluation is diag(0, 81/4, 405/16) — **positive in
  both nontrivial directions**, including the sign
  direction the face block annihilates; the form is
  an explicit sum of two squares
  (`formS3_pair_nonneg`), margins exactly zero.

## Correction on the record

The probe's first-pass pair assembly was WRONG —
raw monomial expectations, and an intermediate
slot-partition cumulant, both misidentify the
dependent part; the error was caught by the
zero-margin check (the wrong assembly shows margin
−9/4 at C₃ and spurious negative directions). The
house's dep is the cumulant over partitions of the
distinct-column support; with the corrected assembly
the margins are exactly zero at both seats, asserted
in the computation and, at S₃, proved in Lean
(`PsiS3_margins`). Both artifacts are recorded in
the verdict memo
(`routeb-general-scratch/verdict-memo-k4probe.md`)
so no future reader inherits them.

## The fence

Two seats probed clean **on the named observable
space** — the module's fence: any negative direction
of the full κ₄^dep at these seats, if one exists,
lives on observables outside that space (the same
fence as SBP-1). K-K4 did not fire; nothing here
proves κ₄^dep's sign at general (G, ρ), and the
zero-margin pattern stands unrelieved: at both seats
the constants direction is exactly flat. The pass
clears exactly one thing — the general-(G, ρ) κ₄^dep
closed-form + sign brick (M) priced in the core
scoping. NO CLAIM; dials 0/4.

## Census effect

Strict 6,692 → **6,743**; attribute-inclusive 6,770 →
**6,821**; modules 230 → **231**; placeholders unchanged
at **7**.

## Backers since last landing

No new backers inscribed in this interval; the roll stands
as recorded in `BACKERS.md`. Every gift is published with
the proof stream, named as the giver wishes, amounts only
with the giver's permission — the standing reciprocity of
this house.
