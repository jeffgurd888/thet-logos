# Rung 7 — the Boost Window, DISCHARGED (2026-10-17)

**Verdict: `BoostInvariance_window` is PROVED (T1) — the whole window, not a
narrowing.** The oldest priced window in the program (priced 2026-10-11 in
`MassShellMeasure.lean`) is closed. Parent-verified firsthand: build green
(3,463 jobs), all six headline axiom checks exactly
`[propext, Classical.choice, Quot.sound]`, zero `sorry`/`admit` in code (the
word occurs only in header prose, disclosed in the module).

**Module:** `lean/ThetLogos/MassShellBoost.lean` — 1,629 lines,
**86 theorem/lemma declarations + 15 definitions** (count reconciled
firsthand: 80 line-initial + 6 attribute-prefixed declarations).

## What the price was

`MassShellMeasure.lean` (Rung 7, Prong 4) proved the restricted Lorentz
group, shell preservation, the integral formula for d³p/2E_p, and invariance
under spatial rotations — and priced the entire remaining gap for full
restricted-Lorentz invariance as one 1D Jacobian identity for the x¹-boost:
for φ(u₁) = γu₁ − βγ√(m² + u₁² + u₂² + u₃²), show |φ′(u₁)| = E′/E so the 1D
change of variables cancels the density 1/(2E). A second step — generation
of the full group by boosts and rotations — was flagged at flag-time as the
likely cap on the discharge.

## What stands

1. **Concrete boost** (`boostLin`, `boostLorentz`, `boostRestricted`): the
   x¹-boost as an explicit linear equivalence, proved to preserve the
   Minkowski form, proper (det = 1, by light-cone conjugation), and
   orthochronous — a member of `RestrictedLorentz`. The corpus's first
   concrete boost element.
2. **Param compatibility** (`boostLin_shellParam`,
   `shellEnergy_boostParamMap`): the boost intertwines the shell
   parametrization, with the boosted-energy identity E′ = γ(E_u − βu₁)
   (positivity of E_u − βu₁ proved).
3. **The Jacobian core** (`boostSlice_jacobian`, `boostSlice_abs_deriv`):
   φ has derivative γ − βγu₁/E everywhere, is strictly monotone and
   surjective ℝ → ℝ, and |φ′(u₁)| = E_{φ(u₁)}/E_u exactly as priced.
4. **Measure discharge** (`boost_preserves_massShellMeasure`): the boost's
   shell action is `MeasurePreserving` for `massShellMeasure`, assembled
   from the mass-shell integral formula, the slice identity via Mathlib's
   `lintegral_image_eq_lintegral_abs_deriv_mul`, and Tonelli over the
   transverse plane. The density cancellation (E′/E)·(2E′)⁻¹ = (2E)⁻¹ is a
   named lemma (`ennreal_jacobian_cancel`).
5. **The cap** (`boostInvariance_window_proved : BoostInvariance_window m hm`,
   for **every** Λ : RestrictedLorentz): every restricted Lorentz
   transformation factors as (spatial lift)⁻¹ ∘ (x¹-boost) ∘ (spatial lift)
   — the spatial factor built from a Householder reflection sending the
   spatial part of Λe₀ to e₁, with the block lemma
   `lorentz_fixing_timeVec_is_spatialLift` identifying time-fixing Lorentz
   maps as spatial lifts. Each factor preserves the measure; hence all do.

No `maxHeartbeats` overrides were needed anywhere in the module (one
heartbeat fight was fixed structurally — pinned measure-type annotations —
not by raising limits).

## Honesty scope

This is invariance of the **free one-particle** mass-shell measure under the
full restricted Lorentz group — the last scope word on the Lorentz side of
the free one-particle representation begun at Rung 7. It is not an
interacting theory, not a continuum limit, not a mass gap; parts of any
official Clay statement closed remain **0**. Rung 7's other priced items
are untouched by this discharge: **strong continuity** of the one-particle
representation and **Fock packaging** remain priced, separately.

## Program total

1,965 (through Pitch 3) + 86 = **2,051 declarations**.
