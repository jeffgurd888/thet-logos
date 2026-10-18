# Translations Strong Continuity — Dossier (2026-10-18)

**Verdict: STANDS.** The translation half of the Rung 7 strong-continuity
remainder is discharged at the gauntlet's price (S, discharge-ready) and by
the gauntlet's named route. **T1 throughout: 10 strict theorem declarations,
zero `sorry`/`admit`, headline axioms exactly the standard three
(`propext`, `Classical.choice`, `Quot.sound`).**

## What was owed

`MassShellMeasure.lean` closes its one-particle section with the admission
that a covariant representation also needs strong continuity of the
translation part, named there as the exact price of this item:

```lean
def StrongContinuity_window (m : ℝ) (hm : 0 < m) : Prop :=
  ∀ ψ : massShell m → ℂ, MemLp ψ 2 (massShellMeasure m hm) →
    Filter.Tendsto (fun a : Minkowski =>
      eLpNorm (fun p => oneParticleFun ⟨a, 1⟩ m hm ψ p - ψ p) 2
        (massShellMeasure m hm)) (nhds 0) (nhds 0)
```

The parked-fleet gauntlet (`whitepaper/gauntlet-parked-fleet-2026-10-17.md`,
§4a) priced this **S / DISCHARGE-READY** and named the route: the integrand
bound `|e^{ip·a} − 1|²·‖ψ(p)‖² ≤ 4‖ψ(p)‖²`, the exact DCT lemma
`tendsto_lintegral_of_dominated_convergence`, and pointwise convergence via
`Complex.continuous_exp`.

## What landed

New module **`lean/ThetLogos/TranslationContinuity.lean`** (220 lines),
following the MassShellBoost precedent — the window `Prop` stays in the old
file, the discharge lands in a new one, and the module is not added to the
root imports. Targeted build green (**3,393 jobs**), `.olean` verified,
parent-checkable by `lake build ThetLogos.TranslationContinuity`.

Headline (the cap):

```lean
theorem strongContinuity_window_proved (m : ℝ) (hm : 0 < m) :
    StrongContinuity_window m hm
```

i.e. for **every** mass `m > 0` and **every** `ψ ∈ L²` of the mass shell,
`‖U₁(a, 1)ψ − ψ‖₂ → 0` in `eLpNorm` as `a → 0` in Minkowski space — the
form the window asks for (continuity at `0`; the group law
`oneParticleFun_mul` transports it to every `a`, as in the file's own
framing).

Support theorems (all T1):

- `translation_diff` — **pointwise identity**: for `g = ⟨a, 1⟩` one has
  `g.lor⁻¹ = 1`, the shell action is therefore the identity
  (`shellActR_one`), and `U₁(a,1)ψ(p) − ψ(p) = (phase a p − 1) * ψ p`
  exactly. This is why the translation case is cheap: translations act on
  the one-particle space as pure phase multiplication.
- `aestronglyMeasurable_translation_diff` — the difference function is
  a.e. strongly measurable (from `measurable_phase` and `hψ`).
- `enorm_eq_one_of_norm_eq_one` — norm `1` ⇒ enorm `1` (bridge lemma).
- `enorm_phase_sub_one_le` — `‖phase a p − 1‖ₑ ≤ 2`, from `‖phase‖ = 1`
  (`phase_norm`) and the triangle inequality.
- `translation_integrand_le` — the gauntlet's dominator, pointwise:
  `‖(phase a p − 1) * ψ p‖ₑ ^ 2 ≤ 4 * ‖ψ p‖ₑ ^ 2` for every `a, p`.
- `aemeasurable_enorm_rpow` — the integrand is a.e. measurable.
- `lintegral_translation_bound_ne_top` — the dominator is integrable:
  `∫⁻ 4‖ψ‖ₑ² = 4 ∫⁻ ‖ψ‖ₑ² < ∞`, the finiteness read off
  `eLpNorm_eq_lintegral_rpow_enorm_toReal` (the `eLpNorm` is the square
  root of that integral) against `hψ : eLpNorm ψ 2 μ < ∞`.
- `tendsto_translation_integrand` — pointwise in `p`: `a ↦ minkowskiInner a p`
  is continuous with value `0` at `a = 0`; composing through `ofReal`,
  multiplication by `I`, and `Complex.continuous_exp` gives
  `phase a p → 1`, hence the integrand `→ 0`.
- `lintegral_translation_tendsto_zero` — the dominated-convergence step
  (filter form `tendsto_lintegral_filter_of_dominated_convergence'`,
  since the index is the filter `nhds 0` on Minkowski space, not `ℕ`):
  the integral of the squared difference tends to `0`.
- `strongContinuity_window_proved` — the cap: `eLpNorm` of the difference
  equals `(∫⁻ ‖·‖ₑ²)^(1/2)` pointwise in `a` by the same
  `eLpNorm_eq_lintegral_rpow_enorm_toReal` identity, and `ENNReal`
  `rpow`-continuity at `0` (`Tendsto.ennrpow_const`) carries the integral's
  convergence to the norm's.

## Route, against the gauntlet's naming

Followed exactly, with two engineering deviations, neither mathematical:

1. The gauntlet names `tendsto_lintegral_of_dominated_convergence`
   (Mathlib/MeasureTheory/Integral/Lebesgue/DominatedConvergence.lean:63).
   In the pinned Mathlib (v4.35.0-rc3) that name is the **sequence**
   version (`ℕ`-indexed). The statement here is convergence along the
   filter `nhds 0` on Minkowski space, so the build uses the same file's
   filter version, `tendsto_lintegral_filter_of_dominated_convergence'`
   (:83) — the same theorem form, with the dominator `4‖ψ‖ₑ²` as scoped.
2. Placement: a new module `TranslationContinuity.lean` rather than an
   extension of `MassShellMeasure.lean` — the corpus's own pattern for
   discharging a window from a sibling file (MassShellBoost discharges
   `boostInvariance_window` the same way). `MassShellMeasure.lean` is
   unmodified.

## Fences

- **Translations only.** Strong continuity of the Lorentz/rotation part of
  the one-particle representation is a separate queue item (priced S–M in
  the gauntlet) and is **not** attempted here; nothing in this proof gives
  it — the Lorentz action moves points on the shell, so the DCT above,
  which rests on the shell action being *trivial* for `⟨a, 1⟩`, does not
  apply to it.
- **No Fock packaging.** `Γ(U₁)` as a Fock-space representation (a later
  queue item, priced M) is untouched; this is a one-particle statement.
- **Free theory, one particle, fixed mass shell.** No interacting, no
  continuum-limit, and no Yang–Mills statement is made or implied. Clay
  parts closed by this brick: **0**, as always until a theorem closes
  part of the official statement.

## Counts

- Strict declarations added: **10** (line-initial `^(theorem|lemma) ` on
  comment-stripped source); `@[simp]`-prefixed: **0**.
- Program total moves 2,677 → **2,687 strict** on this landing.
