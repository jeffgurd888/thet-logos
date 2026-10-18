# Lorentz/Rotation Strong Continuity — Dossier (2026-10-18)

**Verdict: STANDS — WHOLE, no narrowing.** The Lorentz half of the Rung 7
strong-continuity remainder — the last joint of Rung 7 — is discharged at
the commissioned price (S–M). Strong continuity of the Lorentz subgroup
of the one-particle Poincaré action is proved for the **full restricted
Lorentz group** (boosts and rotations together, no axis or subgroup
restriction), at the identity and, by the group law, at every point.
**T1 throughout: 28 strict theorem declarations, zero `sorry`/`admit`,
zero `@[simp]`, headline axioms exactly the standard three (`propext`,
`Classical.choice`, `Quot.sound`).**

## What was owed

The translation half (`TranslationContinuity.lean`, 10 T1, dossier
`translations-continuity-2026-10-18.md`) discharged continuity of the
translation subgroup of the action on `L²(massShellMeasure m)` by
dominated convergence with dominator `4‖ψ‖²` — a route that rests on the
shell action being *trivial* for pure translations and therefore provably
does not extend to the Lorentz subgroup, whose action moves points on
the shell. The parked-fleet gauntlet
(`whitepaper/gauntlet-parked-fleet-2026-10-17.md`, §4a) scoped this
remainder (continuity of the one-particle action under the remaining
factor, proved by density + uniform control), and the commission priced
it **S–M** with a PARTIAL fallback (named narrowing) if the full
subgroup resisted. It did not resist; the fallback was not needed.

## What landed

New module **`lean/ThetLogos/LorentzContinuity.lean`** (28 strict
theorems; `MassShellMeasure.lean` / `MassShellBoost.lean` /
`TranslationContinuity.lean` untouched, per the commission). Targeted
build green (**3,661 jobs**), `.olean` verified, parent-checkable by
`lake build ThetLogos.LorentzContinuity`.

Headlines:

```lean
theorem shellU1_lorentz_tendsto (m : ℝ) (hm : 0 < m) (Ψ : shellLp m hm) :
    Tendsto (fun Λ : RestrictedLorentz => shellU1 m hm ⟨0, Λ⟩ Ψ) (𝓝 1) (𝓝 Ψ)

theorem shellU1_lorentz_tendsto_at (m : ℝ) (hm : 0 < m)
    (Λ₀ : RestrictedLorentz) (Ψ : shellLp m hm) :
    Tendsto (fun Λ : RestrictedLorentz => shellU1 m hm ⟨0, Λ⟩ Ψ) (𝓝 Λ₀)
      (𝓝 (shellU1 m hm ⟨0, Λ₀⟩ Ψ))
```

i.e. for **every** mass `m > 0` and **every** one-particle state
`Ψ ∈ L²` of the mass shell, the packaged Lorentz action
`Λ ↦ shellU1 ⟨0, Λ⟩ Ψ` is continuous — first at the identity, then at
every `Λ₀` by the factorization `⟨0, Λ⟩ = ⟨0, Λ₀⟩ * ⟨0, Λ₀⁻¹·Λ⟩`.

**On the topology, stated plainly (a real content point, not a
technicality).** The corpus had no topology on `LorentzGroup` anywhere;
the statement of Lorentz strong continuity needs one. The module equips
`LorentzGroup` with the **topology of pointwise convergence of the
action on Minkowski space** — equivalently (proved, `tendsto_lorentz_iff`
+ `tendsto_lorentzCoord_iff`) entrywise convergence of the representing
matrices in the standard basis. In finite dimensions this is the usual
Lie-group topology of the Lorentz group; `RestrictedLorentz` carries the
subspace topology. Both are first countable. Continuity is proved for
this topology; no other topology on the group is claimed or needed.

## The route: spatial side, coefficient trick, density, ε/3

The proof follows the commission's scoped route (density + uniform
control), executed on the spatial side of the graph parametrization,
with one simplification found in the corpus's own materials that avoids
the hardest domination step (named here because the commission asked for
cleaner routes to be named when taken):

1. **Transport to ℝ³.** The graph parametrization `shellParam : ℝ³ → Hₘ⁺`
   conjugates the shell action to a spatial action
   `spAct Λ u = spatialOf (Λ⁻¹ (shellParam u))` on ℝ³
   (`spActEquiv_apply`, `measurePreserving_spAct` — the shell measure
   invariance of `FockPackaging` transported along `shellParamEquiv`).
   The intertwining identity `shellLpEquiv_shellU1`,
   `shellLpEquiv (shellU1 ⟨0, Λ⟩ Ψ) = spU Λ (shellLpEquiv Ψ)`, reduces
   shell continuity to continuity of the spatial composition operators
   `spU Λ F = F ∘ spAct Λ` on `spatialLp m = L²(d³u/(2E_u))`.

2. **Dense class: continuous compactly-supported functions.** For such an
   `F`, the squared-norm identity is computed as an integral and ONE
   change of variables (`MeasurePreserving.integral_comp`, which needs
   no integrability side condition) moves `Λ` onto the *fixed* factor:
   `‖spU Λ Ǧ − Ǧ‖² = ∫ ‖F v‖² − 2·Re ∫ conj(F v)·F(spAct Λ⁻¹ v) + ∫ ‖F v‖²`.
   The cross integrand is dominated by `B·‖F v‖` (`B` a sup bound of
   `F`) — integrable, with no `Λ`-dependence to dominate — and converges
   pointwise because `spAct Λ⁻¹ v → v` as `Λ → 1`, which holds *by
   definition* of the pointwise-convergence topology
   (`tendsto_spAct_inv`). Filter-form dominated convergence
   (`integral_cross_tendsto`) closes the cross term; the square root
   closes the norm (`spU_tendsto_of_continuous`). This is the
   coefficient trick: the translations dominator `4‖ψ‖²` does not
   generalize, and no replacement dominator for the *moved* factor is
   ever needed, because the moved factor is eliminated by substitution
   before convergence is taken.

3. **ε/3 extension.** `C_c` functions are dense in `spatialLp m` by
   Mathlib's `MemLp.exists_hasCompactSupport_eLpNorm_sub_le` — its
   regularity hypothesis is discharged by
   `isLocallyFiniteMeasure_spatialMeasure` (the spatial measure is
   Lebesgue measure with the continuous density `(2E_u)⁻¹`) plus
   σ-compactness of ℝ³. Every `spU Λ` is a linear isometry, so the
   standard ε/3 argument extends continuity from the dense class to
   every `L²` element (`spU_tendsto`), and `shellLpEquiv` carries it
   back to the shell (`shellU1_lorentz_tendsto`).

4. **Transport in the group.** Left multiplication by a fixed inverse is
   continuous at the diagonal in the pointwise topology
   (`tendsto_restricted_inv_mul`: `(Λ₀⁻¹·Λ) p = Λ₀⁻¹(Λ p)`, a fixed
   continuous linear map applied to a convergent net), and the group law
   `shellU1_apply_mul` then gives continuity at every `Λ₀`
   (`shellU1_lorentz_tendsto_at`).

Support theorems (all T1) include: the topology API
(`tendsto_lorentzCoord_iff`, `lorentz_apply_coord`, `tendsto_lorentz_iff`,
`tendsto_restricted_iff`, `tendsto_restricted_apply`,
`tendsto_restricted_inv_mul`); the spatial action API (`spAct_comp` —
anti-homomorphism law matching the pullback, `spAct_one`,
`spAct_inv_comp_self`, `spAct_comp_inv_self`, continuity of `spAct`,
`spatialOf`, `shellParam`); the measure package (`spActEquiv`,
`measurePreserving_spAct`, `measurableEmbedding_spAct`); the
intertwining pair (`oneParticleFun_zero`, `shellLpEquiv_shellU1`); and
the analytic infrastructure (`isLocallyFiniteMeasure_spatialMeasure`,
`lp_norm_sq_eq_integral`, `tendsto_spAct_inv`, `integral_cross_tendsto`).

## Fences — what this does NOT give

- **One-particle level only.** Fock-level transport of Lorentz strong
  continuity is **NOT** landed and is **not** free: `FockPackaging`'s
  transport theorems are stated for the translation parameterization;
  the kernel-level filter lemma is generic, but entrywise
  matrix-element continuity for the Lorentz family is a new per-statistic
  proof in each of `FockPackagingBos` / `FockPackagingFerm`, and the two
  cannot be co-imported (the standing `numberOp` fence). This brick
  discharges exactly the one-particle input such transports consume.
  Fock-level Lorentz continuity remains an open, unpriced line item.
- **Subgroup-wise, not joint.** No topology on `RPoincare` is
  introduced. What stands after this landing: the translation subgroup
  action is strongly continuous (2026-10-18, TranslationContinuity) and
  the Lorentz subgroup action is strongly continuous (this brick).
  Strong continuity of the combined action in a product/joint topology
  on the full group is a separate statement, not claimed here.
- `spatialLp m` in this module is the graph-parametrization `L²` space of
  `FockPackaging` (density `d³u/(2E_u)`); continuity is proved there and
  transported back — no new function space is introduced.
- Free theory, one particle, fixed mass shell. Nothing about the
  interacting theory, the continuum limit, or Yang–Mills. **Parts of any
  official Clay statement closed by this brick: 0.**

## Verification (reproduce before citing)

- `lake build ThetLogos.LorentzContinuity` — green, 3,661 jobs, `.olean`
  present.
- Strict recount on the comment-stripped source (line-initial
  `^(theorem|lemma) `): **28**. `@[simp]`: **0**. `sorry`/`admit`
  tokens: **0**.
- `#print axioms` on `shellU1_lorentz_tendsto`,
  `shellU1_lorentz_tendsto_at`, `spU_tendsto`,
  `spU_tendsto_of_continuous`, `integral_cross_tendsto`,
  `shellLpEquiv_shellU1`, `tendsto_restricted_inv_mul`: each exactly
  `[propext, Classical.choice, Quot.sound]`.
- Program total: 2,989 + 28 = **3,017 strict**.

## Surprises

- Two Mathlib routes the scoping had priced as work turned out to be
  one-liners: `MeasurePreserving.integral_comp` performs the key change
  of variables with **no integrability side condition** (only a
  measurable-embedding hypothesis), and the strengthened
  `MeasurePreserving.integrable_comp` needs only a.e. strong
  measurability.
- The only genuinely fiddly point was coercion bookkeeping between the
  two forms of the inverse, `((Λ⁻¹ : RestrictedLorentz) : LorentzGroup)`
  vs `(Λ : LorentzGroup)⁻¹` — definitionally equal (the corpus's own
  `rfl` in `MassShellMeasure`), but rewrite steps must be fed the form
  that occurs syntactically; solved by ascribing membership facts in the
  needed form.
