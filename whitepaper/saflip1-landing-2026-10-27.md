# SA-FLIP-1 — The a₂ Coefficient, Separated: Gravity's Slot at Coefficient Grade

*Landing dossier, 2026-10-27. Module:
`lean/ThetLogos/SpectralActionA2.lean` (strict 7,
defs 3, zero placeholders, zero `native_decide`, no
new axioms; main-tree build green, 3,127 jobs,
parent-verified). **Parts of the Clay Yang–Mills
statement closed by this landing: 0.** All three
pre-named kill conditions were checked and none fired.
The label fence, stated once more on purpose: **this
is the coefficient of the scalar-curvature slot in the
spectral action's heat expansion, proved as algebra —
gravity's shadow at coefficient grade. It is not
spacetime gravity, not a gravity object, and not a
Dial-2 movement; the gravity chair stays empty.***

## What is proved

- **Trace factorization, from structure (KC-1 silent).**
  `trace_endomorphismEA` — with E_A built as the actual
  Kronecker endomorphism ((R/4)•1) ⊗ₖ 1 + 1 ⊗ₖ (D_F^A)²
  on the 128-dimensional product, Tr₁₂₈(E_A) =
  32·R + 4·Tr₃₂((D_F^A)²) is *derived* from
  `Matrix.trace_kronecker`, not assumed. The abstract
  scalar R is a bound variable throughout — the
  treatment introduces no axiom (checked: every
  headline's axiom set is exactly `[propext,
  Classical.choice, Quot.sound]`).
- **Separated a₂, as a new entry.**
  `seely_dewitt_a2_separated` — the Gilkey-form a₂
  equals (4π)⁻² · [(160/3)·R + 4·Tr₃₂((D_F^A)²)]. The
  constant 160/3 = 64/3 (from Tr(R/6) over 128) + 32
  (from E_A) is now machine-checked arithmetic; the
  placeholder `SpectralAction.seely_dewitt_a2_formula`
  (which proves `True`) stands untouched beside it
  under the relabeling rule, superseded in content, not
  in name.
- **The gravitational coefficient is nonzero (KC-2
  silent).** `a2_grav_coeff_ne_zero` — 160/3·(4π)⁻² ≠ 0.
  Within the fixed, conventionally standard form (KC-3:
  no convention was rigged to protect it — E_A is taken
  exactly as the corpus defines it), the Einstein–
  Hilbert slot in this expansion is genuinely occupied:
  the coefficient does not vanish.
- **The matter part, discharged by citation.**
  `a2_matter_discharged` / `…_fluctuated` — the
  Tr₃₂(D_F²) term *is* the landed finite trace (the
  exact Yukawa polynomial), connected to the finite
  spectral-action results rather than recomputed; and
  `a2_matter_vanishes_iff` — it vanishes exactly when
  all five Yukawa couplings vanish.

## What this is, and is not

Heat-kernel coefficients are how the spectral action
*contains* an Einstein–Hilbert term (Connes–
Chamseddine, T4); what this brick adds is that the
*separation* of the a₂ coefficient into its
gravitational and matter parts is a theorem in this
corpus, with R kept as an honest abstract scalar —
because the corpus owns no metric from which to compute
it, and says so. Nothing here moves any dial. It closes
the spectral-flip line's sharp residue: there was no
flip; there was a coefficient, and the coefficient is
now proved separated and nonzero.

## Census effect

Strict 6,450 → **6,457**; attribute-inclusive 6,528 →
**6,535**; modules 223 → **224**; placeholders unchanged
at **7**.

## Backers since last landing

No new backers inscribed in this interval; the roll stands
as recorded in `BACKERS.md`. Every gift is published with
the proof stream, named as the giver wishes, amounts only
with the giver's permission — the standing reciprocity of
this house.
