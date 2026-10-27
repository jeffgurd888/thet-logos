# LOC-1 — The Polymer Activity Brick: All Two-Column Connected Activities Vanish

*Landing dossier, 2026-10-26. Module:
`lean/ThetLogos/PolymerActivity.lean` (strict 42, defs 7,
1,140 lines, zero `sorry`, zero `native_decide`; main-tree
build green, 3,445 jobs, parent-verified). **Parts of the
Clay Yang–Mills statement closed by this landing: 0.** This
is the first brick of the polymer/cluster route to
uniformity — the only route whose constants are N-uniform
by construction. It also corrects its own scoping memo in
two places; derivations outrank memos in this house, and
both corrections are on the module's face.*

## What landed

At general (G, ρ), N even, on β2-1b's moment machinery:

- **The activity, defined and liberated from its column.**
  `colActivity` is the α-integrated Taylor coefficient
  ∫(−β)ᵏ/k!·dens_Pᵏ of a single column, with closed form
  through the real Haar moments; `colActivity_independent`:
  it is a function of the label alone — no dependence on
  base site, direction, or boundary links.
- **Degrees ≤ 2 as activity statements.** Degree 1:
  1 − e₁/d; degree 2: 1 − 2e₁/d + q₂/d²; β2-1b's C₁, C₂
  restated as activities; `activity_kappa2`: κ₂ =
  (1/(4d²))·Re m₂, constant. No irreducibility hypothesis
  anywhere — group data enters only through d and
  (e₁, q₂, m₂).
- **The majorant.** |ζₖ| ≤ (2|β|)ᵏ/k!, via contraction
  numbers |μₐ|/dᵃ ≤ 1 (`contractionNumber_le_one`); the
  total single-column activity Σ_{k≥1}|ζₖ| ≤ exp(2β) − 1
  (`total_colActivity_le`); the dependent sector starts at
  degree 3. Axiom sets on the checked headlines: exactly
  `[propext, Classical.choice, Quot.sound]`.

## The two corrections

**1. The connected two-column sector is empty — at every
degree.** The LOC-0 scoping expected the first nonzero
connected activities at degree pairs (2,1) and (2,2). The
mathematics says otherwise: for distinct columns,
∫ r_Pʲ r_Qᵏ = μⱼμₖ exactly (private-site factorization,
`integral_colRe_pow_mul`), so `connectedActivity_eq_zero`
holds for **all** degree pairs (N ≥ 3), the named (1,1)
zero landed as specified, and the (2,1)/(2,2) pair
activities are the explicit products of the one-column
moments. The dependent polymer gas is thinner than the
scoping counted: genuinely connected activities first
exist at **three** columns. This is good news for LOC-2's
convergence — and it is recorded as a correction, not
quietly absorbed.

**2. The scoping memo's majorant constant was false.** The
memo's bound (2β/d)ᵏ/k! fails for the density activity:
at d = 2 with ρ = sign⊕sign, ∫densᵏ = 2ᵏ⁻¹ > (2/d)ᵏ for
k ≥ 2. The landed majorant is (2|β|)ᵏ/k! in the corpus's
density normalization, with the contraction-number form —
group data only through d and numbers ≤ 1 — being the form
LOC-2 consumes. LOC-2's β₀ will be computed from the
landed constant, not the memo's.

## The fence

LOC-1 owns activities and their bounds. It proves no
convergence (that is LOC-2, where uniformity is born as
sums over clusters through a fixed column) and no regime
theorem (LOC-3). Nothing here touches the continuum, the
trajectory end of the coupling, or any part of the Clay
statement. The pre-named PARTIAL seam at the (2,2)
contraction was **not taken** — nothing is left as a
bounded-but-uncomputed contraction. NO CLAIM; dials 0/4.

## Census effect

Strict 6,343 → **6,385**; attribute-inclusive 6,421 →
**6,463**; modules 214 → **215**; `sorry` placeholders
unchanged at **6**.

## Backers since last landing

No new backers inscribed in this interval; the roll stands
as recorded in `BACKERS.md`. Every gift is published with
the proof stream, named as the giver wishes, amounts only
with the giver's permission — the standing reciprocity of
this house.
