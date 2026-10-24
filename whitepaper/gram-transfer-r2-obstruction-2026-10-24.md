# Gram clause, transfer-matrix route, rung R2 — OBSTRUCTION (the seam kernel has no configuration-valued square)

**Date:** 2026-10-24. **Verdict: the transfer-matrix route
TERMINATES AT R2.** Its pre-registered kill — charter
(`whitepaper/gram-clause-transfer-matrix-scoping-2026-10-24.md`)
§4, clause 1 — fires in the design phase. No Lean was built,
nothing proved was touched, nothing was weakened. Census
unchanged: **4,401 strict / 4,450 attribute-inclusive / 148
modules** (the post-R1 figures). Landing label unchanged: Stage
1b-B positivity **T1 for U(1)** at all β ≥ 0 (Route C); general
(G, ρ) **OPEN**.

**NO CLAIM.** Parts of any official Clay statement closed by
this document: **0**.

Inputs consumed: R1 (`LatticeLayerFactor`), S1
(`LatticeTransferID`), Q2 (`LatticeTransferPointwise`) — all
landed T1, all untouched by this verdict. Substantiation
script: `~/workspace/routeb-general-scratch/r2_obstruction_test.py`
(numpy/scipy, seed fixed) — re-run by the parent at ship time;
every headline number below matched (§5).

---

## 1. The reduction: R2 is one kernel's positive-definiteness

Every step is a landed statement; the chain is an
*equivalence*, so the obstruction is located, not gestured at.

1. **Form = two-slice pairing** (`transferOp_inner`,
   LatticeTransfer §5): for arbitrary ψ,
   `⟪ψ, Tψ⟫ = ∫ conj(ψ∘restrict₀) · (ψ∘next) dGibbs`; the value
   is real by landed self-adjointness
   (`transferOp_inner_symm` at f = g = ψ). So R2 ⟺ this Gibbs
   integral is ≥ 0 for all ψ.
2. **Every ψ is a prepared state.** Each
   `ψ : osSpace β = Lp ℂ 2 (sliceMeasure β)` is
   `sliceState μG ρ β φ hφ` for φ its own Lp representative
   (`Lp.memLp ψ`, `MemLp.coeFn_toLp`). By **S1**
   (`osForm_depthOne_transfer`), R2 ⟺ the depth-one OS
   diagonal `osForm β F F ≥ 0` for all slice observables — so
   the obstruction also blocks any depth-one partial
   discharge of 1b-B.
3. **R1 splits the pairing** (`integral_splitEquiv_factor`,
   `gibbsMeasure_map_splitEquiv_half`): it equals
   `Z⁻¹ ∫∫ conj(Φ(y)) Φ̃(u) · wPlus(y) · wMinus(u) ·
   layerWeightZero(y, u) dπ(y) dπ(u)`, with Φ / Φ̃ the two
   boundary readings and **`layerWeightZero =
   exp(−wilsonActionZero)`** the seam factor. All dependence
   coupling the two readings concentrates in that one factor.
4. **Conditioning** (finite-product Fubini): plaquettes
   touching exactly one boundary slice contribute one-sided
   positive factors; the rest contributes a positive factor.
   The only coupling is the seam — the temporal-link (τ)
   network integral of the crossing-plaquette Boltzmann
   factors. R2 ⟸ positive-definiteness of the fixed-seam
   layer kernel, and any `V† ∘L V` with configuration-valued
   mid-layer would have to reproduce the seam-integrated
   kernel `𝒦_T(x, y) = ∫ conj(K(x, m)) K(y, m) dμ(m)`.

## 2. The kill

**The fixed-seam factor is an exponential of a feature inner
product.** A near-seam crossing plaquette has holonomy
`U_p = u · τ′ · y⁻¹ · τ⁻¹`. By cyclicity of the trace and
unitarity of ρ,

  `tr ρ(U_p) = ⟨ρ(y), ρ(τ⁻¹ u τ′)⟩_HS`

(Hilbert–Schmidt). So per crossing plaquette the Boltzmann
factor is

  `exp(−β·plaquetteDensity) = e^{−β} · exp((β/d) ·
  Re⟨ρ(y), ρ(τ⁻¹ u τ′)⟩_HS)` —

the exponential of a real multiple of an inner product of two
ρ-features. An exponential of an inner product is a Gram
kernel **only** through its tensor series
`exp(c⟨Φ, Φ′⟩) = Σₙ (cⁿ/n!) ⟨Φ^{⊗n}, Φ′^{⊗n}⟩`, whose level-n
features are tensor powers of ρ — products of ρ-entries along
index paths: **words over the crossing plaquette**. That is
exactly charter kill clause 1 ("a factorization of the
one-step kernel over representation indices of a crossing
plaquette … rather than over the mid-layer configuration")
and exactly what charter constraint **D5** fences off from
this route.

**The feature support is infinite.** The class function
`g ↦ exp(β Re tr ρ(g))` (β ≠ 0) is analytic and
non-polynomial; its Peter–Weyl support is unbounded.
Verified at d = 1: the Fourier coefficients of
`exp(β cos θ)` are `Iₙ(β)`, and `Iₙ(1) > 0` for **every** n
(tail `I₁₂(1) = 5.2e-13 ≠ 0`). No finite tensor level closes
the separation; the mid-layer of any half-step operator V
for this kernel is a completion of the **word space** —
in the corpus's own terms, the `GramWordTensor` words — not
an L² space over a group-valued configuration.

**At d = 1 this is Route C, and that is the point.** At
d = 1 the word expansion *is* the Bessel Fourier series:
the one proof of seam positivity that exists in the corpus
is the expansion this route is chartered never to perform.
That is why U(1) closed (Route C) and why the transfer route
cannot follow it there.

**Absorption: the coupling is in the sharing, nowhere
else.** One crossing plaquette alone couples nothing: with
its two temporal links integrated independently, its kernel
collapses to a constant (Haar absorption; verified on U(1):
`I₀(1.3) = 1.469278` at all four probed (a, b)). The coupling
lives irreducibly in the **shared temporal-link network** —
each τ is shared between the two adjacent plaquettes — so
the seam kernel is a genuine network contraction whose only
Gram form is the global word series above.

## 3. Clause 2 does not fire — and the mismatch is named

Under the corpus's actual split (R1), the two *half* factors
are adjoint-matched: both halves carry the identical
`halfActionP` (the negative half read via `mirrorP`). Clause
2 therefore does **not** fire at the half level — R1 landed
exactly what it promised. What cannot be halved is the seam
density itself: there is no scalar kernel K on
(half × mid-layer-configuration) with
`layerWeightZero(y, u) = ∫ conj(K(y, m)) K(u, m) dμ(m)`.
The mismatch term, per crossing plaquette p:
**`exp((β/d) · Re tr ρ(U_p))`** inside `layerWeightZero` —
an exponential of a trace of a 4-link holonomy shared
between the halves, separable into one-sided factors only
through the tensor-power series of §2.

## 4. The independent β fence

Separately from §2: the rung's **every-real-β** form is
unavailable in principle. The seam kernel is not
positive-definite for β < 0 (at d = 1, `Iₙ(β) = (−1)ⁿ
Iₙ(|β|)` alternates; the single-link kernel
`(a, b) ↦ exp(β Re(a b⁻¹))` on L²(U(1)) at β = −1 has
circulant-Gram minimum eigenvalue **−36.17** with **8
negative modes**, vs none at β = +1). Any revival of R2 is
therefore narrowed to **β ≥ 0** — Route C's range —
regardless of the kill in §2, which itself is at β ≥ 0 and
concerns the proof route, not the sign. This is the
narrowing charter D3/U5 anticipated, printed on the face.

## 5. No soft argument exists (certified)

The landed package — `transferOp_form_nonneg` (positivity on
pointwise-positive real observables) + self-adjointness —
does **not** imply all-vector positivity in general: the
swap matrix `[[0,1],[1,0]]` on ℝ² is self-adjoint and
positivity-preserving, with `⟪f, Tg⟫ ≥ 0` for all positive
f, g, yet `⟪(1,−1), T(1,−1)⟫ = −2 < 0`. Polarizing the
landed form-positivity produces the cross-pairings with the
wrong sign. R2 genuinely required the Gibbs seam structure —
which is where §2 sits. The kill is a property of the route,
not of effort.

## 6. Computations (preserved; re-run at ship time, matched)

Script: `r2_obstruction_test.py` (parent re-run 2026-10-24,
all values confirmed against the verdict memo):

- **(D) SU(2) trace identity:**
  `tr ρ(uτ′y⁻¹τ⁻¹) = ⟨ρ(y), ρ(τ⁻¹uτ′)⟩_HS`, |Δ| = 1.1e-16.
- **(A) Bessel support:** `Iₙ(1) > 0` for all n ≤ 12;
  tail `I₁₂(1) = 5.2e-13 ≠ 0` — infinite rank.
  `Iₙ(−1) = (−1)ⁿ Iₙ(1)` (alternating).
- **(B) Absorption:** U(1) single-plaquette absorbed kernel
  = **1.469278** `= I₀(1.3)` at (a, b) = (1, 1), (i, 1),
  (e^{0.7i}, e^{−1.9i}), (−1, i) — constant.
- **(C) β-sign:** circulant Gram (K = 64) of
  `exp(β cos(θ−φ))`: β = +1 — no negative eigenvalues;
  β = −1 — minimum eigenvalue **−36.17**, 8 negative modes.

## 7. What survives, at full rank

- **Untouched:** S1 (depth-one identification), R1
  (factorization), Q1 (`posToSlice`), Q2 (pointwise
  positivity), `transferOp_form_nonneg`, self-adjointness,
  contraction, the β = 0 sector. Stage 1b-B: T1 for U(1),
  general (G, ρ) **OPEN** — unchanged.
- **Even powers are free:** `T^{2k} = (T^k)† (T^k)` by landed
  adjoint algebra, so `⟪ψ, T^{2k} ψ⟫ = ‖T^k ψ‖² ≥ 0` needs
  nothing from R2.
- **R3's identification remains buildable as scoped** —
  `osForm β F F = ⟪ψ_F, T^m ψ_F⟫` is positivity-free and
  R1's iteration forms (`integral_layerFactor_iterated`)
  stand ready for it.
- **Blocked:** every odd power. R4's discharge needs
  `⟪ψ, T^{2k+1} ψ⟫ ≥ 0`, i.e. R2 on the range of `T^k`; and
  by §1 step 2 the depth-one discharge is *equivalent* to
  R2. **The transfer route as chartered therefore terminates
  at R2 on its own pre-registered criterion.**

## 8. U1 — resolved, with jurisdiction

Charter §5 U1 asked whether the (k, a)/(j, i) obstruction
could reappear one level up. The record now carries the
answer at full precision: the mechanism has **no purchase**
on the layer factorization (R1 — its hinge is a whole
mid-layer configuration; it landed) and **no purchase** on
the identification (S1, and R3's as scoped) — and **full
purchase** on positivity, where the hinge is once again an
exponential of ρ-entries of a crossing plaquette, separable
only over representation indices.

## 9. The one named remainder — NOT commissioned

Where the positivity actually lives: the **word expansion
of the crossing weight `exp(−wilsonActionZero)` as a
factored family for the landed conditional
`osForm_nonneg_of_gram_integrated`**. This is a *third*
family — not the factored occurrence family killed at T4c′
(its features are half-action averages; these are seam
words), not the polarization class killed at regrouped R0 —
and it is Gram-route territory, fenced off from the
transfer route by D5 and by R2's kill criterion. It is
recorded here so the map of the territory is exact. It is
**not built, not claimed, and not commissioned**; taking it
up would be a new route decision (Jeff's call).

---

**Route status:** the transfer-matrix route landed its
factorization (R1) and its depth-one identification (S1),
and dies at the positivity rung on its own pre-registered
criterion — the (k, a)/(j, i) mechanism one level up, exactly
the jurisdiction question its charter posed. Stage 1b-B
remains **OPEN** at general (G, ρ). Three closures of
1b-B approaches now stand on the record at full rank: T4c′
(the factored family), regrouped R0 (the polarization
class), and this one (the transfer route's positivity
step) — beside two standings the same campaign produced:
Route C's U(1) theorem, and the S1/R1 landings this route
leaves behind. **NO CLAIM.**

— BONES, for the record. Tiers per the Concrete; the kill
ships at the same speed and fullness as a landing.
