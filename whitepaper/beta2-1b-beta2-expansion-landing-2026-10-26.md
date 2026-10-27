# Brick β2-1b — The β² Expansion: the Seat Was Not Luck

*Landing dossier, 2026-10-26. Module:
`lean/ThetLogos/PlaneCrossingBeta2.lean` (strict 71, zero
`sorry`, zero `native_decide`; main-tree build green, 3,444
jobs, parent-verified). **Parts of the Clay Yang–Mills
statement closed by this landing: 0.** No positivity at any
β > 0 follows from anything here — β2 and (H-PF) remain
L+/open, and the module says so on its face. N = 2 is fenced
out (extra paired terms).*

## The question this brick was built to answer

The (S₃, standard) seat computation (β2-1a) found κ₂
*constant* — its (u,u′)-dependent part identically zero — and
the seat had looked lucky: tiny group, self-dual
representation, character values in {2, 0, −1}. Was the
vanishing a theorem or the seat's accident?

## The answer: a theorem, at general (G, ρ)

- **Every word moment is word-independent** — each column's
  word is a Haar translate / cyclic rearrangement of the
  column variable, so the moments cannot see which word they
  came from. Distinct columns collapse analytically:
  E[Re χ_P · Re χ_Q] = e₁² (`integral_cross`, the
  P₀-collapse as a theorem).
- **The expansion, closed forms:** with M the column count,
  e₁ = ∫ Re χ, q₂ = ∫ (Re χ)², d = dim ρ:
  C₁ = M(1 − e₁/d) and
  C₂ = ½[M(1 − 2e₁/d + q₂/d²) + M(M−1)(1 − 2e₁/d + e₁²/d²)],
  and 𝒜 = 1 − βC₁ + β²C₂ + R(β) with an explicit remainder
  bound. **𝒜's (u,u′)-dependence is O(β³)** in general
  (`layerKernel_dep_beta2_zero`). Hypotheses: N even, N ≥ 3
  — **no self-duality anywhere**.
- **The vanishing criterion, exact:** the single-link form
  is constant at general (G, ρ), κ₂(u,u′) = (1/(4d²))·Re m₂
  with m₂ = ∫ χ² dμG, and **κ₂ ≡ 0 ⟺ m₂ = 0**
  (`kappa2_eq_zero_iff`). Self-duality enters only through
  the classical reading m₂ = multiplicity of the trivial
  representation in ρ⊗ρ — recorded as prose (T4), not a Lean
  claim.

So the (S₃, std) seat's constant κ₂ was the general theorem
showing through the smallest window that could display it.
The luck was in our choice of seat, not in the mathematics:
the seat was *legible*, not *rigged*. Positivity of 𝒜 at any
fixed β > 0 is untouched by this expansion — the dependent
directions are decided at O(β³) and beyond, exactly where
β2-0 proved the joint average is essential.

Axiom sets on six headlines: exactly
`[propext, Classical.choice, Quot.sound]` each.

## Census effect

Strict 6,217 → **6,288**; attribute-inclusive 6,295 → **6,366**;
modules 212 → **213**; `sorry` placeholders unchanged at **6**.

## Backers since last landing

No new backers inscribed in this interval; the roll stands as
recorded in `BACKERS.md`. Every gift is published with the proof
stream, named as the giver wishes, amounts only with the giver's
permission — the standing reciprocity of this house.
