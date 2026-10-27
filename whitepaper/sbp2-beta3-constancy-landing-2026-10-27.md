# SBP-2 — β³ Constancy: The Layer Kernel's Dependence Is O(β⁴)

*Landing dossier, 2026-10-27. Module:
`lean/ThetLogos/PlaneCrossingBeta3.lean` (strict 17, defs
2, 1,382 lines, zero `sorry`, zero `native_decide`;
main-tree build green, 3,446 jobs, parent-verified).
**Parts of the Clay Yang–Mills statement closed by this
landing: 0.** The small-β chapter of the layer kernel 𝒜 is
now proved through order 3 at general (G, ρ): every
coefficient through β³ is a constant, and the first place
(u,u′)-dependence can live is the β⁴ term — the spatial
plaquette 4-cycles. NO CLAIM; dials 0/4.*

## The headline

> **`layerKernel_dep_beta3_zero`** — at general (G, ρ),
> every even N ≥ 4: the β³ coefficient of 𝒜 is
> (u,u′)-independent. With β2-1b's β¹ and β² clauses, 𝒜's
> dependence on its arguments is O(β⁴), made explicit by
> `layerKernel_expansion3` (𝒜 = 1 − βC₁ + β²C₂ − β³C₃ + R₄)
> and the tail bound `layerKernel_tail_bound3`:
> |R₄(β)| ≤ (2M|β|)⁴/24 · exp(2M|β|).

**C₃ in closed form** (`betaCoeff3_closed`): a polynomial
in M and the real moments e₁, q₂, μ₃ alone —
C₃ = [M³ − 3M³(e₁/d) + 3M²(q₂/d²) + 3M²(M−1)(e₁²/d²)
− M(μ₃/d³) − 3M(M−1)(e₁q₂/d³) − M(M−1)(M−2)(e₁³/d³)]/6.
Axiom sets on all checked headlines: exactly
`[propext, Classical.choice, Quot.sound]`.

## Why order 3 falls

The one new combinatorial input landed as priced:
`exists_private_site_triple` — a triple of distinct
columns always has a private site, because a non-strippable
triple would need a triangle in the site lattice and the
even-N lattice has none (proved via the ZMod N
coordinate-sum invariant: column site differences are ±1,
forcing N ∣ 1 or N ∣ 3). With private sites in hand,
`integral_colRe_triple` factors the triple moment,
∫ r_P r_Q r_R = μ₁³, and the leaf-stripping induction over
β2-1b's Haar-translate machinery closes the order.

## The memo flag

The scoping memo's moment menu for C₃ named complex
moments (∫χ³, ∫χ²χ̄, m₂). The derivation consumes **none
of them**: the layer density sees only Re χ, so C₃ is a
function of the real moments e₁, q₂, μ₃ = ∫(Re χ)³ alone.
The memo's structural claim — κ₃^dep ≡ 0, dependence first
at O(β⁴) — is confirmed exactly; its menu was wrong, and
the correction is on the record. Derivations outrank
memos.

## The fence

This is a strong-coupling-end statement. It proves the
β⁴ threshold; it asserts **no sign** for the β⁴ dependent
part at general (G, ρ) (at the (S₃, std) seat SBP-1 found
that part to be a rank-one square — a seat computation,
not a theorem). No 𝒜 ⪰ 0 at any β > 0 follows; (H-PF)
remains open at general (G, ρ); even N is load-bearing;
the continuum trajectory is untouched and not implied.
NO CLAIM; dials 0/4.

## Census effect

Strict 6,385 → **6,402**; attribute-inclusive 6,463 →
**6,480**; modules 215 → **216**; `sorry` placeholders
unchanged at **6**.

## Backers since last landing

No new backers inscribed in this interval; the roll stands
as recorded in `BACKERS.md`. Every gift is published with
the proof stream, named as the giver wishes, amounts only
with the giver's permission — the standing reciprocity of
this house.
