# Gentle Gauntlet: Morley / 3+1 Emergence

**Date:** 2026-10-11. **Mode:** gentle gauntlet (steelman first, kill only if dead).
**Formalization:** `lean/ThetLogos/EdgeSignature.lean` — **BUILD GREEN**
(`lake env lean`, EXIT 0, 2026-10-11 ~15:45 EDT). 13 theorems, zero sorrys,
zero new axioms; `#print axioms` confirms only `[propext, Classical.choice,
Quot.sound]` throughout. Six benign unused-section-variable linter warnings.

---

## 1. The idea (Jeff's)

Morley's miracle: the adjacent trisectors of *any* triangle lock into a
perfect equilateral triangle inside it — arbitrary input, perfect structure
out. The naive 3D lift fails (no tetrahedron analogue; the projection goes
ill-posed).

**Question:** can a 4D boundary carrying *two 2D edge operators* generate the
3+1 (space+time) split?

**Concrete anchor:** in 4D, 2-forms split self-dual/anti-self-dual, and that
split IS signature-sensitive (⋆² = −1 Lorentzian). The Krein η (η² = 1) from
Rung 3 is the abstract fundamental symmetry encoding signature.

**Jeff's refinement (built in):** the projection from D_F may carry
torsion/twist — carried, never assumed away. The Rung-2 flip twist is carried
through (§2). Torsion is modeled as an additive defect with the exact
idempotence defect computed (§3). The killed ℂ⁷-torsion claim is NOT
resurrected.

---

## 2. Steelman

Model the "two 2D edge operators" as a complementary orthogonal idempotent
pair `(E₊, E₋)` — the abstract self-dual/anti-self-dual decomposition — and
the "4D boundary signature data" as a fundamental symmetry `η` with `η² = 1`
(the Krein structure's algebraic core).

**Core equivalence (T1):** edge-pair data ⟺ fundamental-symmetry data.
From `η² = 1`: `E± = (1±η)/2` are perfect (idempotent, orthogonal,
complementary) — `edgePair_of_symm`. From a perfect pair: `η = E₊ − E₋`
squares to 1 — `symm_of_edgePair`. The map is a bijection of data.

---

## 3. What's formalized (all T1, zero sorrys, zero new axioms)

**§1 — Morley core** (`edgePlus_idem`, `edgeMinus_idem`, `edge_orth_lr/rl`,
`edge_compl`, `edge_recover`, `edgePair_of_symm`, `symm_of_edgePair`):
arbitrary `η` with `η² = 1` yields a perfect edge pair, using nothing beyond
`η² = 1`.

**§2 — Flip-twist equivariance** (`edgePlusPair_flip`, `edgeMinusPair_flip`,
`edgePlusPair_diag_flip`, `edgeMinusPair_diag_flip`): the flip swaps the two
edge copies; for the doubled symmetry `(η,η)` the edge pair is flip-INVARIANT
— the Rung-2 twist preserves Morley perfection.

**§3 — Torsion defect** (`torsion_defect`, `torsion_flat_iff`,
`edgePlus_torsion_defect`): `(η+T)² = 1 + (ηT + Tη + T²)` exactly;
fluctuated edge operators miss idempotence by exactly
`(2⁻¹)² • (ηT + Tη + T²)`; perfection survives torsion iff
`ηT + Tη + T² = 0` (Maurer–Cartan-type flatness).

**§4 — Signature non-emergence** (`sigA_sq`, `sigB_sq`,
`edgeMinus_sigA`, `edgeMinus_sigB_snd/ne`, `signature_not_determined`):
`(1,1)` and `(1,−1)` on `ℂ × ℂ` both square to 1, but one's minus-edge
vanishes (signature (2,0)) and the other's doesn't (signature (1,1)).

---

## 4. Torsion/twist accounting

- **Flip twist:** carried via equivariance — the doubled edge decomposition
  commutes with the flip. The twist does not break the perfection.
- **Torsion:** carried as an additive defect `T` on the fundamental symmetry,
  with the EXACT defect equation. Jeff's "torsion twist in the projection
  from the D_F" is accounted to the scalar: the projection stays perfect
  iff the torsion satisfies `ηT + Tη + T² = 0`.
- **What remains priced:** the D_F-specific map (how inner fluctuations
  `D ↦ D_A = D + A + JAJ⁻¹` induce the defect `T` on a concretely-built η).
  This needs η constructed from Dirac data — not assumed here.

---

## 5. Morley analogy assessment (honest)

**Formal content (real):** the "arbitrary input → perfect structure" pattern
is genuine at the algebraic level — the perfection (idempotence,
orthogonality, complementarity) is FORCED by `η² = 1` alone, regardless of
which `η`. No extra assumptions smuggled.

**Evocative only:** Morley's theorem has the extra content that the inner
triangle is EQUILATERAL — maximal symmetry emerging from no symmetry. Our
analogue produces the decomposition, not extra symmetry. The "miracle"
grading is philosophical, not mathematical.

---

## 6. Verdict

| Component | Verdict |
|---|---|
| Edge-pair ⟺ fundamental symmetry (Morley core) | **PROMISING** — formalized T1, twist+​torsion carried |
| Torsion defect equation | **PROMISING** — exact, T1; D_F-specific map priced |
| Flip-twist equivariance | **PROMISING** — T1, minimal and honest |
| Strong emergence ("edge data → 3+1 numbers") | **NO-GO** — sharp counterexample: `η² = 1` does not determine the signature; the 3+1 numbers are extra data |
| Morley analogy | **NEEDS-WORK** — real formal content at the algebraic level; the "miracle" grading stays philosophy |

**Overall: PROMISING with one precise kill.** The mechanism (edge operators
encode signature via the fundamental symmetry) is real and machine-checked.
The strong claim (the signature *numbers* emerge) is dead by counterexample —
and its death is itself a T1 theorem. The idea survives in its honest form.

---

## 7. Priced next steps

1. **D_F-specific torsion map:** build η from Dirac data (grading/sign),
   compute the induced defect `T` under inner fluctuations `D ↦ D_A`.
   Needs: concrete η-from-D construction.
2. **Dimensional reading:** "two 2D" suggests a 2+2 decomposition (neutral
   signature (2,2)), not (3,1) — investigate whether the edge-pair
   formalism naturally selects (2,2) and what breaks it to (3,1).
3. **Twisted-FOC integration:** connect the torsion-flatness condition
   `ηT + Tη + T² = 0` to the twisted first-order condition machinery
   (Rung 3/EVOLVE) — the defect may be the FOC's shadow.
4. **Boundary formalization:** the "4D boundary" itself is not yet a
   formal object — currently the algebra stands alone. A boundary
   spectral triple would be the honest home.

*The ℂ⁷ kill stands. Nothing resurrected. The gentle gauntlet concludes:
the idea is stronger for the examination — one precise kill, a real
mechanism, and priced doors forward.*
