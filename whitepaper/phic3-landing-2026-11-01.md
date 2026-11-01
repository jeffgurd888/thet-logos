# PHI-C3 LANDING DOSSIER — 2026-11-01

**Item:** PHI-C3 (the full census), closing brick of the PHI-C
salvage line (memo `scoping-phi-icosa-2026-10-30.md`; PHI-C0/C1
FULL, PHI-C2 PARTIAL with uniqueness as this brick's remainder).

**Status: FULL — all four clauses closed by proof, K-PHI-4
honored.** No census claim rests on any machine rank computation.

**Artifact:** `lean/ThetLogos/IcosidodecaCensus.lean` — strict
29, defs 14 (in the memo's 25–45 band). Verified by the
coordinator in the main tree (build green, 1806 jobs); headlines
on exactly `[propext, Classical.choice, Quot.sound]`, pure-decide
incidence lemmas on cleaner subsets.

## The census, as proved

1. **ker ∂₂ = ℚ • (1,…,1)** (`ker_d2_eq_span`) — coefficient
   propagation over the connected dual graph: at each non-root
   face's BFS witness edge the kernel equation reduces to
   exactly two terms with opposite nonzero signs (using C2's
   landed signed-sum fact), forcing the coefficient to equal its
   BFS parent's; induction on depth reaches face 0. Reverse
   inclusion is C2's relation, cited.
2. **rank ∂₂ = 31** (`finrank_range_d2`) — rank-nullity
   (finrank C₂ = 32, ker finrank 1).
3. **rank ∂₁ = 29** (`finrank_range_d1`) — ker ∂₁ᵀ = constants
   on vertices by the same propagation over the 1-skeleton;
   rank-nullity gives rank ∂₁ᵀ = 29; `Matrix.rank_transpose`
   moves it back. Corollary: finrank ker ∂₁ = 31.
4. **Homology (1, 0, 1)** (`icosidodeca_census`) — in the model's
   own terms: H₂ as finrank ker ∂₂ = 1; H₁ as exactness
   ker ∂₁ = range ∂₂ (C1's inclusion + finrank equality 31 = 31,
   so the quotient has finrank 0); H₀ as the quotient finrank
   `finrank (C₀ ⧸ range ∂₁) = 1`.

**K-PHI-4 compliance, on the record:** the only `decide` proofs
in the module are finite incidence facts over the explicit
tables (BFS parent tables, witness-edge sign/nonvanishing facts)
— the C1/C2 pattern. Every kernel, rank, and homology statement
is closed by propagation and rank-nullity arguments only. The
probe's certified values (BR1-010) are thereby promoted to T1 by
proof, exactly as the salvage line registered.

## The line, closed

PHI-C is COMPLETE: C0 FULL (model), C1 FULL (chain identity),
C2 PARTIAL-then-completed (independence + relation; uniqueness
discharged here), C3 FULL (census). All polyhedron-only, under
the salvage label: T1 about the icosidodecahedron's chain
complex, zero NCG content, not a promotion of the mnemonic. The
bridge form stays killed at scoping (K-PHI-1/2/3).

## Fences

NO CLAIM — no Millennium problem is claimed solved or advanced;
no dial moves.

**Census after landing: 11,022 strict / 11,185 total / 375 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
