# Axiom Tet — Partner Sector landing dossier (2026-11-03)

**Brick:** THE PARTNER SECTOR — finite supersymmetry of the Axiom Zero
model. Commissioned by Jeff 2026-11-03 02:05 EST ("run it"), fired on
the Axiom Tet brick's FULL landing. Scoping:
`~/workspace/your_files/axiom-zero-supersymmetry-scoping-2026-11-03.md`
(pins SP-0..SP-5 frozen there).

**VERDICT: PARTIAL at full rank** — the pre-named respectable shape.
SP-0 through SP-4 land FULL at T1 (kernel-checked Lean, zero sorrys,
axioms inside the fence). **K-SP-ISO fired:** SP-5 (nonzero spectra of
the two sector Hamiltonians coincide with multiplicities) was not
proved; it is named OPEN below, not smoothed over. The index stands
without isospectrality, exactly as the kill registration priced it.

**Module:** `lean/ThetLogos/AxiomTetPartner.lean` (imports
`ThetLogos.AxiomTet`), built in the isolated worktree
`~/workspace/thet-logos-partner` on branch `partner-sector-lane`
(branched from `axiom-tet-lane`). Strict count **51** (theorem/lemma
at column 0, comment-stripped, house rule). Targeted build
`lake build ThetLogos.AxiomTetPartner` green, warning-clean.
`#print axioms` on all nine headlines (`supercharge_sq`,
`adjoint_identity`, `vertex_energy`, `edge_energy`,
`ker_vertexHam_eq`, `finrank_ker_vertexHam`, `ker_edgeHam_eq`,
`finrank_ker_edgeHam_add`, `index_eq`): each depends on exactly
{propext, Classical.choice, Quot.sound} — inside the fence, no
sorryAx. T2 sanity script `python/axiom_tet_partner.py` exit 0 (see
below). NO CLAIM. Dials 0/4.

## The construction (one paragraph)

For one finite web (a `SimpleGraph` on a `Fintype V`) with positive
per-edge need weights `w`, AxiomTet supplies the break energy. This
module builds the signed difference operator `d` (edge functions on
the subtype `↥G.edgeSet`; orientation fixed once: tail = min, head =
max under an ambient `LinearOrder V`), its transpose `dᵀ` (the
divergence), the root weight `√W` as a linear equivalence of the edge
sector, and the weighted pair `D = √W ∘ d`, `Dᵀ = dᵀ ∘ √W`. The two
Hamiltonians are the operator squares `H_v = DᵀD` (vertex sector) and
`H_e = DDᵀ` (edge sector); the supercharge `Q` on the product
(vertex ⊕ edge) swaps the sectors. One `d` thereby organizes both
sectors, exactly the partner structure whose absence the Axiom Tet
dossier recorded.

## Pins vs outcomes

| Pin | Outcome | Where |
|---|---|---|
| SP-0 supercharge: Q odd, swaps sectors, Q² = H_v ⊕ H_e | **FULL (T1)** | `supercharge_sq`, `supercharge_fst`, `supercharge_snd`. Q is realized on the product module `(V → ℝ) × (↥G.edgeSet → ℝ)` — the direct sum in product form; the grading is the sector swap, recorded in the module header. |
| SP-1 both squares: ⟨f, H_v f⟩ = breakEnergy; ⟨g, H_e g⟩ a sum of weighted squares | **FULL (T1)** | `vertex_energy` (the energy form Σ f·(H_v f) EQUALS `AxiomTet.breakEnergy` — consumed, not re-proved); `edge_energy` (= Σ_v (Dᵀg v)²). Both rest on one adjoint identity (`adjoint_identity`: Σ_v f v·(dᵀg v) = Σ_e (df)(e)·g(e)), proved by splitting the ordered-edge sum into its two halves and reindexing — no inner-product machinery (this Mathlib's plain function types carry none; recorded in the module header). |
| SP-2 vertex zero modes = constants per component | **FULL (T1)** | `ker_vertexHam_eq`: ker H_v = the per-component-constants submodule, consuming AZ-2W through `vertex_energy`; `finrank_ker_vertexHam`: its finrank is `Nat.card G.ConnectedComponent`. |
| SP-3 edge zero modes = circulations; dimension = \|E\| − \|V\| + #components | **FULL (T1)**, with one honesty note | `ker_edgeHam_eq`: ker H_e = ker Dᵀ EXACTLY. `ker_wAdjDiff_iff`: ker Dᵀ is the weighted circulation space ({g : √W • g is divergence-free}). `finrank_ker_edgeHam_add`: finrank ker H_e + \|V\| = #edges + #components. NOTE, plainly: the scoping's shorthand "ker dᵀ" names the kernel of the adjoint of the difference operator; the operator this brick is about is the weighted `D`, and `Dᵀ` is its adjoint — ker H_e = ker Dᵀ is the exact statement, and the cyclomatic dimension formula is the same. No unweighted-adjoint kernel is asserted anywhere. |
| SP-4 the index: finrank ker H_v − finrank ker H_e = \|V\| − \|E\| | **FULL (T1)** | `index_eq`, stated in addition form — `finrank ker H_v + #edges = finrank ker H_e + #vertices` — chosen because ℕ-subtraction would truncate and ℤ-casts would add a conversion layer; the addition form is the provable content with nothing hidden in a cast. Proof route: rank(Dᵀ) = rank(D) (entry lemma `adjDiff_single`, matrix transpose, `Matrix.rank_transpose`; rank(D) = rank(d) and range(Dᵀ) = range(dᵀ) via the root-weight equivalence), then rank-nullity on both operators and arithmetic (`omega`). |
| SP-5 STRETCH: nonzero spectra of H_v, H_e coincide with multiplicities | **OPEN — K-SP-ISO fired** | Not attempted past the priced point: the eigenspace-intertwining route (D maps nonzero eigenspaces of H_v isomorphically onto those of H_e) needs spectral machinery for self-adjoint operators on plain function spaces that this Mathlib does not provide off the shelf (no inner product instances on `ι → ℝ` as bare types; the spectral theorem would have to be assembled via matrices/eigenspaces by hand). Priced in the scoping at L as its own brick; it remains exactly that: a separate, scoped, unfired brick. The T2 script observes the agreement numerically on all four test webs — T2 evidence of the phenomenon, NOT a proof, and not a softening of this verdict. |

## Fences and discharges

- **K-SP-ORIENT: discharged.** One orientation is fixed explicitly
  (tail = min, head = max under the ambient linear order) — the
  module does not pretend the operator form is orientation-free.
  The choice is inert for every pinned statement: under any per-edge
  sign flip `d ↦ S∘d` (S the diagonal sign on the edge sector),
  `H_v = (S∘d)ᵀ(S∘d) = dᵀd` and `H_e = (S∘d)(S∘d)ᵀ = ddᵀ` are
  literally the same operators, and SP-1's vertex side lands on
  `breakEnergy`, which never mentions orientation. (Algebra fact,
  recorded here; the module never needs the flip because its pins
  are proved for the one fixed `d`.)
- **Naming fence (on the face, per the scoping):** this is FINITE
  SUPERSYMMETRIC QUANTUM MECHANICS ON A GRAPH — one finite web, two
  finite-dimensional sectors, a grading swap, and an index. The word
  "supersymmetry" names this finite QM structure and nothing else:
  no superpartners of particles, no physics claim, no Standard Model
  contact. "Fermionic" appears only as a grading analogy for the
  edge sector, if at all. Nothing here touches the dials: **NO
  CLAIM, dials 0/4.**
- **Weights discipline:** the module splits roles exactly as
  AxiomTet fixed them — unweighted `d` carries the combinatorics;
  `w` enters only as `√W` post-composition. Positivity of `w` is a
  hypothesis everywhere it is used (it is what makes `√W` an
  equivalence and what discharges `ker D = ker d`).

## T2 sanity (verifies nothing about the theorems)

`python/axiom_tet_partner.py`, exit 0. On C21 (21/21, 1 component),
a 9-vertex tree (9/8), a 4×4 grid (16/24), and two disjoint
triangles plus an isolated vertex (7/6, 3 components), with random
positive weights: vertex zero modes = #components, edge zero modes
= |E| − |V| + #components, index = |V| − |E|, all matching. The
script also reports the NONZERO spectra of the two sectors agreeing
numerically on all four webs — labeled in the script itself as the
SP-5 phenomenon, T2 only, with SP-5 open at T1.

## Systemic-unification watch (a rhyme logged, NOT a claim)

Per Jeff's 2026-11-02 watch instruction: the same shape recurs
again. One operator `d` organizes three facts that a single index
theorem now counts together — unity (ker `D` = the constants per
component, the Axiom Zero content), cycles (ker `Dᵀ` = the
circulations), and their difference forced to be the Euler
characteristic |V| − |E|. This rhymes with the kernel-equals-
constants pattern already at T1 in the Bridge material and in
Mirror-21 (zero mode = constants, derived), and with Orthogonal
Pantoreality's joint kernel. Logged as a recurrence for the watch;
no unifying theorem is stated or claimed here, and none of the
rhymes moves any dial.

## Census effect (for the parent ceremony; not asserted here)

Uncommitted lane work: this module adds 51 strict / 1 module on top
of the Axiom Tet lane state it branched from (whose own +15 / +1 is
likewise uncommitted). Parent re-derives all figures at integration;
nothing in this dossier is a public number.

## Fence-admission candidates (for the parent ceremony)

1. `ThetLogos.supercharge_sq` — SP-0, Q² = H_v ⊕ H_e.
2. `ThetLogos.vertex_energy` — SP-1, the vertex energy IS the
   AxiomTet break energy.
3. `ThetLogos.index_eq` — SP-4, the index theorem (headline).

## CEREMONY — Brick 1 close, 2026-11-03 (parent ceremony, main tree)

This brick's ceremony ran as part of the joint Brick 1 close (Axiom Tet + Partner Sector + Orthogonal Pantoreality) after Jeff lifted all holds ("back to work open the gates and lift the holds").

- Main-tree build: full build green; targeted build of the staged modules green; Python companion re-run exit 0.
- **Step B stop, on the record:** the ceremony first STOPPED at the axiom-fence step. The official runner reported 41/47 — this brick's three headlines (`supercharge_sq`, `vertex_energy`, `index_eq`) among the six declarations "NOT REPORTED (unknown constant)". Root cause: the registry (`lean/scripts/axiom-fence.txt`) carried the six AxiomTet/AxiomTetPartner declarations under `import ThetLogos.MirrorTwentyOneOrthogonalSpectral` with NO `import ThetLogos.AxiomTet` and NO `import ThetLogos.AxiomTetPartner` lines — a registry structural omission, not an axiom failure and not a missing declaration. With the registry untouched, a scratch check importing the two modules verified all six declarations exist and pass (this brick's three on exactly {propext, Classical.choice, Quot.sound}). The parent authorized the exact repair: the two import lines added above their declaration groups, registry edit landing in the SAME commit as the modules (the standing CI lesson).
- Fence after repair: **47/47 PASS** — every registered headline on exactly {propext, Classical.choice, Quot.sound}, no sorryAx anywhere.
- Census effect of this brick (recount, method of record): **+51 strict / +1 module**. Joint ceremony census: **12,875 strict / 13,401 total / 466 modules**, zero sorrys. README updated to the joint figures; ledger record `axiom-tet-partner-sector` at status **partial** (validator PASS, 11 records).
- Commit: the Brick 1 ceremony commit of 2026-11-03 — this dossier ships inside it; the hash is recorded in the pipeline log's Brick 1 completion entry.

**Verdict stands at full rank: PARTIAL — SP-0..SP-4 FULL at T1; K-SP-ISO fired; SP-5 open, unfired. NO CLAIM; dials 0/4.**
