# Ternary Substrate Rebuild — TritGrading (2026-10-15)

**Verdict: STANDS.** The salvageable ideas from the killed "Theta
Framework" paste — balanced ternary substrate, ℤ₃ grading, graded
commutator facts, the squared-commutator trace bound — are rebuilt from
scratch to thet-logos standard in `lean/ThetLogos/TritGrading.lean`
(350 lines; import wired into `lean/ThetLogos.lean`). Full `lake build`
green (3325 jobs). Zero sorrys. Axiom footprint on all headline results:
`[propext, Classical.choice, Quot.sound]` only — no `sorryAx`, no new
axioms. (`Trit.add_assoc` depends on no axioms at all.)

**Tier: this is T1 background algebra. It is not mass-gap content, not a
Chern character, not physics.** Details below; the file header carries
the same ledger.

## What was built (all T1)

### §1. Trit arithmetic, complete
`Trit` (inductive: `neg | zero | pos`) with `Fintype` and `DecidableEq`
instances — the instances whose absence killed the paste's headline
proof. `Trit.toInt` (`neg ↦ -1, zero ↦ 0, pos ↦ 1`), `Trit.negate`,
`Trit.add` (the pasted table, which the gauntlet verified *is* ℤ₃).
Full abelian-group laws proved by case analysis: `Trit.add_assoc`,
`Trit.add_comm`, `Trit.zero_add`, `Trit.add_zero`, `Trit.neg_add_cancel`,
`Trit.add_neg_cancel`, `Trit.neg_neg`, `Trit.toInt_neg`. The ℤ₃ claim is
made precise two ways: `Trit.toInt_add` / `Trit.toInt_add_modEq`
(`toInt (a + b) ≡ toInt a + toInt b [ZMOD 3]`) and the bundled
`Trit.addEquivZMod3 : Trit ≃+ ZMod 3`, via `Trit.toZMod3`,
`Trit.toZMod3_add`, `Trit.toZMod3_injective`, `Trit.ofZMod3` and its two
inverse laws.

### §2. Commutator facts, honestly named
`commutator A B := A * B - B * A` (not "curvature"); `ad A X := A * X - X * A`
(the adjoint action, not a "covariant derivative" — there is no
differential term). Conjugation covariance of both, re-derived cleanly
in project Mathlib: `conj_mul_conj`, `commutator_conj`, `ad_conj`.
Plus `commutator_self`, `commutator_antisymm`, and
`commutator_conjTranspose` (commutator of Hermitians is skew-Hermitian).

### §3. A real grading structure
`TritGrading ι`: each grade's homogeneous component is a
`Submodule ℂ (Matrix ι ι ℂ)`; the only axiom is `mul_mem` (products land
in the summed grade). The paste's predicate-only grading admitted the
degenerate model `IsGraded := fun _ _ => True`, which is why its graded
theorems did not follow. Here they do: `TritGrading.sub_mem`
(subtraction closure, inherited from the submodule),
`TritGrading.commutator_mem` (`[A, B]` is homogeneous of grade
`g₁ + g₂`), `TritGrading.ad_mem` (the adjoint action of a grade-`zero`
element preserves every grade) — exactly the two consequences the
paste's extension had to `sorry`.

### §4. Block-offset instance
`blockComponent g`: the submodule of matrices over `Trit × n` supported
where column block = row block + `g`; `mem_blockComponent`
(characterization, `Iff.rfl`); `blockGrading : TritGrading (Trit × n)`,
with the multiplication rule proved by the entry-sum argument (each
summand vanishes either by the first factor's offset or the second's,
using `Trit.add_assoc`). This is the paste's headline Part IV claim,
proved against a definition strong enough to carry it.

### §5. The squared-commutator trace bound, proved
`trace_conjTranspose_mul_self_re_nonneg`: `trace (Cᴴ * C)` equals the
real number `∑ i j, normSq (C j i)` (entrywise via `Complex.mul_conj`),
hence has non-negative real part — it is the Frobenius norm squared.
`trace_commutator_sq_nonpos`: for Hermitian `A B`,
`(trace (commutator A B * commutator A B)).re ≤ 0`, via
skew-Hermiticity of the commutator and `C * C = -(Cᴴ * C)`.
The word "Chern" appears nowhere in the file: `trace [A,B]²` is not a
Chern character (no bundle, no cycle, no exponential series, no
normalization), and it is not named as one.

## Connection audit (honest)

Does this ℤ₃-graded algebra connect to the corpus's existing ternary
structures? Read before claiming: `TRO.lean`, `XYZTripotents.lean`,
`Mod9Triad.lean`, and the spectral-triple files. Findings:

- The corpus's "ternary" is the **TRO product** `⟨a, b, c⟩ = a · star b · c`
  (`ThetLogos.ternary`, `ternaryMat`) — a 3-*ary operation*. That is a
  different notion of "three" from a cyclic *grading*: the TRO product
  assigns no grades to elements, and nothing in the corpus grades the
  TRO or its tripotents (`XYZTripotents`: `{{e, e, e}} = e`) by ℤ₃.
  Tripotents do not carry a natural ℤ₃ grading in this corpus, and none
  is asserted here.
- The corpus's actual operator-algebra gradings are **ℤ₂** (the
  spectral triple grading `γ_F`; Dirac operators are grading-*odd*).
  No ℤ₃ grading of any operator algebra existed in the corpus before
  this file.
- The one genuine arithmetic adjacency: `Mod9Triad`'s triad
  `{0, 3, 6} ⊆ ZMod 9` is the unique order-3 subgroup of `ZMod 9`, hence
  additively isomorphic to `ZMod 3 ≅ Trit`. That is a fact about ℤ/9
  arithmetic, already T1 in the corpus; `Mod9Triad`'s own honesty
  ledger already labels its further mappings interpretive (T5). It is
  not a grading of anything, and no bridge is built on it here.

**Conclusion: the substrate stands alone as background algebra.** No
forced bridges. If a ℤ₃ grading is ever *derived* inside the corpus's
physics-facing structures, §3–§4 are the correct formal home for it;
until then there is nothing to connect, and this dossier says so.

## Excluded, deliberately

- **The Part II energy toy** (the renamed ACME toy: `Δ > 0` assumed as a
  structure field, energy *defined* as `Δ · v1²`): excluded. The gap
  there is an input, not a derivation — same verdict as the original
  toy audit. It adds nothing.
- **Hamiltonian ODE material** (Schrödinger/von Neumann evolution,
  "Hamiltonian preserves unitarity"): out of scope, priced here: the
  paste's own statements did not follow from its definitions (its
  evolution predicate carried no differentiability hypothesis, and
  Mathlib's `deriv` is 0 off the differentiable locus), and honest
  proofs need ODE theory (Picard–Lindelöf / Grönwall) that is a
  separate project. Not built; not claimed.
- **"Temporal evolution" / "topological" language**: nothing in the
  file defines or proves anything temporal or topological; the words
  do not appear except in this exclusion note.

## What the grading buys the program

One honest paragraph: today, nothing physical. What it buys is
hygiene and readiness. It removes a wrong object from the program's
orbit — a non-compiling, degenerate-model grading whose three sorrys
concealed underivable statements — and replaces it with a correct,
reusable gadget: any future three-fold cyclic sector decomposition of
a matrix algebra (should one ever be derived, e.g. from a genuine ℤ₃
symmetry of some `D_F`) can now be stated in one line and gets
commutator closure, adjoint-action closure, and subtraction closure
for free, with the trace bound as a citable lemma. The bedrock value
is that the foundation stone is now actually a stone: definitions
strong enough that the natural theorems *follow*, checked by the
machine, with names that say exactly what the objects are.
