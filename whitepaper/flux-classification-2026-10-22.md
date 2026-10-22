# FluxClassification — the modular-flux classification: STANDS WHOLE (T1)

**Date:** 2026-10-22 · **Module:** `lean/ThetLogos/FluxClassification.lean`
(namespace `ThetLogos.FluxClassification`) · **Commission:** Jeff,
2026-10-22 ("build them both") — roadmap item A, nominated as the
first stress test in item D of `your_files/roadmap-answers-2026-10-22.md`.

## Verdict

**STANDS WHOLE (T1).** The classification is proved in full, in both
commissioned forms, on the corpus's actual constructions — with
**fewer hypotheses than the target allowed**. The pre-registered kill
criterion (close PARTIAL if the iff needs hypotheses beyond finite +
Hermitian + the construction as built) **did not fire**.

15 strict theorem/lemma declarations, 1 def, 0 `@[simp]`, 0 sorry,
0 admits, 0 axiom declarations. Parent-verified: candidate
byte-identical to the built scratch source (md5
`f7d5d7baa027b8ca44fbcb696ee7d54b`); own comment-stripped scan
15/1/0/0/0; own recompile of the candidate exit 0 with an empty log;
in-tree `lake build ThetLogos.FluxClassification` green on the exact
shipped text (3,584 jobs, `.olean` present); `#print axioms` on all
15 theorems — exactly `[propext, Classical.choice, Quot.sound]`.

## The statement

With the corpus's own objects — `modularFlux K D = Complex.I • (K * D
− D * K)` and the built modular Hamiltonian `diagModularK w`
(`ModularTime.lean`, K = −ln ρ for `ρ = diagState w`):

- **Engine** (`modularFlux_diagonal_apply`): for diagonal K, entry by
  entry, `(modularFlux (diagonal k) D) i j = I • (k i − k j) • D i j`.
  The flux entry at a cross-sector position is exactly the sector gap
  times the D entry there.
- **Diagonal classification** (`classification_diagonal`): for any
  diagonal `k` and **any** D,
  `modularFlux (diagonal k) D = 0 ↔ sectorBlockDiagonal k D`
  (D i j = 0 wherever k i ≠ k j).
- **The built K** (`classification_diagModularK`): at
  `K = diagModularK w`, any real weights, any D:
  `modularFlux (diagModularK w) D = 0 ↔ ∀ i j, log (w i) ≠ log (w j)
  → D i j = 0`. **No positivity on w.** At positive weights
  (`classification_diagModularK_of_pos`) the sectors are the weight
  level sets themselves.
- **General Hermitian K** (`classification_hermitian`): for K
  Hermitian, flux = 0 iff `star U * D * U` is sector-block-diagonal in
  K's eigenbasis (U the eigenvector unitary), via
  HermitianReduction's spectral form.
- **Preservation forms:** `classification_diagonal_preserves` (flux =
  0 iff D maps every sector-supported vector to a sector-supported
  vector); `flux_eq_zero_preserves_eigenspace` — for **arbitrary** K,
  no Hermiticity, vanishing flux implies D preserves every eigenspace
  of K, basis-free.
- Corollaries: constant weights ⇒ flux = 0 for all D
  (`flux_diagModularK_eq_zero_of_const`); one nonzero cross-sector
  entry ⇒ flux ≠ 0 (`flux_diagModularK_ne_zero_of_entry`, the
  criterion form of `exists_activeDriver` /
  `interSectoral_flux_nonzero`); at positive weights, flux = 0 ⇒ the
  built flow is trivial (`diagFlow_eq_of_flux_eq_zero`).

## Strengthening, recorded not silent

The commissioned target allowed Hermitian D. The proof needs **no
hypothesis on D at all** — in no part — so the headlines are stated
for arbitrary D; the Hermitian-D case is a special case (where the
flux is additionally self-adjoint, `modularFlux_selfAdjoint`).

## Fences, on the face

- Finite level only; no continuum or functional-calculus claim beyond
  the spectral theorem already in the corpus.
- For non-positive weights the sectors are **log-level sets**, not
  weight level sets (Real.log identifies w and −w and sends 0 to 0) —
  that is `diagModularK` as built, and headline 2 states it in the
  log form so the fence sits on the theorem.
- The Hermitian form is an **eigenbasis statement** (entries of
  `star U * D * U`), per HermitianReduction's remainder R1; no
  original-basis entry claim is made or implied.

## Census effect

Program census moves 3,507 → **3,522 strict** (3,547 → **3,562**
attribute-inclusive), 125 → **126 counted modules**.

## What this closes

Roadmap challenge 1 is answered: the vanishing side (proved before,
several ways), the non-vanishing side (witnesses, proved before), and
now the iff itself — φ = 0 exactly when D has no entries between
distinct-weight sectors. The classification is the natural input to
the (uncommissioned, parked) item-B numerical exhibit.
