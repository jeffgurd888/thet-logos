# QFT Formalization Report — 2026-10-06

**Beachhead run:** the most formalizable Rung-2 target (Connes–Kreimer Hopf
algebra) + the Rung-3 pinned statement (Wightman axioms).
**Rule:** zero `sorry`s in proved claims; `#print axioms` on every theorem;
no physical predictions. Partial progress is a result.

---

## Target 1 (primary): Connes–Kreimer Hopf algebra of rooted trees

**File:** `lean/ThetLogos/Renormalization.lean` — builds green
(`lake build ThetLogos.Renormalization`, 3198 jobs).

### PROVED (T1, zero sorrys, axioms `[propext, Classical.choice, Quot.sound]`)

**Definitions.**
- `RKTree`: planar rooted trees (`inductive RKTree | node : List RKTree → RKTree`).
  Scoping: this is the noncommutative Connes–Kreimer–Foissy algebra; the
  commutative quotient is future work. `deriving DecidableEq` fails for the
  nested inductive — worked around with Bool `List.isEmpty` (no equality needed).
- `graft` (B₊), `treeCoprod`/`forestCoprod` (coproduct via the B₊-cocycle
  recursion `Δ(B₊(F)) = B₊(F)⊗1 + (id⊗B₊)(Δ̂(F))`, implemented with
  `List.foldr` so termination is structural), `counit`,
  `collapseR`/`collapseL` (the `(id⊗ε)`/`(ε⊗id)` contractions as multiset maps).

**Coproduct computations.**
- `treeCoprod_single`: Δ(•) = •⊗1 + 1⊗• (primitivity).
- `treeCoprod_chain2`: Δ(𝔩₂) = 𝔩₂⊗1 + •⊗• + 1⊗𝔩₂.
- `treeCoprod_V`: Δ(V) = (V,[]) + (••,•) + (•,𝔩₂) + (•,𝔩₂) + ([],V) —
  the two single-cut terms coincide (multiset with multiplicity 2).
- `treeCoprod_node`: the cocycle unfolding lemma.

**Counity — both sides, the headline result.**
- `counity_right`: `(id⊗ε)(Δ(t)) = t`. Proof: the `t⊗1` term is the unique
  term with empty second component; the rest dies under collapse. No induction.
- `counity_left`: `(ε⊗id)(Δ(t)) = t`. Proof: strong induction on a size
  bound. The hard direction — the `1⊗t` term is *not* syntactically isolated
  by the cocycle, so the proof goes through a forest-level lemma
  (`forest_collapseL_of_tree`, by list induction, taking the tree statement
  as hypothesis) plus a reindexing lemma (`collapseL_cocycle`: the rest
  reindexes through the grafting map). Key algebraic steps use
  `Multiset.bind_assoc`, `Multiset.singleton_bind`, `Multiset.map_bind`,
  and an `isEmpty`-over-append split.
- Supporting: `collapseR_add`, `collapseR_rest`, `forestCoprod_nil/cons`,
  `treeSize_pos`, `isEmpty_append_eq`, `collapse_if_split`.

### BLOCKED (precise obstructions)

- **Coassociativity** (`coassociativity : Prop`, `tripleL`/`tripleR` defined,
  T5): needs a mutual tree/forest induction bijecting two-step cuts between
  the two parenthesizations. Unlike counity (collapse kills all but one
  term), every term survives and must be matched. Requires a "subforest"
  order with chain characterization + iterated-bind reindexing lemmas.
  Unblocker: an explicit admissible-cut description of `treeCoprod`.
- **Antipode** (`antipodeSchema : Prop`, `SSum` defined, T5): the recursion
  `S(.node ts) = -[t] − Σ S(P)·[node R]` needs no filtering (cocycle
  isolates `t⊗1`), but Lean can't see termination through
  `Multiset.bind` over `forestCoprod`; needs manual well-founded recursion
  + the signed-sum convolution algebra + the cut analysis from above.
  Unblockers: `DecidableEq RKTree` (attempted via mutual instances —
  elaboration failed), the cut description.

---

## Target 2 (secondary): Wightman axioms, pinned statement

**File:** `lean/ThetLogos/WightmanAxioms.lean` — builds green. Claims only
the statement; no interacting QFT is constructed (none exists in
mathematics, per the rungs map).

### PROVED (T1)
- `minkowskiInner_nonneg_of_mem`: reverse Cauchy–Schwarz — the Minkowski
  product of two forward-light-cone vectors is nonnegative (via spatial
  Cauchy–Schwarz + `Real.sqrt_le_sqrt`). Axioms: `[propext,
  Classical.choice, Quot.sound]`.
- `forwardLightCone_convexCone`: the closed forward light cone (the
  geometric object in the spectrum condition W3) is a `ConvexCone`
  (construction, zero sorrys).

### PINNED (T5, honestly opaque)
- `WightmanAxioms`: the six axioms (W0 vacuum through W5 cyclicity, plus
  nontriviality) as labeled opaque `Prop` fields — Mathlib 2026 has no
  Schwartz distributions, no operator-valued distributions, no Poincaré
  representation theory for quantum fields (dependency ledger in file).
- `InteractingWightmanQFT`, `WightmanExistence`: the open existence problem,
  pinned so partial progress is measured against a fixed target.

---

## Ledger

| Item | Status | Axioms |
|---|---|---|
| Coproduct + B₊ + examples (•, 𝔩₂, V) | PROVED | propext, Classical.choice, Quot.sound |
| Right counity | PROVED | same |
| **Left counity** | **PROVED** | same |
| Coassociativity | BLOCKED (cut-bijection) | — |
| Antipode | BLOCKED (termination + convolution) | — |
| Wightman T1 (light cone) | PROVED | same |
| Wightman axioms + existence problem | PINNED (T5) | — |

**Zero `sorry`s** in either file (one docstring mentions the word only).
**No physical claims** anywhere. Nothing pushed; commit is the parent's call.
