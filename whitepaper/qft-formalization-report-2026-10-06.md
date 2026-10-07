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

---

## Second wave (2026-10-07): coassociativity falls, antipode defined

**File:** `lean/ThetLogos/Renormalization.lean` — extended from 30 to 59
theorems/defs, builds green, zero sorrys, axioms still
`[propext, Classical.choice, Quot.sound]`.

### Target 1 — Coassociativity: PROVED (T1)

**Theorem:** `coassociativity_theorem : coassociativity` — the T5-pinned
`coassociativity : Prop` from the first wave is now a theorem. Both
parenthesizations `(Δ⊗id)∘Δ` and `(id⊗Δ)∘Δ` agree as multisets of
forest-triples. With counity (both sides, first wave), the Connes–Kreimer
**bialgebra axioms are complete** at the combinatorial (planar) level.

**Method:** the standard cocycle-induction proof, following the size-bound
mutual-induction pattern from `counity_left`:
- `forestCoprod_append`: the forest coproduct is multiplicative
  (`Δ̂(F++G) = Δ̂(F)·Δ̂(G)`), from the `foldr` definition. Key helper:
  `bind_append_reindex` (pushing singleton-appends through a product of binds).
- `bind_swap`: independent `Multiset.bind`s commute.
- `forestTripleL_cons` / `forestTripleR_cons`: forest-level triple
  coproducts split as products over cons (via multiplicativity + swap).
- `forest_coassoc_of_tree`: forest-level coassociativity by list induction.
- `tripleL_node` / `tripleR_node`: both sides expand to a common
  `C₁ + C₂` plus `(forestTripleL/R ts).map` under third-component grafting.
  Helpers `tripleL_rest`, `tripleR_rest`, `tripleR_deep` handle the
  reindexing; `forestCoprod_singleton` bridges forest/tree coproducts.
- `coassoc_aux`: strong induction on the size bound closes it.

**What this means:** the "every term survives" obstruction from the first
wave is resolved — not by a cut-bijection (the suggested unblocker), but by
the cocycle induction, which achieves the same end via the recursive
structure. The cut description remains valuable future work but is no longer
blocking.

### Target 2 — Antipode: DEFINED (termination resolved), axiom STATED

**Termination (sub-problem a): RESOLVED.** The report's obstruction was
"Lean can't see termination through `Multiset.bind` over `forestCoprod`."
Resolved via size bounds + bounded recursion:
- `forest_size_bound_of_tree` / `tree_size_bound_aux` /
  `coprod_pruned_bound`: pruned forests in coproduct terms are size-bounded;
  trees in `P` (for `(P,R) ∈ forestCoprod ts`) are strictly smaller than
  `.node ts`. Proved by the same mutual-induction pattern.
- `antipodeTree` / `antipodeForest` (mutual, `noncomputable`): defined by
  recursion on the size bound `n`, not by well-founded recursion through
  the multiset. The formula `S(.node ts) = -Σ_{(P,R)∈Δ̂(ts)} S(P)·[node R]`
  (the `([],ts)` term contributes `[t]`, so no separate `-[t]` is needed —
  correcting the report's formula which double-counted).
- Sum over `Multiset.toList` with a classical `DecidableEq` instance
  (already in the axiom footprint).

**Convolution algebra (sub-problem b): SET UP.** `ssumAdd`/`ssumNeg`/
`ssumMul`/`ssumOne` on `SSum = List (ℤ × Forest)`; `ssumMul` is the
bilinear convolution `[(c₁,F₁)]*[(c₂,F₂)] = [(c₁*c₂, F₁++F₂)]`.

**Axiom: STATED (T5).** `antipodeAxiom : Prop` with `antipodeAxiomSum`
(formalizing `m(S⊗id)Δ = ηε` as a toList-fold sum). **Proof open.**
Precise obstruction: the axiom follows from the definition by expanding
`treeCoprod t` via the cocycle and matching the definitional fold against
the axiom's fold — a routine but lengthy reindexing (the two folds traverse
the same multiset in different orders; needs a `toList`-fold congruence
lemma). No mathematical obstacle; purely formalization work.

### Targets 3–4 (van Suijlekom Hopf ideal, Birkhoff): SCOPED, not attempted

- **Target 3:** The rungs map rates this "feasible, moderate" but notes
  "the hard part is formalizing Feynman-graph combinatorics with enough
  fidelity." Our trees are the *skeleton* of the graph Hopf algebra, but
  the Slavnov–Taylor identities are statements about *graphs* (with
  external structure, insertion places). Formalizing the theorem needs the
  graph combinatorics first. The abstract Hopf-ideal *definition* (ideal
  `I` with `Δ(I) ⊆ I⊗H + H⊗I`) is statable at our level, but the
  *theorem* is not. Precise next step: a `FeynmanGraph` type with the
  Connes–Kreimer coproduct (subgraph contraction), then the ST ideal.
- **Target 4 (Birkhoff):** Needs characters (`H → A` algebra maps),
  convolution, and Rota–Baxter operators — substantial algebraic
  infrastructure beyond the current combinatorial level. Downstream of a
  full algebra packaging (the file notes "bialgebra packaging is future
  work").

### Updated ledger

| Item | Status | Axioms |
|---|---|---|
| Coproduct + B₊ + examples | PROVED | propext, Classical.choice, Quot.sound |
| Right counity | PROVED | same |
| Left counity | PROVED | same |
| **Coassociativity** | **PROVED (second wave)** | same |
| Antipode definition + termination | **DONE (second wave)** | same |
| Antipode axiom | STATED (T5) | — |
| van Suijlekom Hopf ideal | SCOPED (needs graphs) | — |
| Birkhoff decomposition | SCOPED (needs algebra packaging) | — |
| Wightman T1 (light cone) | PROVED | same |
| Wightman axioms + existence | PINNED (T5) | — |

**Zero `sorry`s.** **No physical claims.** Nothing pushed; commit is the
parent's call.
