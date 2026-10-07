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

---

## Rung 3 (constructive QFT) — beachhead run, 2026-10-07

**Context:** Rung 2 (renormalization) is complete at the bialgebra level.
Rung 3 is the field's wall: no interacting 4D Wightman QFT has ever been
constructed (undisputed; it is the Clay problem's difficulty). The beachhead
is therefore the FREE field — the one QFT that provably exists
(Streater–Wightman 1964) — plus the Haag–Kastler and Osterwalder–Schrader
frameworks pinned as statements.

### Target 1 (primary): the free scalar field — algebraic core

**File:** `lean/ThetLogos/FreeField.lean` — builds green
(`lake build ThetLogos.FreeField`), full project build green (3324 jobs).

**Infrastructure survey (Mathlib 2026) — what exists and what doesn't:**
- HAS: `SymmetricAlgebra` (bosonic Fock, algebraic) with universal
  property (`lift`), induction principle, augmentation map
  (`algebraMapInv`); `ExteriorAlgebra` (fermionic analogue);
  `CliffordAlgebra` contraction; Hilbert `ℓ²` spaces (`PiL2`, `l2Space`).
- LACKS: Fock inner product (the `n!`/permanent formula on `Sym(V)`);
  Schwartz distribution theory (`𝒮`, `𝒮'`); annihilation operators
  (need the inner product); unbounded-operator theory for fields;
  the mass shell `Hₘ⁺` with Lorentz-invariant measure as a ready object;
  second quantization functor `Γ`; Minlos' theorem / nuclear spaces.

### PROVED (T1, zero sorrys, axioms `[propext, Classical.choice, Quot.sound]`)

- `bosonicFock V := SymmetricAlgebra ℂ V` — the algebraic Fock space;
  `fockVacuum := 1`; `vacuumExp := SymmetricAlgebra.algebraMapInv`
  (the augmentation map as vacuum expectation functional).
- `onePoint_vanishes`: `⟨0| a†(v) |0⟩ = 0` — the 1-point function vanishes
  (`algebraMapInv_ι` read in field language).
- `twoPoint_algebraic_trivial`: the algebraic vacuum functional gives a
  *trivial* 2-point function (`⟨0|ι(v)ι(w)|0⟩ = 0`). This is the honest,
  checked location of the gap: the quantum 2-point function `⟪v,w⟫` lives
  entirely in the missing Fock inner product. Not a bug — a measurement.
- `create_commute`: `[a†(v), a†(w)] = 0` — creation operators commute
  (via `mul_left_comm` on the commutative symmetric algebra).
- `vacuum_cyclic`: `Algebra.adjoin ℂ (range (ι ℂ V)) = ⊤` — every Fock
  vector is a polynomial in creators applied to the vacuum. The algebraic
  shadow of Wightman W5, proved via `SymmetricAlgebra.induction`.

**Build note (honest):** two elaboration traps were hit and fixed, both
worth recording. (1) `SymmetricAlgebra.algebraMapInv` takes `R M`
*implicit* while `SymmetricAlgebra.ι` takes them *explicit* — the file's
`variable (R M : Type*)` line is misleading; `#check` is authoritative.
(2) The first `create_commute` attempt used `mul_comm` where the goal
needed `mul_left_comm` — the error surfaced as a spurious `sorryAx`
downstream, a reminder that axiom-footprint anomalies get investigated,
not ignored.

### Per-axiom ledger: free field vs. W0–W6

| Axiom | Verdict | Gap (infrastructure vs. mathematical) |
|---|---|---|
| W0 (Hilbert space) | BLOCKED | infrastructure: Fock inner product absent |
| W1 (fields as OVDs) | BLOCKED | infrastructure: no `𝒮'`; annihilation needs W0's inner product |
| W2 (Poincaré covariance) | BLOCKED | infrastructure: mass-shell `L²` + second quantization `Γ` |
| W3 (spectrum) | geometry T1 (in `WightmanAxioms.lean`); operator statement BLOCKED on W0/W1 | mixed |
| W4 (locality) | BLOCKED | infrastructure: full CCR needs annihilation; Pauli–Jordan `Δ` needs `𝒮'`; shadow `[create,create]=0` PROVED |
| W5 (vacuum cyclicity) | algebraic shadow PROVED (`vacuum_cyclic`); Hilbert density BLOCKED on W0 | mixed |
| W6 (clustering) | BLOCKED | infrastructure: explicit `Δ₊` + spacelike decay analysis |

### Target 2: Haag–Kastler axioms — PINNED (T5)

**File:** `lean/ThetLogos/HaagKastler.lean` — builds green.
`HaagKastlerAxioms` structure (net, isotony, locality, Poincaré covariance,
spectrum condition, vacuum, irreducibility — all opaque Props);
`InteractingHaagKastlerNet` / `HaagKastlerExistence` pinned (open problem).
One T1-adjacent contribution: `SpacelikeSeparated` defined directly from
the checked Minkowski inner product. Dependency ledger: HK avoids
distributions but needs C*-net machinery Mathlib lacks; neither framework
is formalizable past the statement.

### Target 3: Osterwalder–Schrader axioms + reconstruction — PINNED (T5)

**File:** `lean/ThetLogos/OsterwalderSchrader.lean` — builds green.
`OsterwalderSchraderAxioms` (E0–E4: temperedness, Euclidean covariance,
reflection positivity, symmetry, clustering — opaque Props);
`OSReconstruction : Prop` (OS ⇒ Wightman, proved 1975, not formalized —
analytic gap named: Bargmann–Hall–Wightman analytic continuation,
edge-of-the-wedge, no Mathlib infrastructure); `InteractingOSMeasure`
pinned (open). Noted honestly: even the *free* field's OS verification
needs Minlos' theorem + distribution kernels — T5 for now.

### Updated ledger (Rung 3)

| Item | Status | Axioms |
|---|---|---|
| Free field: Fock space, vacuum, vacuum functional | PROVED | propext, Classical.choice, Quot.sound |
| 1-point vanishes; 2-point algebraic-trivial | PROVED | same |
| `[a†,a†] = 0` | PROVED | same |
| Algebraic vacuum cyclicity (W5 shadow) | PROVED | same |
| W0,W1,W2,W4,W6 for free field | BLOCKED (infrastructure, precisely named) | — |
| W3 geometry | PROVED (prior wave) | same |
| Haag–Kastler axioms + existence | PINNED (T5) | — |
| OS axioms + reconstruction + OS existence | PINNED (T5) | — |

**Zero `sorry`s. No interacting-QFT existence claims — the map documents
that none exist in 4D, and this run doesn't change that.** Nothing pushed;
commit is the parent's call.
