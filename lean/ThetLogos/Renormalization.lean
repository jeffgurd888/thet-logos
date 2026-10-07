import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Multiset.Functor

namespace ThetLogos

/-!
# ThetLogos.Renormalization — Connes–Kreimer Hopf algebra of rooted trees

Source: the QFT rungs map (`whitepaper/qft-rungs-map-2026-10-06.md`, Rung 2),
which names the Connes–Kreimer Hopf algebra as the "feasible now, high value"
Rung-2 target: it is pure combinatorics, needs no continuum analysis, and is
the mathematical core of perturbative renormalization
(Connes–Kreimer, *Commun. Math. Phys.* 1998, 2000).

**What this file IS.** A machine-checked construction of the combinatorial
skeleton: planar rooted trees, the grafting operator B₊, the coproduct defined
by the B₊-cocycle recursion, the counit — with the counity axioms proved on
both sides, and precise obstructions for coassociativity and the antipode.

**Honest scoping (read before citing).**
- Trees here are *planar* (children ordered as a `List`): this is the
  noncommutative Connes–Kreimer–Foissy Hopf algebra. The commutative quotient
  (children as multisets) is future work. Every identity proved here is stated
  at the planar level; the coproduct formula is identical in both versions.
- The algebra is presented at the *combinatorial* level: coproduct values are
  explicit multisets of forest-pairs, not elements of `H ⊗ H` for a
  Mathlib tensor product. The bialgebra packaging is future work.
- **Proved:** right counity (`counity_right`), left counity (`counity_left`),
  **coassociativity** (`coassociativity_theorem`, second wave),
  coproduct computations on •, 𝔩₂, V.
- **Blocked (precise obstruction below):** antipode axiom (definition and
  termination resolved; axiom stated as `antipodeAxiom`).
- No physical claim: no amplitudes, no counterterms, no mass gaps.

**Tiers in this file:** T1 = proved below with zero sorrys (check `#print
axioms`); T5 = clearly marked statements/definitions whose proofs are open.
-/

/-- Planar rooted trees: a node with an ordered list of child subtrees.
    The single-node tree is `.node []`. -/
inductive RKTree where
  | node : List RKTree → RKTree
deriving Repr

/-- A forest is a list of trees; the algebra product is concatenation.
    (Planar version: the commutative product is multiset union — future work.) -/
abbrev Forest := List RKTree

/-- The grafting operator B₊: graft a forest onto a fresh root.
    Every tree `t` is uniquely `B₊` of its branch forest. -/
def graft (F : Forest) : RKTree := .node F

/-- Number of nodes. -/
def treeSize : RKTree → Nat
  | .node ts => 1 + (ts.map treeSize).sum

/-- The single-node tree •. -/
def rket1 : RKTree := .node []

/-- The 2-chain: root with one child. -/
def rket2 : RKTree := .node [.node []]

/-- The 3-"V": root with two single-node children. -/
def rketV : RKTree := .node [.node [], .node []]

/-- The 3-chain. -/
def rket3 : RKTree := .node [.node [.node []]]

theorem treeSize_pos (t : RKTree) : 0 < treeSize t := by
  cases t with
  | node ts => unfold treeSize; omega

/-- The Connes–Kreimer coproduct on trees, via the B₊-cocycle recursion:
    `Δ(B₊(F)) = B₊(F) ⊗ 1 + (id ⊗ B₊)(Δ̂(F))`.
    As multiset-of-pairs: the term `([B₊(F)], [])`, plus for every
    `(P, R)` in the forest coproduct `Δ̂(F)` (computed by folding over the
    branches), the term `(P, [B₊(R)])`.
    The recursion is structural: `foldr` calls `treeCoprod` only on the
    child subtrees. -/
def treeCoprod : RKTree → Multiset (Forest × Forest)
  | .node ts =>
    let fcp : Multiset (Forest × Forest) :=
      ts.foldr (fun t acc =>
        (treeCoprod t).bind fun pr₁ =>
        acc.bind fun pr₂ =>
        {((pr₁.1 ++ pr₂.1, pr₁.2 ++ pr₂.2))}) {(([], []))}
    {((([.node ts], [])))} + fcp.bind fun pr => {((pr.1, [.node pr.2]))}

/-- The forest-level coproduct: multiplicative extension of `treeCoprod`. -/
def forestCoprod : Forest → Multiset (Forest × Forest) :=
  List.foldr (fun t acc =>
    (treeCoprod t).bind fun pr₁ =>
    acc.bind fun pr₂ =>
    {((pr₁.1 ++ pr₂.1, pr₁.2 ++ pr₂.2))}) {(([], []))}

@[simp] theorem forestCoprod_nil : forestCoprod [] = {(([], []))} := rfl

theorem forestCoprod_cons (t : RKTree) (ts : Forest) :
    forestCoprod (t :: ts) =
      (treeCoprod t).bind fun pr₁ =>
      (forestCoprod ts).bind fun pr₂ =>
      {((pr₁.1 ++ pr₂.1, pr₁.2 ++ pr₂.2))} := rfl

/-- Δ(•) = • ⊗ 1 + 1 ⊗ • : the single-node tree is primitive. -/
theorem treeCoprod_single :
    treeCoprod rket1 = {(( [rket1], [])), (([], [rket1]))} := by
  unfold rket1 treeCoprod
  simp only [List.foldr_nil]
  rw [Multiset.bind_singleton]
  rfl

/-- Cocycle unfolding: Δ on a node in terms of the forest coproduct. -/
theorem treeCoprod_node (ts : List RKTree) :
    treeCoprod (.node ts) = {((([.node ts], [])))} +
      (forestCoprod ts).bind fun pr => {((pr.1, [.node pr.2]))} := by
  unfold treeCoprod forestCoprod
  rfl

/-- Δ of the 2-chain: 𝔩₂ ↦ 𝔩₂⊗1 + •⊗• + 1⊗𝔩₂. -/
theorem treeCoprod_chain2 :
    treeCoprod rket2 =
      {(( [rket2], [])), (([rket1], [rket1])), (([], [rket2]))} := by
  have h1 : rket2 = .node [rket1] := rfl
  rw [h1, treeCoprod_node, forestCoprod_cons, forestCoprod_nil,
    treeCoprod_single]
  simp only [Multiset.bind_singleton]
  rw [Multiset.singleton_add]
  rfl

/-- The counit: ε([]) = 1, ε = 0 on nonempty forests. -/
def counit : Forest → Nat
  | [] => 1
  | _ :: _ => 0

/-- Right collapse `(id ⊗ ε)`: keep the first components of terms whose
    second component is the empty forest. Uses Bool `isEmpty`, so no
    `DecidableEq` on trees is needed. -/
def collapseR (m : Multiset (Forest × Forest)) : Multiset Forest :=
  m.bind fun pr => if pr.2.isEmpty then {pr.1} else ∅

/-- Left collapse `(ε ⊗ id)`: keep the second components of terms whose
    first component is the empty forest. -/
def collapseL (m : Multiset (Forest × Forest)) : Multiset Forest :=
  m.bind fun pr => if pr.1.isEmpty then {pr.2} else ∅

theorem collapseR_add (a b : Multiset (Forest × Forest)) :
    collapseR (a + b) = collapseR a + collapseR b := by
  unfold collapseR; rw [Multiset.add_bind]

/-- Every term of the "rest" part of `Δ(node ts)` has a *nonempty* second
    component, so right-collapse kills it. -/
theorem collapseR_rest (fcp : Multiset (Forest × Forest)) :
    collapseR (fcp.bind fun pr : Forest × Forest => {((pr.1, [.node pr.2]))}) = ∅ := by
  unfold collapseR
  simp only [Multiset.bind_assoc, Multiset.singleton_bind]
  have hempty : ∀ r : Forest, ([RKTree.node r]).isEmpty = false := fun r => rfl
  simp only [hempty]
  simp [Multiset.bind_zero]

/-- Right counity: `(id ⊗ ε)(Δ(t)) = t`. Needs no induction: the `t ⊗ 1`
    term is the unique term with empty second component. -/
theorem counity_right (t : RKTree) :
    collapseR (treeCoprod t) = {[t]} := by
  cases t with
  | node ts =>
    rw [treeCoprod_node, collapseR_add, collapseR_rest]
    unfold collapseR
    rw [Multiset.singleton_bind]
    simp

/-- `isEmpty` distributes over list append. -/
theorem isEmpty_append_eq (l₁ l₂ : List α) :
    (l₁ ++ l₂).isEmpty = (l₁.isEmpty && l₂.isEmpty) := by
  cases l₁ <;> simp

/-- The collapse-`if` on an appended pair splits into nested `if`s. -/
theorem collapse_if_split (a : Forest × Forest) :
    (fun b : Forest × Forest =>
      if (a.1 ++ b.1).isEmpty then ({a.2 ++ b.2} : Multiset Forest) else ∅)
    = (fun b => if a.1.isEmpty then
        (if b.1.isEmpty then ({a.2 ++ b.2} : Multiset Forest) else ∅) else ∅) := by
  funext b
  have h : (a.1 ++ b.1).isEmpty = (a.1.isEmpty && b.1.isEmpty) :=
    isEmpty_append_eq a.1 b.1
  cases ha : a.1.isEmpty <;> cases hb : b.1.isEmpty <;> simp [h, ha, hb]

/-- Forest-level left counity, assuming the tree-level statement for
    trees of bounded size. Proved by list induction on the forest;
    the tree hypothesis supplies the head case. -/
theorem forest_collapseL_of_tree {n : Nat}
    (htree : ∀ t : RKTree, treeSize t ≤ n → collapseL (treeCoprod t) = {[t]})
    : ∀ (F : Forest), (F.map treeSize).sum ≤ n →
      collapseL (forestCoprod F) = {F} := by
  intro F
  induction F with
  | nil =>
    intro _
    unfold collapseL forestCoprod
    simp
  | cons t ts ih =>
    intro hF
    have hsum : ((t :: ts).map treeSize).sum
        = treeSize t + (ts.map treeSize).sum := by simp
    have ht_le : treeSize t ≤ n := by omega
    have hts_le : (ts.map treeSize).sum ≤ n := by omega
    have ht := htree t ht_le
    have hts := ih hts_le
    unfold collapseL at ht hts ⊢
    rw [forestCoprod_cons, Multiset.bind_assoc]
    have hinner : ∀ a : Forest × Forest,
        ((((forestCoprod ts).bind fun b : Forest × Forest =>
            ({((a.1 ++ b.1, a.2 ++ b.2))} : Multiset (Forest × Forest))).bind
          fun pr => if pr.1.isEmpty then ({pr.2} : Multiset Forest) else ∅))
        = (if a.1.isEmpty then ({a.2 ++ ts} : Multiset Forest) else ∅) := by
      intro a
      rw [Multiset.bind_assoc]
      simp only [Multiset.singleton_bind]
      rw [collapse_if_split a]
      by_cases ha : a.1.isEmpty = true
      · have hfun : (fun b : Forest × Forest =>
              if a.1.isEmpty then
                (if b.1.isEmpty then ({a.2 ++ b.2} : Multiset Forest) else ∅) else ∅)
            = (fun b : Forest × Forest =>
                if b.1.isEmpty then ({a.2 ++ b.2} : Multiset Forest) else ∅) := by
          funext b
          simp [ha]
        rw [hfun]
        have hmap : ((forestCoprod ts).bind fun b : Forest × Forest =>
              if b.1.isEmpty then ({a.2 ++ b.2} : Multiset Forest) else ∅)
            = (((forestCoprod ts).bind fun b : Forest × Forest =>
                if b.1.isEmpty then ({b.2} : Multiset Forest) else ∅)).map
              (fun F => a.2 ++ F) := by
          rw [Multiset.map_bind]
          apply Multiset.bind_congr
          intro b _
          by_cases hb : b.1.isEmpty = true <;> simp [hb]
        rw [hmap, hts]
        simp [ha]
      · have hempty : a.1.isEmpty = false := by
          cases h : a.1.isEmpty <;> simp_all
        simp [hempty]
    simp only [hinner]
    have houter : ((treeCoprod t).bind fun a : Forest × Forest =>
          if a.1.isEmpty then ({a.2 ++ ts} : Multiset Forest) else ∅)
        = (((treeCoprod t).bind fun a : Forest × Forest =>
            if a.1.isEmpty then ({a.2} : Multiset Forest) else ∅)).map
          (fun F => F ++ ts) := by
      rw [Multiset.map_bind]
      apply Multiset.bind_congr
      intro a _
      by_cases ha : a.1.isEmpty = true <;> simp [ha]
    rw [houter, ht]
    simp

/-- Collapse of the cocycle form: the `t ⊗ 1` term dies under left
    collapse (its first component is nonempty), and the rest reindexes
    through the grafting map. -/
theorem collapseL_cocycle (t : RKTree) (fcp : Multiset (Forest × Forest)) :
    collapseL (({(([t], []))} : Multiset (Forest × Forest)) +
      fcp.bind (fun pr : Forest × Forest =>
        ({((pr.1, [RKTree.node pr.2]))} : Multiset (Forest × Forest))))
    = (collapseL fcp).map (fun F => [RKTree.node F]) := by
  unfold collapseL
  have h1 : ((({(([t], []))} : Multiset (Forest × Forest))).bind
      fun pr : Forest × Forest => if pr.1.isEmpty then ({pr.2} : Multiset Forest) else ∅)
      = ∅ := by
    rw [Multiset.singleton_bind]
    simp
  rw [Multiset.add_bind, h1]
  have hadd : ∀ X : Multiset Forest, (∅ : Multiset Forest) + X = X :=
    fun X => by simp
  simp only [hadd, Multiset.bind_assoc, Multiset.singleton_bind, Multiset.map_bind]
  apply Multiset.bind_congr
  intro pr _
  by_cases hpr : pr.1.isEmpty = true <;> simp [hpr]

/-- Tree-level left counity, by strong induction on the size bound.
    The inductive step uses the forest lemma on the branch forest. -/
theorem counity_left_aux : ∀ n : Nat, ∀ t : RKTree,
    treeSize t ≤ n → collapseL (treeCoprod t) = {[t]} := by
  intro n
  induction n with
  | zero =>
    intro t ht
    have := treeSize_pos t
    omega
  | succ n ih =>
    intro t ht
    cases t with
    | node ts =>
      have hts_le : (ts.map treeSize).sum ≤ n := by
        have h1 : treeSize (RKTree.node ts) = 1 + (ts.map treeSize).sum := by
          unfold treeSize
          simp
        omega
      have hforest := forest_collapseL_of_tree (fun u hu => ih u hu) ts hts_le
      rw [treeCoprod_node, collapseL_cocycle, hforest]
      simp

/-- Left counity: `(ε ⊗ id)(Δ(t)) = t`. With right counity, the counit
    axioms for the Connes–Kreimer bialgebra are complete. -/
theorem counity_left (t : RKTree) :
    collapseL (treeCoprod t) = {[t]} :=
  counity_left_aux (treeSize t) t le_rfl

/-- Δ of the 3-V: root with two single-node children.
    Cutting no edge: (V,[]). Cutting both: ([•,•],[•]).
    Cutting left (resp. right): ([•],[𝔩₂]) twice. Full cut: ([],V). -/
theorem treeCoprod_V :
    treeCoprod rketV =
      {(([rketV], [])), (([rket1, rket1], [rket1])), (([rket1], [rket2])),
       (([rket1], [rket2])), (([], [rketV]))} := by
  have hV : rketV = .node [rket1, rket1] := rfl
  have h2 : rket2 = .node [rket1] := rfl
  rw [hV, treeCoprod_node, forestCoprod_cons, forestCoprod_cons,
    forestCoprod_nil, treeCoprod_single]
  simp only [Multiset.bind_singleton]
  rw [h2]
  rfl

/-!
## Blocked: coassociativity and antipode (precise obstructions)

### Coassociativity
The two triple coproducts `(Δ ⊗ id) ∘ Δ` and `(id ⊗ Δ) ∘ Δ`:
-/
def tripleL (t : RKTree) : Multiset (Forest × Forest × Forest) :=
  (treeCoprod t).bind fun pr =>
    (forestCoprod pr.1).bind fun qr => {((qr.1, qr.2, pr.2))}

def tripleR (t : RKTree) : Multiset (Forest × Forest × Forest) :=
  (treeCoprod t).bind fun pr =>
    (forestCoprod pr.2).bind fun qr => {((pr.1, qr.1, qr.2))}

/-- Coassociativity as a pinned statement (T5, proof open). -/
def coassociativity : Prop := ∀ t : RKTree, tripleL t = tripleR t

/-!
**Obstruction for coassociativity.** The proof requires a mutual tree/forest
induction establishing that both parenthesizations enumerate the same
"two-step admissible cuts." The inductive step demands a reindexing bijection:
terms of `tripleL (.node ts)` (cuts of cuts of the branch forest, with the
outer B₊ grafting) must be matched with terms of `tripleR (.node ts)` (cuts
where the second coproduct splits the grafted trunk). Unlike counity — where
the collapse functors killed all but one term — here *every* term survives
and must be bijected. The bijection is mathematically clear (both sides index
chains `P₂ ⊆ P₁` of subforests), but formalizing it needs:
  1. a "subforest" order on forests with the chain characterization, and
  2. reindexing lemmas for iterated `Multiset.bind` over the cocycle.
What would unblock it: an explicit "admissible cut" description of
`treeCoprod` (cuts as a type, Δ as the cut-sum), from which coassociativity
is a cut-bijection. That description is itself a substantial formalization.
-/

/-!
### Antipode
The antipode `S` is defined by the recursion (no filtering needed: the
cocycle isolates the `t ⊗ 1` term as the separate singleton):
  `S(.node ts) = -[.node ts] - Σ_{(P,R) ∈ forestCoprod ts} S(P) • [node R]`
with `S` multiplicative on forests and `S([]) = []`.
-/
/-- Signed forest sums: formal ℤ-linear combinations of forests. -/
abbrev SSum := List (ℤ × Forest)

/-- The antipode as a pinned definition schema (T5): the recursion is
    well-founded by `treeSize`, but formalizing it needs the signed-sum
    algebra (multiplication, negation) and the termination argument through
    `Multiset.bind` over `forestCoprod`. Stated here so the target is fixed. -/
def antipodeSchema : Prop :=
  ∃ _ : RKTree → SSum, True

/-!
**Obstruction for the antipode.** Two gaps:
  1. *Definition:* the recursion `S(.node ts) = -[t] - Σ S(P)·[node R]`
     is well-founded (terms `P` are proper subforests), but Lean's
     termination checker cannot see through the `Multiset.bind` over
     `forestCoprod`; it needs a manual well-founded recursion with an
     explicit size measure and a lemma that coproduct terms are smaller.
  2. *Axiom:* `m(S⊗id)Δ = ε·1` needs the signed-sum algebra (the
     `List (ℤ × Forest)` convolution) plus the same cut analysis as
     coassociativity.
What would unblock it: (1) a `DecidableEq` instance for `RKTree` (via
mutual instances — attempted, hit elaboration issues) to enable computational
normalization of signed sums; (2) the cut description from the coassociativity
obstruction. The *computational* content is clear: `S(•) = -•`,
`S(𝔩₂) = -𝔩₂ + ••`.
-/

end ThetLogos

namespace ThetLogos

/-!
## Coassociativity (second wave, 2026-10-07)

The first wave proved counity on both sides and ledgered coassociativity as
blocked on a "cut-bijection." This section closes it by the standard
cocycle-induction proof (cf. Manchon's notes on the Connes–Kreimer Hopf
algebra), following the size-bound mutual-induction pattern already used
for `counity_left` above:

- `forestCoprod` is multiplicative (`forestCoprod_append`), proved from the
  `foldr` definition;
- forest-level coassociativity follows by list induction via a product
  decomposition (needs a `bind_swap` commutativity lemma);
- the tree-level step expands `tripleL/tripleR (.node ts)` and reduces to
  forest-level coassociativity by `Multiset.map` congruence.

All T1: zero sorrys.
-/

/-- Forest-level triple coproducts: `(Δ̂ ⊗ id) ∘ Δ̂` and `(id ⊗ Δ̂) ∘ Δ̂`,
    as multisets of forest-triples. -/
def forestTripleL (F : Forest) : Multiset (Forest × Forest × Forest) :=
  (forestCoprod F).bind fun pr =>
    (forestCoprod pr.1).bind fun qr => {((qr.1, qr.2, pr.2))}

def forestTripleR (F : Forest) : Multiset (Forest × Forest × Forest) :=
  (forestCoprod F).bind fun pr =>
    (forestCoprod pr.2).bind fun qr => {((pr.1, qr.1, qr.2))}

/-- Independent `bind`s commute. Both sides enumerate the product with
    multiplicity `mult_s(x) * mult_t(y)`. -/
theorem bind_swap {α β γ : Type*} (s : Multiset α) (t : Multiset β)
    (K : α → β → Multiset γ) :
    (s.bind fun x => t.bind fun y => K x y)
      = (t.bind fun y => s.bind fun x => K x y) := by
  induction s using Multiset.induction with
  | empty => simp
  | cons x s ih =>
    simp only [Multiset.cons_bind, Multiset.bind_add]
    rw [ih]

/-- Reindexing helper: pushing an outer singleton-append through a
    product of binds. Both sides normalize (via `bind_assoc` /
    `singleton_bind`) to `S >>= λ a => G >>= λ b => {(p ++ (a.1 ++ b.1), _)}`
    up to append associativity. -/
theorem bind_append_reindex (S G : Multiset (Forest × Forest)) (p q : Forest) :
    (((S.bind fun a => G.bind fun b => {((a.1 ++ b.1, a.2 ++ b.2))}).bind
      fun pr₂ => {((p ++ pr₂.1, q ++ pr₂.2))}) : Multiset (Forest × Forest))
    = (((S.bind fun a => {((p ++ a.1, q ++ a.2))}).bind
      fun a => G.bind fun b => {((a.1 ++ b.1, a.2 ++ b.2))}) : Multiset (Forest × Forest)) := by
  simp only [Multiset.bind_assoc, Multiset.singleton_bind]
  apply Multiset.bind_congr
  intro a _
  apply Multiset.bind_congr
  intro b _
  rw [List.append_assoc, List.append_assoc]

/-- The forest coproduct is multiplicative: `Δ̂(F ++ G) = Δ̂(F) · Δ̂(G)`.
    From the `foldr` definition by list induction; the cons case uses the
    reindexing helper above. -/
theorem forestCoprod_append (F G : Forest) :
    forestCoprod (F ++ G) =
      (forestCoprod F).bind fun a =>
      (forestCoprod G).bind fun b =>
      {((a.1 ++ b.1, a.2 ++ b.2))} := by
  induction F with
  | nil =>
    rw [List.nil_append, forestCoprod_nil, Multiset.singleton_bind]
    simp only [List.nil_append]
    rw [Multiset.bind_singleton]
    exact (Multiset.map_id' _).symm
  | cons t ts ih =>
    rw [List.cons_append, forestCoprod_cons, ih, forestCoprod_cons]
    conv_rhs => rw [Multiset.bind_assoc]
    apply Multiset.bind_congr
    intro pr₁ _
    exact bind_append_reindex _ _ pr₁.1 pr₁.2

end ThetLogos

namespace ThetLogos

/-- Product decomposition (left): `forestTripleL` on a cons splits as the
    product of `tripleL` on the head and `forestTripleL` on the tail.
    Proof: unfold, `forestCoprod_cons`, normalize binds, rewrite the inner
    `forestCoprod` of an append by multiplicativity, normalize again, then
    swap the independent binds. -/
theorem forestTripleL_cons (t : RKTree) (ts : Forest) :
    forestTripleL (t :: ts) =
      (tripleL t).bind fun tc =>
      (forestTripleL ts).bind fun fd =>
      {((tc.1 ++ fd.1, (tc.2.1 ++ fd.2.1, tc.2.2 ++ fd.2.2)))} := by
  unfold forestTripleL tripleL
  rw [forestCoprod_cons]
  simp only [Multiset.bind_assoc, Multiset.singleton_bind, forestCoprod_append,
    Multiset.bind_assoc, Multiset.singleton_bind]
  apply Multiset.bind_congr
  intro a _
  rw [bind_swap]

end ThetLogos

namespace ThetLogos

/-- Product decomposition (right): `forestTripleR` on a cons splits as the
    product of `tripleR` on the head and `forestTripleR` on the tail.
    Same proof shape as the left version. -/
theorem forestTripleR_cons (t : RKTree) (ts : Forest) :
    forestTripleR (t :: ts) =
      (tripleR t).bind fun tc =>
      (forestTripleR ts).bind fun fd =>
      {((tc.1 ++ fd.1, (tc.2.1 ++ fd.2.1, tc.2.2 ++ fd.2.2)))} := by
  unfold forestTripleR tripleR
  rw [forestCoprod_cons]
  simp only [Multiset.bind_assoc, Multiset.singleton_bind, forestCoprod_append,
    Multiset.bind_assoc, Multiset.singleton_bind]
  apply Multiset.bind_congr
  intro a _
  rw [bind_swap]

end ThetLogos

namespace ThetLogos

/-- Forest-level coassociativity, assuming the tree-level statement for
    trees of bounded size. By list induction; the cons case uses the product
    decompositions and rewrites with the two hypotheses. Follows the
    `forest_collapseL_of_tree` pattern from the counity proof. -/
theorem forest_coassoc_of_tree {n : Nat}
    (htree : ∀ t : RKTree, treeSize t ≤ n → tripleL t = tripleR t)
    : ∀ (F : Forest), (F.map treeSize).sum ≤ n →
      forestTripleL F = forestTripleR F := by
  intro F
  induction F with
  | nil =>
    intro _
    unfold forestTripleL forestTripleR
    simp [forestCoprod_nil]
  | cons t ts ih =>
    intro hF
    have hsum : ((t :: ts).map treeSize).sum
        = treeSize t + (ts.map treeSize).sum := by simp
    have ht_le : treeSize t ≤ n := by
      have hpos : 0 < treeSize t := treeSize_pos t
      omega
    have hts_le : (ts.map treeSize).sum ≤ n := by omega
    rw [forestTripleL_cons, forestTripleR_cons, htree t ht_le, ih hts_le]

end ThetLogos

namespace ThetLogos

/-- The forest coproduct on a singleton is the tree coproduct. -/
theorem forestCoprod_singleton (t : RKTree) :
    forestCoprod [t] = treeCoprod t := by
  rw [show [t] = t :: [] from rfl, forestCoprod_cons, forestCoprod_nil]
  simp only [Multiset.singleton_bind, List.append_nil, Prod.mk.eta]
  rw [Multiset.bind_singleton]
  exact Multiset.map_id' _

end ThetLogos

namespace ThetLogos

/-- Reindexing helper for the tree step (left): the "rest" part of
    `tripleL (.node ts)` — applying the second coproduct after the
    cocycle's grafting — is the `map` of `forestTripleL ts` under the
    grafting of the third component. -/
theorem tripleL_rest (ts : Forest) :
    (((forestCoprod ts).bind fun pr => {((pr.1, [RKTree.node pr.2]))}).bind
      fun pr => (forestCoprod pr.1).bind fun qr => {((qr.1, qr.2, pr.2))})
    = (forestTripleL ts).map fun q => (q.1, q.2.1, [RKTree.node q.2.2]) := by
  unfold forestTripleL
  rw [Multiset.bind_assoc]
  simp only [Multiset.singleton_bind]
  rw [Multiset.map_bind]
  apply Multiset.bind_congr
  intro pr _
  rw [Multiset.map_bind]
  apply Multiset.bind_congr
  intro qr _
  rfl

end ThetLogos

namespace ThetLogos

/-- The "deep" part of `tripleR (.node ts)`: the double coproduct on the
    grafted trunk reindexes to the `map` of `forestTripleR ts`. -/
theorem tripleR_deep (ts : Forest) :
    ((forestCoprod ts).bind fun a => (forestCoprod a.2).bind fun s =>
      ({((a.1, s.1, [RKTree.node s.2]))} : Multiset (Forest × Forest × Forest)))
    = (forestTripleR ts).map fun q => (q.1, q.2.1, [RKTree.node q.2.2]) := by
  unfold forestTripleR
  rw [Multiset.map_bind]
  apply Multiset.bind_congr
  intro pr _
  rw [Multiset.map_bind]
  apply Multiset.bind_congr
  intro qr _
  rfl

/-- Reindexing helper for the tree step (right): the "rest" part of
    `tripleR (.node ts)` splits into the trunk term plus the `map` of
    `forestTripleR ts` under grafting of the third component. -/
theorem tripleR_rest (ts : Forest) :
    (((forestCoprod ts).bind fun pr => {((pr.1, [RKTree.node pr.2]))}).bind
      fun pr => (forestCoprod pr.2).bind fun qr => {((pr.1, qr.1, qr.2))})
    = ((forestCoprod ts).bind fun pr => {((pr.1, [RKTree.node pr.2], []))}) +
      (forestTripleR ts).map fun q => (q.1, q.2.1, [RKTree.node q.2.2]) := by
  rw [Multiset.bind_assoc]
  simp only [Multiset.singleton_bind]
  have key : ∀ pr : Forest × Forest,
      ((forestCoprod [RKTree.node pr.2]).bind fun qr => {((pr.1, qr.1, qr.2))})
      = ({((pr.1, [RKTree.node pr.2], []))} : Multiset (Forest × Forest × Forest)) +
        ((forestCoprod pr.2).bind fun s => {((pr.1, s.1, [RKTree.node s.2]))}) := by
    intro pr
    rw [forestCoprod_singleton, treeCoprod_node, Multiset.add_bind]
    simp only [Multiset.singleton_bind, Multiset.bind_assoc]
  simp only [key, Multiset.bind_add, tripleR_deep]

end ThetLogos

namespace ThetLogos

/-- Expansion of `tripleL` on a node. -/
theorem tripleL_node (ts : Forest) :
    tripleL (RKTree.node ts) =
      {(([RKTree.node ts], [], []))} +
      ((forestCoprod ts).bind fun pr => {((pr.1, [RKTree.node pr.2], []))}) +
      (forestTripleL ts).map fun q => (q.1, q.2.1, [RKTree.node q.2.2]) := by
  unfold tripleL
  rw [treeCoprod_node ts, Multiset.add_bind]
  have hA : (({(([RKTree.node ts], []))} : Multiset (Forest × Forest)).bind
      (fun pr => (forestCoprod pr.1).bind fun qr => {((qr.1, qr.2, pr.2))}))
      = ({(([RKTree.node ts], [], []))} : Multiset (Forest × Forest × Forest)) +
        ((forestCoprod ts).bind fun pr => {((pr.1, [RKTree.node pr.2], []))}) := by
    rw [Multiset.singleton_bind, forestCoprod_singleton, treeCoprod_node ts,
      Multiset.add_bind]
    simp only [Multiset.singleton_bind, Multiset.bind_assoc]
  rw [hA, tripleL_rest ts, add_assoc]

end ThetLogos

namespace ThetLogos

/-- Expansion of `tripleR` on a node: same first two chunks as `tripleL`,
    differing only in the `forestTripleR` vs `forestTripleL` map. -/
theorem tripleR_node (ts : Forest) :
    tripleR (RKTree.node ts) =
      {(([RKTree.node ts], [], []))} +
      ((forestCoprod ts).bind fun pr => {((pr.1, [RKTree.node pr.2], []))}) +
      (forestTripleR ts).map fun q => (q.1, q.2.1, [RKTree.node q.2.2]) := by
  have hA : (({(([RKTree.node ts], []))} : Multiset (Forest × Forest)).bind
      (fun pr => (forestCoprod pr.2).bind fun qr => {((pr.1, qr.1, qr.2))}))
      = ({(([RKTree.node ts], [], []))} : Multiset (Forest × Forest × Forest)) := by
    rw [Multiset.singleton_bind, forestCoprod_nil, Multiset.singleton_bind]
  unfold tripleR
  rw [treeCoprod_node ts, Multiset.add_bind, hA, tripleR_rest ts]
  rw [add_assoc]

end ThetLogos

namespace ThetLogos

/-- Tree-level coassociativity by strong induction on the size bound.
    The node case expands both sides (`tripleL_node`, `tripleR_node`) and
    closes by forest-level coassociativity on the branch forest. -/
theorem coassoc_aux : ∀ n : Nat, ∀ t : RKTree,
    treeSize t ≤ n → tripleL t = tripleR t := by
  intro n
  induction n with
  | zero =>
    intro t ht
    have := treeSize_pos t
    omega
  | succ n ih =>
    intro t ht
    cases t with
    | node ts =>
      have hts_le : (ts.map treeSize).sum ≤ n := by
        have h1 : treeSize (RKTree.node ts) = 1 + (ts.map treeSize).sum := by
          unfold treeSize
          simp
        omega
      have hforest := forest_coassoc_of_tree (fun u hu => ih u hu) ts hts_le
      rw [tripleL_node, tripleR_node, hforest]

/-- **Coassociativity proved (T1).** The `coassociativity : Prop` pinned as
    T5 in the first wave is now a theorem: both parenthesizations of the
    triple coproduct agree. With counity (both sides, first wave), the
    Connes–Kreimer bialgebra axioms are complete at the combinatorial level. -/
theorem coassociativity_theorem : coassociativity :=
  fun t => coassoc_aux (treeSize t) t le_rfl

end ThetLogos

namespace ThetLogos

/-!
## Antipode (second wave, 2026-10-07)

The first wave ledgered the antipode as blocked on (a) termination and (b)
the signed-sum algebra. This section resolves (a): coproduct terms are
size-bounded, so the antipode recursion is well-founded by `treeSize`.
-/

/-- Forest-level size bound, assuming the tree-level bound for bounded sizes.
    If `(P,R) ∈ forestCoprod ts` then the pruned forest `P` is no bigger
    than `ts` (node count is conserved by cuts). -/
theorem forest_size_bound_of_tree {n : Nat}
    (htree : ∀ t : RKTree, treeSize t ≤ n →
      ∀ P R : Forest, (P, R) ∈ treeCoprod t → (P.map treeSize).sum ≤ treeSize t)
    : ∀ (ts : Forest), (ts.map treeSize).sum ≤ n →
      ∀ P R : Forest, (P, R) ∈ forestCoprod ts →
        (P.map treeSize).sum ≤ (ts.map treeSize).sum := by
  intro ts
  induction ts with
  | nil =>
    intro _ P R hmem
    rw [forestCoprod_nil, Multiset.mem_singleton] at hmem
    obtain ⟨rfl, rfl⟩ := hmem
    simp
  | cons t us ih =>
    intro hts P R hmem
    rw [forestCoprod_cons, Multiset.mem_bind] at hmem
    obtain ⟨a, ha, hPR⟩ := hmem
    rw [Multiset.mem_bind] at hPR
    obtain ⟨b, hb, hPR2⟩ := hPR
    simp only [Multiset.mem_singleton] at hPR2
    -- hPR2 : (P, R) = (a.1 ++ b.1, a.2 ++ b.2)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hPR2
    have hsum : ((t :: us).map treeSize).sum
        = treeSize t + (us.map treeSize).sum := by simp
    have ht_le : treeSize t ≤ n := by
      have hpos : 0 ≤ (us.map treeSize).sum := Nat.zero_le _
      omega
    have hus_le : (us.map treeSize).sum ≤ n := by
      have hpos : 0 < treeSize t := treeSize_pos t
      omega
    have htree_a := htree t ht_le a.1 a.2 ha
    have hforest_b := ih hus_le b.1 b.2 hb
    simp only [List.map_append, List.sum_append]
    omega

end ThetLogos

namespace ThetLogos

/-- Tree-level size bound by strong induction: coproduct pruned forests are
    no bigger than the tree. The `([t],[])` term is exact; the rest uses the
    forest bound on the branches. -/
theorem tree_size_bound_aux : ∀ n : Nat, ∀ t : RKTree,
    treeSize t ≤ n → ∀ P R : Forest,
      (P, R) ∈ treeCoprod t → (P.map treeSize).sum ≤ treeSize t := by
  intro n
  induction n with
  | zero =>
    intro t ht
    have := treeSize_pos t
    omega
  | succ n ih =>
    intro t ht P R hmem
    cases t with
    | node us =>
      have hts_le : (us.map treeSize).sum ≤ n := by
        have h1 : treeSize (RKTree.node us) = 1 + (us.map treeSize).sum := by
          unfold treeSize
          simp
        omega
      have hforest := forest_size_bound_of_tree (fun u hu => ih u hu) us hts_le
      rw [treeCoprod_node] at hmem
      rw [Multiset.mem_add] at hmem
      cases hmem with
      | inl h =>
        rw [Multiset.mem_singleton] at h
        obtain ⟨rfl, rfl⟩ := h
        simp
      | inr h =>
        rw [Multiset.mem_bind] at h
        obtain ⟨pr, hpr, hPR⟩ := h
        rw [Multiset.mem_singleton] at hPR
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hPR
        have hb := hforest pr.1 pr.2 hpr
        have h1 : treeSize (RKTree.node us) = 1 + (us.map treeSize).sum := by
          unfold treeSize
          simp
        omega

/-- Size bound: every pruned forest in a coproduct term is bounded by the
    input. In particular, trees in `P` are strictly smaller than `.node ts`. -/
theorem coprod_pruned_bound (ts : Forest) (P R : Forest)
    (hmem : (P, R) ∈ forestCoprod ts) :
    (P.map treeSize).sum ≤ (ts.map treeSize).sum :=
  forest_size_bound_of_tree
    (n := (ts.map treeSize).sum)
    (fun t ht P R h => tree_size_bound_aux _ t ht P R h)
    ts le_rfl P R hmem

end ThetLogos

namespace ThetLogos

/-! ### Signed-sum algebra -/

/-- Addition of signed sums: concatenation. -/
def ssumAdd (x y : SSum) : SSum := x ++ y

/-- Negation: flip coefficients. -/
def ssumNeg (x : SSum) : SSum := x.map fun pr => (-pr.1, pr.2)

/-- Multiplication (convolution): bilinear extension of
    `[(c₁,F₁)] * [(c₂,F₂)] = [(c₁*c₂, F₁++F₂)]`. -/
def ssumMul (x y : SSum) : SSum :=
  x.flatMap fun pr₁ => y.flatMap fun pr₂ => [((pr₁.1 * pr₂.1, pr₁.2 ++ pr₂.2))]

/-- Unit: `[(1, [])]`. -/
def ssumOne : SSum := [(1, [])]

theorem ssumAdd_nil_left (x : SSum) : ssumAdd [] x = x := rfl
theorem ssumAdd_nil_right (x : SSum) : ssumAdd x [] = x := by
  unfold ssumAdd; simp

end ThetLogos

namespace ThetLogos

/-! ### Antipode definition -/

/-- Classical decidability for coproduct terms (for `Multiset.toList`).
    Uses `Classical.choice`, already in the axiom footprint. -/
noncomputable instance decEqForestProd : DecidableEq (Forest × Forest) :=
  Classical.decEq _

mutual
/-- The antipode on trees, by recursion on a size bound `n`.
    `S(.node ts) = - Σ_{(P,R) ∈ Δ̂(ts)} S(P)·[node R]`
    (The `([], ts)` term of the sum contributes `[t]` via `S([]) = [[]]`,
    so no separate `-[t]` is needed.)
    The sum is over `Multiset.toList` (classical); the recursion is on `n`,
    valid because pruned forests are strictly smaller (`coprod_pruned_bound`).
    Returns `[]` when the bound is exhausted (never called in that case). -/
noncomputable def antipodeTree : Nat → RKTree → SSum
  | 0, _ => []
  | (n+1), .node ts =>
    let terms := Multiset.toList (forestCoprod ts)
    let s := terms.foldr (fun pr acc =>
      ssumAdd (ssumMul (antipodeForest n pr.1) [(1, [RKTree.node pr.2])]) acc) []
    ssumNeg s
/-- The antipode on forests: multiplicative extension. -/
noncomputable def antipodeForest (n : Nat) : Forest → SSum
  | [] => ssumOne
  | u :: us => ssumMul (antipodeTree n u) (antipodeForest n us)
end

end ThetLogos

namespace ThetLogos

/-! ### Antipode axiom (statement) -/

/-- The left antipode axiom `m(S⊗id)Δ = ηε`, as a sum over the coproduct:
    for nonempty `t`, `Σ_{(P,R) ∈ Δ(t)} S(P)·[R] = 0`.
    The sum is over `Multiset.toList` folded with `ssumAdd`. -/
noncomputable def antipodeAxiomSum (n : Nat) (t : RKTree) : SSum :=
  (Multiset.toList (treeCoprod t)).foldr
    (fun pr acc => ssumAdd (ssumMul (antipodeForest n pr.1) [(1, pr.2)]) acc) []

/-- Antipode axiom (T5, statement): the antipode cancels the coproduct.
    Proof sketch: expand `treeCoprod t` by the cocycle (`treeCoprod_node`);
    the `([t],[])` term gives `S(t)·[[]] = S(t)`; the rest gives
    `Σ_{(P,R)∈Δ̂(ts)} S(P)·[[.node R]]`; by the definition of `antipodeTree`
    these sum to zero. The full formalization needs the toList-fold
    to match the definitional fold — a routine but lengthy reindexing. -/
def antipodeAxiom : Prop :=
  ∀ (n : Nat) (t : RKTree), 0 < treeSize t →
    treeSize t ≤ n → antipodeAxiomSum n t = []

end ThetLogos
