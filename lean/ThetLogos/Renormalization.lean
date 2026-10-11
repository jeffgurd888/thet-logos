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

/-! ### The as-stated antipode axiom is FALSE

`SSum = List (ℤ × Forest)` is a free-monoid presentation with NO cancellation:
`ssumNeg` merely flips coefficients, so concatenated signed sums never cancel
to `[]`. The antipode identity `m(S⊗id)Δ = ηε` is true in the group ring, but
`antipodeAxiom` states it as list-equality with `[]` — which is false. The
wave-2 "toList-fold congruence" obstruction misdiagnosed the problem: no
reindexing can close `antipodeAxiom`, because the statement itself is wrong.
Counterexample: `n = 1`, `t = •` (the single-node tree).
The corrected statement (evaluation into finitely supported functions) is
`antipodeAxiomEval` below. -/

/-- The antipode of the single-node tree, computed in closed form. -/
theorem antipodeTree_rket1 : antipodeTree 1 rket1 = [(-1, [rket1])] := by
  simp only [antipodeTree, forestCoprod, rket1, List.foldr_nil, List.foldr_cons,
    Multiset.toList_singleton, ssumNeg, ssumAdd, ssumMul, ssumOne, antipodeForest,
    List.flatMap_singleton, List.append_nil, mul_one, List.nil_append, List.map_singleton]

/-- The forest antipode on `[•]`, computed in closed form. -/
theorem antipodeForest_rket1 : antipodeForest 1 [rket1] = [(-1, [rket1])] := by
  simp only [antipodeForest, antipodeTree_rket1, ssumOne, ssumMul,
    List.flatMap_singleton, mul_one, List.append_nil]

/-- Each axiom-sum term for `t = •` is a nonempty singleton list. -/
theorem axiomTerm_rket1_ne_nil (pr : Forest × Forest)
    (hmem : pr ∈ ({(([rket1], [])) , (([], [rket1]))} : Multiset (Forest × Forest))) :
    ssumMul (antipodeForest 1 pr.1) [(1, pr.2)] ≠ [] := by
  have hdisj : pr = (([rket1], [])) ∨ pr = (([], [rket1])) := by simpa using hmem
  have e1 : ssumMul (antipodeForest 1 [rket1]) [(1, ([] : Forest))] = [(-1, [rket1])] := by
    rw [antipodeForest_rket1]
    simp only [ssumMul, List.flatMap_singleton, mul_one, List.append_nil]
  have e2 : ssumMul (antipodeForest 1 ([] : Forest)) [(1, [rket1])] = [(1, [rket1])] := by
    have h0 : antipodeForest 1 ([] : Forest) = [(1, [])] := by
      simp only [antipodeForest, ssumOne]
    rw [h0]
    simp only [ssumMul, List.flatMap_singleton, mul_one, List.nil_append]
  rcases hdisj with rfl | rfl
  · rw [e1]; simp
  · rw [e2]; simp

/-- `ssumAdd` emptiness splits (it is list append). -/
theorem ssumAdd_eq_nil_iff (x y : SSum) : ssumAdd x y = [] ↔ x = [] ∧ y = [] :=
  List.append_eq_nil_iff

/-- The as-stated antipode axiom is FALSE. At `n = 1`, `t = •`, the axiom sum
    is the 2-element list `[(-1,[•]), (1,[•])]` (in some order), never `[]`. -/
theorem antipodeAxiom_false : ¬ antipodeAxiom := by
  intro h
  have hle : treeSize rket1 ≤ 1 := by
    have hr : treeSize rket1 = 1 := by simp [treeSize, rket1]
    rw [hr]
  have hcon := h 1 rket1 (treeSize_pos rket1) hle
  unfold antipodeAxiomSum at hcon
  rw [treeCoprod_single] at hcon
  have hcard : Multiset.card ({(([rket1], [])) , (([], [rket1]))} :
      Multiset (Forest × Forest)) = 2 := by
    rw [Multiset.insert_eq_cons, Multiset.card_cons, Multiset.card_singleton]
  have hlen : (Multiset.toList ({(([rket1], [])) , (([], [rket1]))} :
      Multiset (Forest × Forest))).length = 2 := by
    rw [Multiset.length_toList, hcard]
  obtain ⟨p₁, p₂, hlist⟩ := List.length_eq_two.mp hlen
  have hm1 : p₁ ∈ ({(([rket1], [])) , (([], [rket1]))} :
      Multiset (Forest × Forest)) := by
    rw [← Multiset.mem_toList, hlist]; simp
  have hm2 : p₂ ∈ ({(([rket1], [])) , (([], [rket1]))} :
      Multiset (Forest × Forest)) := by
    rw [← Multiset.mem_toList, hlist]; simp
  have ht1 := axiomTerm_rket1_ne_nil p₁ hm1
  rw [hlist] at hcon
  simp only [List.foldr_cons, List.foldr_nil] at hcon
  rw [ssumAdd_eq_nil_iff] at hcon
  exact ht1 hcon.1


/-! ### Corrected antipode axiom: evaluation into the group ring -/

/-- Classical decidability for forests (for coefficient evaluation). -/
noncomputable instance decEqForest : DecidableEq Forest := Classical.decEq _

/-- Evaluation of a signed sum at a forest: the net coefficient.
    Unlike raw `SSum` lists, this has cancellation — which is what the
    antipode identity needs. `ssumEval x F` sums the coefficients of all
    pairs `(c, F')` in `x` with `F' = F`. -/
noncomputable def ssumEval (x : SSum) (F : Forest) : ℤ :=
  (x.map (fun pr => if pr.2 = F then pr.1 else 0)).sum

/-- Evaluation distributes over concatenation. -/
theorem ssumEval_add (x y : SSum) (F : Forest) :
    ssumEval (x ++ y) F = ssumEval x F + ssumEval y F := by
  unfold ssumEval
  rw [List.map_append, List.sum_append]

/-- Corrected antipode axiom (T1, proved as `antipodeAxiomEval_proved` below):
    the antipode cancels the coproduct *in the group ring* — i.e., after
    evaluation (which has cancellation). For nonempty `t`, the net coefficient
    at every forest is zero.
    Proof: joint induction on the size bound `n` (`stab_treeStab_axiomN`),
    proving evaluation-stability of `antipodeForest`/`antipodeTree` alongside
    the axiom. The analytic core is the convolution formula
    `ssumEval_ssumMul`: evaluation turns the list convolution `ssumMul` into a
    genuine convolution of integer-valued functions, so evaluation is a
    congruence for `ssumMul`. The cocycle split (`treeCoprod_node`) then gives
    `S(t) + Σ = S(t) - S(t) = 0` after the stability rewrite. -/
def antipodeAxiomEval : Prop :=
  ∀ (n : Nat) (t : RKTree), 0 < treeSize t →
    treeSize t ≤ n → ∀ F : Forest, ssumEval (antipodeAxiomSum n t) F = 0


/-! ## Evaluated antipode axiom: proof
The proof goes by induction on the size bound `n`, proving three statements jointly:
`Stab` (evaluation-stability of `antipodeForest`), `TreeStab` (of `antipodeTree`),
and `AxiomN` (the evaluated antipode axiom). The analytic core is that evaluation
turns the list convolution `ssumMul` into a genuine convolution of integer-valued
functions (`ssumEval_ssumMul`), making evaluation a congruence for `ssumMul`. -/

theorem list_map_congr_of {α β : Type} (l : List α) (f g : α → β)
    (h : ∀ a ∈ l, f a = g a) : l.map f = l.map g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      simp only [List.map_cons, h a (List.mem_cons.mpr (Or.inl rfl)),
        ih (fun b hb => h b (List.mem_cons.mpr (Or.inr hb)))]

theorem list_sum_map_zero_of (l : List α) (f : α → ℤ) (h : ∀ a ∈ l, f a = 0) :
    (l.map f).sum = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      rw [List.map_cons, List.sum_cons, h a (by simp),
        ih (fun b hb => h b (by simp [hb])), add_zero]

theorem sum_flatMap_aux (x : List α) (k : α → List ℤ) :
    (x.flatMap k).sum = (x.map fun a => (k a).sum).sum := by
  induction x with
  | nil => rfl
  | cons a x ih =>
      simp only [List.flatMap_cons, List.sum_append, List.map_cons, List.sum_cons, ih]

theorem sum_map_ite_mul (l : List β) (p : β → Prop) [DecidablePred p] (r : ℤ) (f : β → ℤ) :
    (l.map fun b => if p b then r * f b else 0).sum
      = r * (l.map fun b => if p b then f b else 0).sum := by
  induction l with
  | nil => simp
  | cons b l ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      by_cases h : p b <;> simp [h, mul_add]

theorem sum_map_ite_filter (l : List α) (p : α → Prop) [DecidablePred p] (C : α → ℤ) :
    (l.map fun k => if p k then C k else 0).sum
      = ((l.filter fun k => decide (p k)).map C).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      by_cases h : p a
      · have hd : decide (p a) = true := decide_eq_true h
        have hf : (a :: l).filter (fun k => decide (p k)) = a :: l.filter (fun k => decide (p k)) := by
          simp [hd]
        simp only [List.map_cons, List.sum_cons, ih, ite_eq_left h, hf, List.map_cons, List.sum_cons]
      · have hd : decide (p a) = false := by simp [h]
        have hf : (a :: l).filter (fun k => decide (p k)) = l.filter (fun k => decide (p k)) := by
          simp [hd]
        simp only [List.map_cons, List.sum_cons, ih, ite_eq_right h, zero_add, hf]

theorem ssumEval_nil (F : Forest) : ssumEval [] F = 0 := by
  simp [ssumEval]

theorem ssumEval_neg (x : SSum) (F : Forest) :
    ssumEval (ssumNeg x) F = -ssumEval x F := by
  have h : ∀ l : List (ℤ × Forest),
      (l.map fun pr => if pr.2 = F then -pr.1 else (0:ℤ)).sum
        = -((l.map fun pr => if pr.2 = F then pr.1 else (0:ℤ))).sum := by
    intro l
    induction l with
    | nil => simp
    | cons pr l ih =>
        simp only [List.map_cons, List.sum_cons, ih]
        by_cases hc : pr.2 = F <;> simp [hc] <;> ac_rfl
  have e : ssumEval (ssumNeg x) F
      = ((x.map fun pr => if pr.2 = F then -pr.1 else (0:ℤ))).sum := by
    unfold ssumNeg ssumEval
    rw [List.map_map]
    apply congrArg List.sum
    apply list_map_congr_of
    intro pr _
    rfl
  rw [e, h]
  rfl

theorem shiftEval_eq (y : SSum) (A F : Forest) :
    (y.map fun pr₂ => if A ++ pr₂.2 = F then pr₂.1 else 0).sum
      = if A.length ≤ F.length ∧ F.take A.length = A then ssumEval y (F.drop A.length) else 0 := by
  by_cases hc : A.length ≤ F.length ∧ F.take A.length = A
  · have key : ∀ pr₂ : ℤ × Forest,
        (if A ++ pr₂.2 = F then pr₂.1 else (0:ℤ))
          = (if pr₂.2 = F.drop A.length then pr₂.1 else 0) := by
      intro pr₂
      by_cases h : A ++ pr₂.2 = F
      · have hB : pr₂.2 = F.drop A.length := by
          have hcon := congrArg (List.drop A.length) h
          simp only [List.drop_left] at hcon
          exact hcon
        rw [ite_eq_left h, ite_eq_left hB]
      · have hB : ¬ pr₂.2 = F.drop A.length := by
          intro hcon
          apply h
          have e : A ++ pr₂.2 = F.take A.length ++ F.drop A.length := by rw [hc.2, hcon]
          rw [e, List.take_append_drop]
        rw [ite_eq_right h, ite_eq_right hB]
    rw [ite_eq_left hc]
    have e2 : (y.map fun pr₂ => if A ++ pr₂.2 = F then pr₂.1 else (0:ℤ))
        = (y.map fun pr₂ => if pr₂.2 = F.drop A.length then pr₂.1 else (0:ℤ)) :=
      list_map_congr_of _ _ _ (fun pr₂ _ => key pr₂)
    rw [e2]
    rfl
  · have hvan : ∀ pr₂ : ℤ × Forest, A ++ pr₂.2 = F → False := by
      intro pr₂ hcon
      apply hc
      constructor
      · have hle := congrArg List.length hcon
        simp only [List.length_append] at hle
        omega
      · have htk := congrArg (List.take A.length) hcon
        simp only [List.take_left] at htk
        exact htk.symm
    rw [ite_eq_right hc, sum_map_ite_filter]
    have hnil : y.filter (fun pr₂ => decide (A ++ pr₂.2 = F)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro a _ hcon
      exact hvan a (of_decide_eq_true hcon)
    rw [hnil]
    rfl

theorem nodup_all_eq_singleton {α : Type} (l : List α) (c : α) (hn : l.Nodup)
    (hall : ∀ x ∈ l, x = c) (hmem : c ∈ l) : l = [c] := by
  cases l with
  | nil => simp at hmem
  | cons y ys =>
      have hy : y = c := hall y (by simp)
      have hys : ys = [] := by
        by_contra hne
        obtain ⟨z, hz⟩ := List.exists_mem_of_ne_nil ys hne
        have h1 : z = c := hall z (by simp [hz])
        have hnp : y ∉ ys := (List.nodup_cons.mp hn).1
        have h2 : y ∈ ys := by rw [hy, ← h1]; exact hz
        exact hnp h2
      rw [hy, hys]

theorem sum_range_ite_take (F a : Forest) (C : Nat → ℤ) :
    ((List.range (F.length + 1)).map fun k => if a = F.take k then C k else 0).sum
      = if a.length ≤ F.length ∧ F.take a.length = a then C a.length else 0 := by
  have key : ∀ k, k ≤ F.length → (a = F.take k ↔ k = a.length ∧ F.take a.length = a) := by
    intro k hk
    constructor
    · intro h
      have hlen : a.length = k := by
        have hle := congrArg List.length h
        rw [List.length_take] at hle
        omega
      exact ⟨hlen.symm, by rw [hlen]; exact h.symm⟩
    · rintro ⟨rfl, h⟩
      exact h.symm
  rw [sum_map_ite_filter]
  by_cases h : a.length ≤ F.length ∧ F.take a.length = a
  · rw [ite_eq_left h]
    have hfil : (List.range (F.length + 1)).filter (fun k => decide (a = F.take k)) = [a.length] := by
      have hnod : ((List.range (F.length + 1)).filter fun k => decide (a = F.take k)).Nodup :=
        List.Nodup.filter _ List.nodup_range
      have hall : ∀ x ∈ (List.range (F.length + 1)).filter (fun k => decide (a = F.take k)),
          x = a.length := by
        intro x hx
        rw [List.mem_filter] at hx
        have hkk : x ≤ F.length := by
          have hmem := hx.1; rw [List.mem_range] at hmem; omega
        have hxx : a = F.take x := of_decide_eq_true hx.2
        exact ((key x hkk).mp hxx).1
      have hmemf : a.length ∈ (List.range (F.length + 1)).filter (fun k => decide (a = F.take k)) := by
        rw [List.mem_filter]
        exact ⟨List.mem_range.mpr (by omega), decide_eq_true h.2.symm⟩
      exact nodup_all_eq_singleton _ _ hnod hall hmemf
    rw [hfil, List.map_singleton, List.sum_singleton]
  · rw [ite_eq_right h]
    have hnil : (List.range (F.length + 1)).filter (fun k => decide (a = F.take k)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro k hk hcon
      have hkk : k ≤ F.length := by
        rw [List.mem_range] at hk; omega
      have hkk' : a = F.take k := of_decide_eq_true hcon
      have hlen : a.length ≤ F.length := by
        have hle := congrArg List.length hkk'
        rw [List.length_take] at hle
        omega
      exact h ⟨hlen, ((key k hkk).mp hkk').2⟩
    rw [hnil]
    rfl

theorem ssumEval_ssumMul_single (pr : ℤ × Forest) (y : SSum) (F : Forest) :
    ssumEval (ssumMul [pr] y) F
      = ((List.range (F.length + 1)).map fun k => ssumEval [pr] (F.take k) * ssumEval y (F.drop k)).sum := by
  have e1 : ssumMul [pr] y = y.flatMap fun pr₂ => [(pr.1 * pr₂.1, pr.2 ++ pr₂.2)] := by
    simp only [ssumMul, List.flatMap_singleton]
  rw [e1]
  have e2 : ssumEval (y.flatMap fun pr₂ => [(pr.1 * pr₂.1, pr.2 ++ pr₂.2)]) F
      = (y.map fun pr₂ => if pr.2 ++ pr₂.2 = F then pr.1 * pr₂.1 else 0).sum := by
    unfold ssumEval
    rw [List.map_flatMap, sum_flatMap_aux]
    apply congrArg List.sum
    apply list_map_congr_of
    intro pr₂ _
    simp only [List.map_singleton, List.sum_singleton]
  rw [e2, sum_map_ite_mul, shiftEval_eq]
  have e3 : ∀ k, ssumEval [pr] (F.take k) * ssumEval y (F.drop k)
      = (if pr.2 = F.take k then pr.1 * ssumEval y (F.drop k) else 0) := by
    intro k
    have e4 : ssumEval [pr] (F.take k) = (if pr.2 = F.take k then pr.1 else (0:ℤ)) := by
      unfold ssumEval
      simp
    rw [e4]
    by_cases h : pr.2 = F.take k <;> simp [h]
  rw [list_map_congr_of _ _ _ (fun k _ => e3 k), sum_range_ite_take]
  by_cases h : pr.2.length ≤ F.length ∧ F.take pr.2.length = pr.2 <;> simp [h]

theorem ssumEval_ssumMul (x y : SSum) (F : Forest) :
    ssumEval (ssumMul x y) F
      = ((List.range (F.length + 1)).map fun k => ssumEval x (F.take k) * ssumEval y (F.drop k)).sum := by
  induction x with
  | nil =>
      have e1 : ssumMul ([] : SSum) y = [] := rfl
      rw [e1, ssumEval_nil]
      have hpw : ∀ k ∈ List.range (F.length + 1),
          ssumEval ([] : SSum) (F.take k) * ssumEval y (F.drop k) = 0 := by
        intro k _
        rw [ssumEval_nil, zero_mul]
      exact (list_sum_map_zero_of _ _ hpw).symm
  | cons pr x ih =>
      have hsplit : ssumMul (pr :: x) y = ssumMul [pr] y ++ ssumMul x y := by
        simp only [ssumMul, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [hsplit, ssumEval_add, ih, ssumEval_ssumMul_single]
      rw [← List.sum_map_add]
      have hpw : ∀ k ∈ List.range (F.length + 1),
          ssumEval [pr] (F.take k) * ssumEval y (F.drop k)
            + ssumEval x (F.take k) * ssumEval y (F.drop k)
            = ssumEval (pr :: x) (F.take k) * ssumEval y (F.drop k) := by
        intro k _
        have e : ssumEval (pr :: x) (F.take k)
            = ssumEval [pr] (F.take k) + ssumEval x (F.take k) := by
          have hcc : (pr :: x) = [pr] ++ x := rfl
          rw [hcc, ssumEval_add]
        rw [e, add_mul]
      rw [list_map_congr_of _ _ _ hpw]

theorem ssumEval_ssumMul_congr {x₁ x₂ y₁ y₂ : SSum} (F : Forest)
    (hx : ∀ A, ssumEval x₁ A = ssumEval x₂ A)
    (hy : ∀ B, ssumEval y₁ B = ssumEval y₂ B) :
    ssumEval (ssumMul x₁ y₁) F = ssumEval (ssumMul x₂ y₂) F := by
  rw [ssumEval_ssumMul, ssumEval_ssumMul]
  simp only [hx, hy]

theorem ssumEval_ssumMul_singleton_congr {x₁ x₂ : SSum} (G₀ F : Forest)
    (hx : ∀ A, ssumEval x₁ A = ssumEval x₂ A) :
    ssumEval (ssumMul x₁ [(1, G₀)]) F = ssumEval (ssumMul x₂ [(1, G₀)]) F :=
  ssumEval_ssumMul_congr F hx (fun _ => rfl)

theorem ssumEval_mul_one_right (x : SSum) (F : Forest) :
    ssumEval (ssumMul x [(1, [])]) F = ssumEval x F := by
  have e : ∀ pr₁ : ℤ × Forest,
      (if pr₁.2 ++ ([] : Forest) = F then pr₁.1 * 1 else (0:ℤ))
        = (if pr₁.2 = F then pr₁.1 else 0) := by
    intro pr₁
    by_cases h : pr₁.2 ++ ([] : Forest) = F
    · have h2 : pr₁.2 = F := by simpa using h
      simp [h, h2]
    · have h2 : ¬ pr₁.2 = F := by simpa using h
      simp [h, h2]
  have inner : ∀ pr₁ : ℤ × Forest,
      ((([(pr₁.1 * 1, pr₁.2 ++ ([] : Forest))].map
        fun p => if p.2 = F then p.1 else (0:ℤ))).sum)
        = (if pr₁.2 = F then pr₁.1 else 0) := by
    intro pr₁
    rw [List.map_singleton, List.sum_singleton]
    show (if pr₁.2 ++ ([] : Forest) = F then pr₁.1 * 1 else (0:ℤ)) = _
    exact e pr₁
  simp only [ssumMul, List.flatMap_singleton]
  unfold ssumEval
  rw [List.map_flatMap, sum_flatMap_aux]
  simp only [inner]

theorem foldr_eval_gen (term : Forest × Forest → SSum) (F : Forest) :
    ∀ (L : List (Forest × Forest)) (init : SSum),
    ssumEval (L.foldr (fun pr acc => ssumAdd (term pr) acc) init) F
      = (L.map fun pr => ssumEval (term pr) F).sum + ssumEval init F := by
  intro L
  induction L with
  | nil => intro init; simp
  | cons a L ih =>
      intro init
      rw [List.foldr_cons]
      have h2 : ssumEval (ssumAdd (term a) (L.foldr (fun pr acc => ssumAdd (term pr) acc) init)) F
          = ssumEval (term a) F + ssumEval (L.foldr (fun pr acc => ssumAdd (term pr) acc) init) F :=
        ssumEval_add _ _ _
      rw [h2, ih, List.map_cons, List.sum_cons]
      ac_rfl

theorem foldr_eval_additive (M₁ M₂ : Multiset (Forest × Forest))
    (term : Forest × Forest → SSum) (F : Forest) :
    ssumEval ((M₁ + M₂).toList.foldr (fun pr acc => ssumAdd (term pr) acc) []) F
      = ssumEval (M₁.toList.foldr (fun pr acc => ssumAdd (term pr) acc) []) F
        + ssumEval (M₂.toList.foldr (fun pr acc => ssumAdd (term pr) acc) []) F := by
  have hperm : List.Perm (M₁ + M₂).toList (M₁.toList ++ M₂.toList) := by
    rw [← Multiset.coe_eq_coe]
    rw [Multiset.coe_toList, ← Multiset.coe_add, Multiset.coe_toList, Multiset.coe_toList]
  have hperm_eval : ∀ L₁ L₂ : List (Forest × Forest), List.Perm L₁ L₂ →
      ssumEval (L₁.foldr (fun pr acc => ssumAdd (term pr) acc) []) F
        = ssumEval (L₂.foldr (fun pr acc => ssumAdd (term pr) acc) []) F := by
    intro L₁ L₂ h
    have e1 := foldr_eval_gen term F L₁ []
    have e2 := foldr_eval_gen term F L₂ []
    rw [e1, e2, ssumEval_nil, add_zero, add_zero]
    exact List.Perm.sum_eq (h.map _)
  rw [hperm_eval _ _ hperm, List.foldr_append]
  simp only [foldr_eval_gen, ssumEval_nil, add_zero]

theorem foldr_eval_multiset (M : Multiset (Forest × Forest))
    (term : Forest × Forest → SSum) (F : Forest) :
    ssumEval (M.toList.foldr (fun pr acc => ssumAdd (term pr) acc) []) F
      = (M.map fun pr => ssumEval (term pr) F).sum := by
  induction M using Multiset.induction_on with
  | empty =>
      simp [Multiset.toList_zero, ssumEval_nil]
  | cons a s ih =>
      rw [← Multiset.singleton_add, foldr_eval_additive, Multiset.map_add, Multiset.sum_add, ih]
      congr 1
      rw [Multiset.toList_singleton]
      simp only [List.foldr_cons, List.foldr_nil, ssumAdd, List.append_nil,
        Multiset.map_singleton, Multiset.sum_singleton, add_zero]

/-- Stability of `antipodeForest` under evaluation when the bound grows,
    for forests of sufficiently small trees. -/
def Stab (N : Nat) : Prop :=
  ∀ P : Forest, (∀ u ∈ P, treeSize u ≤ N) → ∀ G : Forest,
    ssumEval (antipodeForest (N+1) P) G = ssumEval (antipodeForest N P) G

/-- Stability of `antipodeTree` under evaluation when the bound grows. -/
def TreeStab (N : Nat) : Prop :=
  ∀ u : RKTree, treeSize u ≤ N → ∀ G : Forest,
    ssumEval (antipodeTree (N+1) u) G = ssumEval (antipodeTree N u) G

/-- The evaluated antipode axiom at bound `N`. -/
def AxiomN (N : Nat) : Prop :=
  ∀ t : RKTree, 0 < treeSize t → treeSize t ≤ N → ∀ F : Forest,
    ssumEval (antipodeAxiomSum N t) F = 0

theorem stab_treeStab_axiomN : ∀ N, Stab N ∧ TreeStab N ∧ AxiomN N := by
  intro N
  induction N with
  | zero =>
      refine ⟨?_, ?_, ?_⟩
      · show ∀ P : Forest, (∀ u ∈ P, treeSize u ≤ 0) → ∀ G : Forest,
            ssumEval (antipodeForest (0+1) P) G = ssumEval (antipodeForest 0 P) G
        intro P hP G
        have hempty : P = [] := by
          rw [List.eq_nil_iff_forall_not_mem]
          intro u hmem
          have h1 := hP u hmem
          have h2 := treeSize_pos u
          omega
        rw [hempty]
        simp only [antipodeForest]
      · show ∀ u : RKTree, treeSize u ≤ 0 → ∀ G : Forest,
            ssumEval (antipodeTree (0+1) u) G = ssumEval (antipodeTree 0 u) G
        intro u hu G
        have h2 := treeSize_pos u
        omega
      · show ∀ t : RKTree, 0 < treeSize t → treeSize t ≤ 0 → ∀ F : Forest,
            ssumEval (antipodeAxiomSum 0 t) F = 0
        intro t h0 hN F
        omega
  | succ N ih =>
      obtain ⟨hS, hT, hA⟩ := ih
      have hT' : TreeStab (N+1) := by
        show ∀ u : RKTree, treeSize u ≤ N+1 → ∀ G : Forest,
          ssumEval (antipodeTree (N+1+1) u) G = ssumEval (antipodeTree (N+1) u) G
        intro u hu G
        cases u with
        | node ts =>
            have hts : treeSize (RKTree.node ts) = 1 + (ts.map treeSize).sum := by
              unfold treeSize; simp
            simp only [antipodeTree, ssumEval_neg]
            rw [foldr_eval_multiset, foldr_eval_multiset]
            congr 1
            congr 1
            apply Multiset.map_congr rfl
            intro pr hmem
            obtain ⟨P, R⟩ := pr
            show ssumEval (ssumMul (antipodeForest (N+1) P) [(1, [RKTree.node R])]) G
                = ssumEval (ssumMul (antipodeForest N P) [(1, [RKTree.node R])]) G
            have hPlt : ∀ v ∈ P, treeSize v ≤ N := by
              intro v hv
              have h1 : treeSize v ≤ (P.map treeSize).sum :=
                List.le_sum_of_mem (List.mem_map.mpr ⟨v, hv, rfl⟩)
              have h2 : (P.map treeSize).sum ≤ (ts.map treeSize).sum :=
                coprod_pruned_bound ts P R hmem
              omega
            exact ssumEval_ssumMul_singleton_congr _ _ (hS P hPlt)
      refine ⟨?_, hT', ?_⟩
      · show ∀ P : Forest, (∀ u ∈ P, treeSize u ≤ N+1) → ∀ G : Forest,
            ssumEval (antipodeForest (N+1+1) P) G = ssumEval (antipodeForest (N+1) P) G
        intro P
        induction P with
        | nil =>
            intro hP G
            simp only [antipodeForest]
        | cons u us ihP =>
            intro hP G
            have hu : treeSize u ≤ N + 1 := hP u (by simp)
            have hus : ∀ v ∈ us, treeSize v ≤ N + 1 := fun v hv => hP v (by simp [hv])
            simp only [antipodeForest]
            exact ssumEval_ssumMul_congr G (hT' u hu) (ihP hus)
      · show ∀ t : RKTree, 0 < treeSize t → treeSize t ≤ N+1 → ∀ F : Forest,
            ssumEval (antipodeAxiomSum (N+1) t) F = 0
        intro t h0 hN F
        cases t with
        | node ts =>
            have hts : treeSize (RKTree.node ts) = 1 + (ts.map treeSize).sum := by
              unfold treeSize; simp
            have step1 : ssumEval (antipodeAxiomSum (N+1) (RKTree.node ts)) F
                = ((treeCoprod (RKTree.node ts)).map fun pr =>
                    ssumEval (ssumMul (antipodeForest (N+1) pr.1) [(1, pr.2)]) F).sum := by
              simp only [antipodeAxiomSum]
              rw [foldr_eval_multiset]
            rw [step1, treeCoprod_node, Multiset.map_add, Multiset.sum_add]
            have eSing : ((({((([RKTree.node ts], [])))} : Multiset (Forest × Forest))).map fun pr =>
                ssumEval (ssumMul (antipodeForest (N+1) pr.1) [(1, pr.2)]) F).sum
                = ssumEval (ssumMul (antipodeForest (N+1) [RKTree.node ts]) [(1, ([] : Forest))]) F := by
              simp only [Multiset.map_singleton, Multiset.sum_singleton]
            have term1 : ssumEval (ssumMul (antipodeForest (N+1) [RKTree.node ts]) [(1, ([] : Forest))]) F
                = ssumEval (antipodeTree (N+1) (RKTree.node ts)) F := by
              rw [ssumEval_mul_one_right]
              have e1 : antipodeForest (N+1) [RKTree.node ts]
                  = ssumMul (antipodeTree (N+1) (RKTree.node ts)) (antipodeForest (N+1) []) := by
                simp only [antipodeForest]
              have e2 : antipodeForest (N+1) ([] : Forest) = ssumOne := by
                simp only [antipodeForest]
              rw [e1, e2]
              exact ssumEval_mul_one_right _ _
            have term2 : ((((forestCoprod ts).bind fun pr => {((pr.1, [RKTree.node pr.2]))}).map fun pr =>
                ssumEval (ssumMul (antipodeForest (N+1) pr.1) [(1, pr.2)]) F)).sum
                = (((forestCoprod ts).map fun pr =>
                    ssumEval (ssumMul (antipodeForest N pr.1) [(1, [RKTree.node pr.2])]) F)).sum := by
              rw [Multiset.bind_singleton, Multiset.map_map]
              congr 1
              apply Multiset.map_congr rfl
              intro pr hmem
              obtain ⟨P, R⟩ := pr
              show ssumEval (ssumMul (antipodeForest (N+1) P) [(1, [RKTree.node R])]) F
                  = ssumEval (ssumMul (antipodeForest N P) [(1, [RKTree.node R])]) F
              have hPlt : ∀ v ∈ P, treeSize v ≤ N := by
                intro v hv
                have h1 : treeSize v ≤ (P.map treeSize).sum :=
                  List.le_sum_of_mem (List.mem_map.mpr ⟨v, hv, rfl⟩)
                have h2 : (P.map treeSize).sum ≤ (ts.map treeSize).sum :=
                  coprod_pruned_bound ts P R hmem
                omega
              exact ssumEval_ssumMul_singleton_congr _ _ (hS P hPlt)
            have eTree : ssumEval (antipodeTree (N+1) (RKTree.node ts)) F
                = -(((forestCoprod ts).map fun pr =>
                    ssumEval (ssumMul (antipodeForest N pr.1) [(1, [RKTree.node pr.2])]) F)).sum := by
              simp only [antipodeTree, ssumEval_neg]
              rw [foldr_eval_multiset]
            rw [eSing, term1, term2, eTree]
            exact neg_add_cancel _

/-- The corrected antipode axiom (evaluation into the group ring) holds. -/
theorem antipodeAxiomEval_proved : antipodeAxiomEval := by
  intro n t h0 hN F
  exact (stab_treeStab_axiomN n).2.2 t h0 hN F


end ThetLogos
