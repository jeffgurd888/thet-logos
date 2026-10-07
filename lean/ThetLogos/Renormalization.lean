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
  coproduct computations on •, 𝔩₂, V.
- **Blocked (precise obstructions below):** coassociativity, antipode.
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
