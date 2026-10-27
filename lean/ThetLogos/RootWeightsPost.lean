import Mathlib.Data.Fin.VecNotation
import ThetLogos.ThermalClock
import ThetLogos.ThermalKernel

/-!
# ThetLogos.RootWeightsPost — Q-ROOT: the triad as weights (Tier T5, open)

**Origin (Jeff, 2026-10-27 ~00:56 EDT, his coinage, verbatim):**
"no it's -1 the void +2 inside the 0 unity" — amending his containment
formula "1 split into 2 contained in 0" (2026-10-24). The triad named
there: **−1** the void, **0** the unity-container, **+2** the pair.

**The three floors, graded separately in the scoping memo
(`proto-root-ternary-202-scoping-2026-10-27`), in three lines:**

- **Floor 1 — notation: STANDS.** The triad is Jeff's doctrine: void,
  container, pair; its arithmetic checks (−1 + 0 + 2 = +1; −1 + 2 = 1).
- **Floor 2 — numeral root: KILLED.** As digits {−1, 0, 2}: base 3
  cannot write any integer ≡ 1 (mod 3), including 1 itself; base 2 is
  complete except exactly +1, its recursion's fixed point — the system
  cannot write the One; digitwise negation is impossible (−2 ∉ D).
- **Floor 3 — tripotent values: KILLED, by landed theorems.**
  `scalar_tripotent_iff` and `tripotent_selfadjoint_spectrum` force
  tripotent spectra into {−1, 0, 1} (μ³ = μ); no rescaling produces
  the asymmetric triple either (scaled spectra stay symmetric).

**The open residue — the only content of this post.** Floors 2 and 3
kill (−1, 0, 2) as a numeral root and as tripotent *values*. They have
no jurisdiction over **weights**: weighting is Jeff's allocation
doctrine ("to each its need, not equality" — the ThermalKernel pays
each mode (λᵢ)⁻¹, its own reciprocal rate; equipartition is the flat
special case). The triad is *normalized* — its weights sum to exactly
+1, the normalization every state in the corpus carries — but it is
not *faithful*: its void seat is negative and its container seat is
zero. The posted question is whether any allocation/kernel object in
the corpus realizes it anyway.

**Why the question is posed at this level.** The sharpest formulation —
a signed thermal clock, normalized but unfaithful, whose weights are
produced by the heat kernel at unit time (the `ThermalKernel` jewel:
`heatKernel (fun j => −log (weights j)) 1 = Matrix.diagonal weights`) —
needs data the corpus does not have: `ThermalClock` bakes faithfulness
in as a structure field, the jewel's `−log` weights require positivity,
and no signed-state type exists anywhere in the tree (checked). So the
question is posed at the sharpest *owned* level: the corpus's three
canonical allocation modes — clock weights, Gibbs weights, and the
payoff allocation in the domain where its payoff identity is proved
(`integral_exp_neg_mul_Ioi`, rates > 0).

**The fences, stated before any answer.** Each canonical mode is
individually positivity-fenced by landed facts: a clock's `faithful`
field; Gibbs weights are exponentials, hence strictly positive; payoff
reciprocals of positive rates are positive. (Even the bare reciprocal
formula outside its proved domain only half-escapes: it hits the void
seat at λ = −1 and the pair seat at λ = 1/2, but λ⁻¹ = 0 has no finite
rate — the container seat is missed there too.) A **kill** is the
assembly of these three fences into the statement that the owned
allocation machinery is faithful-only. A **promote** is the exhibition
of owned data in one of the three modes — or, as a NEW entry under the
relabeling rule (never as this post's retrofitted answer), a
corpus-native signed allocation object realizing the triad.

**This post's own kill conditions (from the scoping, pre-named).**
**K-ROOT-1** — if a landed (−1, 0, 2)-weighted object is found in the
tree, the answer collapses to a citation receipt and the line closes
ALREADY OWNED; it is not a discovery. **K-ROOT-2** — any wording
re-posing the decided questions (the ternary *root*, tripotent
*values*) is killed on sight: those are decided (NO), and the
relabeling rule forbids re-posing them. This post asks about weights
only.

**Status: Tier T5 question-post. NO CLAIM.** Following the
`BlockedQuestions` ledger rule: the placeholder below is a
**formalized question**, never an answer. Nothing in this module
decides anything; the definitions are Tier T2 data, the question is
the placeholder.
-/

namespace ThetLogos

/-- **Jeff's triad as a weight assignment on three seats** (Tier T2,
    data): seat 0 is the void, assigned −1; seat 1 is the
    unity-container, assigned 0; seat 2 is the pair, assigned +2.
    The assignment is normalized — its entries sum to +1 — but not
    faithful: the void seat is negative and the container seat is
    zero, where every state weight in the corpus is strictly
    positive. -/
def rootTriadWeights : Fin 3 → ℝ := ![(-1 : ℝ), 0, 2]

/-- **Realization by owned allocation data** (Tier T2). A three-seat
    weight assignment `w` is *realized* when it is the weight function
    assigned by one of the corpus's three canonical allocation
    mechanisms:

    - **(clock)** the weights of a `ThermalClock 3`;
    - **(Gibbs)** `gibbsDiagWeights` of some inverse temperature,
      spectrum, and log-partition value;
    - **(payoff)** the ThermalKernel payoff allocation
      `s ↦ (lam s)⁻¹` of a positive rate function `lam` — the domain
      in which `integral_exp_neg_mul_Ioi` proves that a mode's total
      payment is exactly its reciprocal rate. -/
def RootWeightsRealized (w : Fin 3 → ℝ) : Prop :=
  (∃ C : ThermalClock 3, C.weights = w) ∨
    (∃ (β logZ : ℝ) (lam : Fin 3 → ℝ), gibbsDiagWeights β lam logZ = w) ∨
    (∃ lam : Fin 3 → ℝ, (∀ s, 0 < lam s) ∧ (fun s => (lam s)⁻¹) = w)

/-- Definitional unfolding of `RootWeightsRealized` (Tier T1 — the
    predicate is exactly the three-mode disjunction, by definition). -/
theorem rootWeightsRealized_iff (w : Fin 3 → ℝ) :
    RootWeightsRealized w ↔
      (∃ C : ThermalClock 3, C.weights = w) ∨
        (∃ (β logZ : ℝ) (lam : Fin 3 → ℝ), gibbsDiagWeights β lam logZ = w) ∨
        (∃ lam : Fin 3 → ℝ, (∀ s, 0 < lam s) ∧ (fun s => (lam s)⁻¹) = w) :=
  Iff.rfl

/-- **Q-ROOT, open (Tier T5, placeholder):** Jeff's triad
    (−1, 0, 2) — void, unity-container, pair — is realized as
    *weights* by some allocation/kernel object of the corpus, in one
    of the three canonical modes of `RootWeightsRealized`.

    Promote: exhibit the data (one mode suffices) — or open a new
    entry for a corpus-native signed allocation object; this post is
    not retrofitted. Kill: assemble the three landed positivity
    fences (clock faithfulness; Gibbs weights are exponentials;
    payoff reciprocals of positive rates) into the faithful-only
    statement at this owned level. -/
theorem rootWeights_realized : RootWeightsRealized rootTriadWeights := by
  sorry

end ThetLogos
