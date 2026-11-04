import Mathlib.Tactic
import ThetLogos.BridgeCompletion
import ThetLogos.ThermalChargePoisson
import ThetLogos.ModularVariance

/-!
# ThetLogos.PrimordialsExhibit — the are/do duality inside the corpus's own grammar

HONESTY LEDGER (read before citing):

- COMMISSION. Jeff's seeing (2026-11-04 ~11:16, T5, filed verbatim
  in `~/memory/2026-11-04.md`): "our primordials are mathematics
  physics and correlations of letters and meanings. in language
  words are and do while in mathematics numbers are objects or
  actions and the correlations to each in a unified
  language/letters/numbers/correlations/meaning/logic/reason".
  Jeff's commission: "build it" (2026-11-04 11:19). The bounded
  reading, executed here: build the formable core — the are/do
  duality inside the formal grammar the corpus already owns — and
  fence the rest as not-yet-statements (dossier pins N1–N5).
- WHAT THIS MODULE IS. In dependent type theory every term both
  IS (an object of the grammar: named, stored, passed) and, when
  its type is a function type, DOES (acts by application). This
  module pins that duality at the corpus's own seats: the graph
  Laplacian (`laplacianOp` / `lapLinFun`, BridgeLaplacian /
  BridgeCompletion), the scaling action of a real number on
  potentials, the evaluation action of a vertex name, and the
  Gibbs weight-object's action as an expectation functional
  (ModularVariance). The correlations between the two roles are
  stated as theorems about those seats: ring operations on
  action-objects act as the corresponding doings; a number's
  object-arithmetic correlates with its action-arithmetic; the
  number-action is faithful at an inhabited seat; evaluation of
  a number's action is multiplication; the number-action and the
  Laplacian action commute, by the corpus's own proved linearity.
- GRADE OF EACH ITEM, ON ITS FACE. DEFINITIONAL items are the
  grammar's own shadow (application of a packaged object is its
  unfolding) and are labeled as such — they pin the duality, they
  prove nothing. GENERIC items are the pinned Mathlib's structure
  instantiated at the seat, proved here pointwise. SEAT-CONTENT
  items consume facts the corpus itself proved (the Laplacian's
  linearity) or carry genuine hypotheses (faithfulness needs an
  inhabited seat: on an empty seat there are no potentials to act
  on and the correlation collapses — the hypothesis is in the
  statement, not hidden).
- WHAT THIS MODULE IS NOT. It is NOT a unified language of
  letters and meanings. No letter in this file means anything:
  the vertex names are indices, the operator names are Lean
  identifiers, and no syntax type, denotation map, or semantics
  is built or implied. The letters↔meaning correlation is T5,
  unbuilt; its pins (N1 syntax-with-denotation, N2 meaning,
  N3 natural language, N4 the mathematics↔physics correlation,
  N5 a unified-language object) are listed in the dossier
  `whitepaper/primordials-exhibit-landing-2026-11-04.md` for
  Jeff's hand. Jeff's seeing stands at T5 as filed; this module
  is its formable core and nothing more. NO CLAIM; dials 0/4.
-/

namespace ThetLogos

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## §1. The operator: one name, two roles

`laplacianOp w` in curried form is a doing waiting for arguments.
`lapLinFun w` (BridgeCompletion) is the same doing packaged as
ONE object — a citizen of the endomorphism ring of the potential
space, where action-objects can be added and multiplied as
objects. The landed bridge `lapLinFun_apply` (consumed, not
restated) says applying the object reproduces the action. -/

/-- **Actions compose into an object; the object acts by
iteration.** The product of the Laplacian action-object with
itself — an object, formed by ring multiplication in the
endomorphism ring — applied to a potential is the action applied
twice. (GENERIC grade: `LinearMap.mul_apply` at the seat, over
the landed `lapLinFun_apply`.) -/
theorem lapAction_mul_apply (w : V → V → ℝ) (F : V → ℝ) :
    (lapLinFun w * lapLinFun w) F = laplacianOp w (laplacianOp w F) := by
  rw [Module.End.mul_apply, lapLinFun_apply, lapLinFun_apply]

/-- **Action-objects add as objects; the sum acts as the sum of
the doings.** The sum of two Laplacian action-objects, applied to
a potential, is the pointwise sum of the two actions.
(GENERIC grade.) -/
theorem lapAction_add_apply (w w' : V → V → ℝ) (F : V → ℝ) :
    (lapLinFun w + lapLinFun w') F = laplacianOp w F + laplacianOp w' F := by
  rw [LinearMap.add_apply, lapLinFun_apply, lapLinFun_apply]

/-! ## §2. Numbers: objects that are actions

A real number `a` IS an object (a term of `ℝ`). It also DOES:
`numAction a` is the action-object "scale by `a`" on the
potential space. The theorems of this section are the
correlations between the number's object-arithmetic and its
action-arithmetic, and the faithfulness of the assignment. -/

/-- **The number as action-object.** `numAction a` is the linear
map "multiply by the number `a`", on potentials. The number
occupies the action seat as a single object. -/
def numAction (a : ℝ) : (V → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun F := a • F
  map_add' F G := smul_add a F G
  map_smul' c F := smul_comm a c F

omit [Fintype V] [DecidableEq V] in
/-- **Applying the number's action-object is the number's
doing:** scaling. (DEFINITIONAL grade — the object's unfolding.) -/
theorem numAction_apply (a : ℝ) (F : V → ℝ) :
    numAction a F = a • F := rfl

omit [Fintype V] [DecidableEq V] in
/-- **The number's doing, read at a vertex:** multiplication.
(GENERIC grade.) -/
theorem numAction_apply_apply (a : ℝ) (F : V → ℝ) (i : V) :
    numAction a F i = a * F i := by
  simp [numAction_apply]

/-- **The zero number is the zero action.** The object `0`,
acting, does nothing. (GENERIC grade.) -/
theorem numAction_zero : numAction (V := V) (0 : ℝ) = 0 := by
  ext F
  simp [numAction_apply]

/-- **The one number is the identity action.** The object `1`,
acting, leaves every potential alone. (GENERIC grade.) -/
theorem numAction_one : numAction (V := V) (1 : ℝ) = LinearMap.id := by
  ext F
  simp [numAction_apply]

omit [Fintype V] [DecidableEq V] in
/-- **CORRELATION (addition).** The sum of two numbers, as an
action-object, is the sum of the two action-objects: object
addition and action addition are the same fact read in the two
roles. (GENERIC grade.) -/
theorem numAction_add (a b : ℝ) :
    numAction (V := V) (a + b) = numAction (V := V) a + numAction (V := V) b := by
  refine LinearMap.ext fun F => ?_
  rw [LinearMap.add_apply, numAction_apply, numAction_apply, numAction_apply,
    add_smul]

omit [Fintype V] [DecidableEq V] in
/-- **CORRELATION (multiplication).** The product of two
numbers, as an action-object, is the composition (endomorphism
product) of the two action-objects: object multiplication and
action composition are the same fact read in the two roles.
(GENERIC grade.) -/
theorem numAction_mul (a b : ℝ) :
    numAction (V := V) (a * b) = numAction (V := V) a * numAction (V := V) b := by
  refine LinearMap.ext fun F => ?_
  rw [Module.End.mul_apply, numAction_apply, numAction_apply, numAction_apply,
    smul_smul]

omit [Fintype V] [DecidableEq V] in
/-- **FAITHFULNESS (seat content).** At an inhabited seat, the
assignment number ↦ action is injective: distinct numbers are
distinct actions, so the number's are-role and do-role determine
each other. The hypothesis has teeth — on an empty seat there
are no potentials, every action-object coincides, and the
correlation collapses; that case is excluded by the hypothesis,
on the face. -/
theorem numAction_injective [Nonempty V] :
    Function.Injective (numAction : ℝ → (V → ℝ) →ₗ[ℝ] (V → ℝ)) := by
  intro a b h
  obtain ⟨i₀⟩ := ‹Nonempty V›
  have h2 : numAction a (fun _ => (1 : ℝ)) i₀
      = numAction b (fun _ => (1 : ℝ)) i₀ := by rw [h]
  simpa [numAction_apply] using h2

/-! ## §3. Names act: evaluation

A vertex `i : V` is a pure object — the seat's "letter". It also
DOES: evaluation at `i` is a linear action on the space of
potentials. And the totality of the names' actions determines
the object acted on: that determination is the correlation
between an object and everything the letters can ask of it. -/

/-- **The name as action-object.** `evalAt i` is the evaluation
functional at the vertex `i`: the letter `i`, occupying the
action seat as a single linear object. -/
def evalAt (i : V) : (V → ℝ) →ₗ[ℝ] ℝ where
  toFun F := F i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype V] [DecidableEq V] in
/-- **Applying the name's action-object is the name's doing:**
reading the potential at that vertex. (DEFINITIONAL grade.) -/
theorem evalAt_apply (i : V) (F : V → ℝ) : evalAt i F = F i := rfl

omit [Fintype V] [DecidableEq V] in
/-- **DETERMINATION.** A potential is exactly the totality of
what the names' actions return: if every letter's evaluation
agrees on two potentials, the potentials are equal. The object
IS the correlation of all its readings. (GENERIC grade: this is
`funext` at the seat, stated in the exhibit's vocabulary.) -/
theorem eq_of_evalAt_eq (F G : V → ℝ)
    (h : ∀ i, evalAt i F = evalAt i G) : F = G := by
  funext i
  exact h i

omit [Fintype V] [DecidableEq V] in
/-- **The two role-systems correlate at a point.** A name's
evaluation of a number's action is multiplication of the reading
by the number: letters and numbers, acting on the same object,
compose to arithmetic. (GENERIC grade.) -/
theorem evalAt_numAction (a : ℝ) (F : V → ℝ) (i : V) :
    evalAt i (numAction a F) = a * evalAt i F := by
  simp [evalAt_apply, numAction_apply]

/-! ## §4. The weight acts: the Gibbs functional

On the Gibbs seat (ModularVariance), the weight
`gibbsProb E β` is an object — a function on sectors. It also
DOES: as a functional on observables it returns the expectation,
and at the energy observable it returns the mean energy — a
number produced by one object acting on another. -/

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- **A weight as action-object.** `weightFunctional u` is the
linear functional "pair with the weight `u`": the weight-object
occupying the action seat. -/
def weightFunctional (u : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun X := ∑ i, u i * X i
  map_add' X Y := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by simp [mul_add])
  map_smul' c X := by
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)

omit [Nonempty ι] in
/-- **Applying the weight's action-object is the weight's
doing:** the pairing sum. (DEFINITIONAL grade.) -/
theorem weightFunctional_apply (u X : ι → ℝ) :
    weightFunctional u X = ∑ i, u i * X i := rfl

omit [Nonempty ι] in
/-- **The Gibbs weight, acting, is the Gibbs expectation.** The
state's weight-object, in the action seat, returns exactly
`gibbsExpect` — the corpus's expectation is the weight's doing,
packaged. (DEFINITIONAL grade: the two definitions unfold to the
same sum; the exhibit pins that they are one fact in two roles.) -/
theorem weightFunctional_gibbsProb (E : ι → ℝ) (β : ℝ) (X : ι → ℝ) :
    weightFunctional (ModularVariance.gibbsProb E β) X
      = ModularVariance.gibbsExpect E β X := rfl

omit [Nonempty ι] in
/-- **The weight acting on the energy returns the mean energy.**
One object (the Gibbs weight) acts on another object (the
energy observable) and the correlation lands on a number:
`meanEnergy`. (DEFINITIONAL grade, via the previous item.) -/
theorem gibbsWeight_act_energy (E : ι → ℝ) (β : ℝ) :
    weightFunctional (ModularVariance.gibbsProb E β) E
      = ModularVariance.meanEnergy E β :=
  weightFunctional_gibbsProb E β E

/-! ## §5. The roles commute where the grammar says they must

The number's doing and the operator's doing, acting on the same
potential in either order, agree. The reason is not a metaphor
about unity: it is the corpus's own proved linearity of its
Laplacian (the `map_smul'` field of `lapLinFun` is the landed
`laplacianOp_smul`). The correlation between the roles is
exactly as strong as the linearity the corpus proved — no
stronger. -/

/-- **COMMUTATION CORRELATION (seat content).** Scaling a
potential and then applying the Laplacian is applying the
Laplacian and then scaling: the number's action and the
operator's action commute, because the operator is linear —
a theorem the corpus proved about its own operator, consumed
here as the correlation between the two role-systems. -/
theorem numAction_comm_lap (a : ℝ) (w : V → V → ℝ) (F : V → ℝ) :
    lapLinFun w (numAction a F) = numAction a (lapLinFun w F) := by
  rw [numAction_apply, numAction_apply, map_smul]

end ThetLogos
