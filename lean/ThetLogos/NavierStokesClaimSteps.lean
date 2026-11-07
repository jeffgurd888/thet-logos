import ThetLogos.NavierStokesClaimClassify

namespace ThetLogos

/-!
# ThetLogos.NavierStokesClaimSteps — claim-tester step analysis (CT-2)

Board charter: **NO CLAIM.** Parts of the Clay Navier–Stokes
problem closed by this house: **0**. This module is the Q3 half
of the claim-tester model pinned at CT-0
(`ThetLogos.NavierStokesClaimPin`) and classified at CT-1
(`ThetLogos.NavierStokesClaimClassify`): **does a candidate
claim's derivation smuggle in a negation step between
alternatives — and is that step valid at the pin's quantifier
shape?** Answered here as proved non-entailment at the level of
logical shape, with explicit countermodels.

## Method, stated plainly

The alternatives are abstracted to their quantifier SHAPES over
a per-(ν, data) solution predicate `Sol` and admissibility
predicates: the existence shape (`nsAShape`: `∀ ν > 0`, `∀`
admissible initial data, `∀` zero forcing, solution) shared by
(A) and (B), and the breakdown shape (`nsCShape`: `∀ ν > 0`,
`∃` admissible data with no solution) shared by (C) and (D). The
four bridge theorems below tie the shapes definitionally to the
pin's own `Prop`s (`Iff.rfl` for (A), (C), (D); a currying
conversion for (B), whose zero-forcing package is two
hypotheses). A negation step `¬src → tgt` is ENTAILED at shape
level iff every assignment to `Sol` and the predicates making
`¬(src shape)` true makes `tgt shape` true; the countermodels
here are assignments refuting that — they refute inference
FORMS. **They assert nothing about the truth values of the
actual alternatives** (assignments to the actual `nsSolR3` /
`nsSolTorus` would be analysis, i.e. the Clay problem itself).
K-NS-1 discipline holds throughout: no alternative is asserted
non-vacuous; there is no existence content in this module.

## Findings (all proved below)

1. **At the pin's regime, every cross-alternative negation step
   is blocked.** The same-domain steps (¬C→A, ¬A→C, ¬D→B, ¬B→D)
   are blocked by the ν-quantification ALONE: the countermodels
   `ν = 1` (solvable exactly at one viscosity) and `ν ≠ 1`
   (solvable except at one viscosity) use TRIVIAL admissibility
   predicates — every inclusion, in particular the zero-forcing
   admissibility inclusion, is GRANTED — and the steps still
   fail, because `¬C` as composed yields A's content at a single
   viscosity while A quantifies over all `ν > 0`, and `¬A` as
   composed yields C's witness at a single viscosity while C
   quantifies over all `ν > 0`. The cross-domain steps are
   blocked at every regime (domain, and the same ν assignments).
   All twelve ordered steps are proved below.

2. **At a fixed viscosity, the same-domain steps turn on
   exactly one further ingredient.** With `Sol`, the predicates,
   and a SINGLE shared `ν`, each direction is pure logic GIVEN
   the admissibility inclusion `∀ f, Zero f → Force f`
   (`nsFixedNu_notC_imp_A`, `nsFixedNu_notA_imp_C`) — and WITHOUT
   the inclusion each direction fails even at fixed `ν`
   (one shared countermodel: solutions exist exactly on the
   admissible class `{false}`, the zero forcing `true` lies
   outside it). So the exact status of every step is: blocked by
   ν as pinned; at ambient ν, blocked by shape alone unless the
   zero-forcing admissibility inclusion is supplied, with which
   it is pure logic. This is the content behind the frozen
   `nsStepStatus` table of CT-0.

3. **CT-3 — the ¬A → C reading stays a reading.** Nothing here
   states ¬A → C (or any step) as a theorem about the pin's
   `Prop`s. The refinement this module adds to the board's
   record, at full rank: the NS-1b header calls ¬A ⇒ C "the one
   implication that does hold for the `Prop`s as composed here"
   while (correctly) withholding theorem status from it; the
   shape analysis shows that AS COMPOSED (`∀ν` inside each
   `Prop`) the implication needs the ambient-ν reading as well
   as the admissibility inclusion — NS-0's "¬A ⇒ C and ¬C ⇒ A
   hold" is the ambient-reading statement, and the pin's own
   header already records the matching failure of ¬C ⇒ A under
   the composition. The pin's statements are untouched and
   K-NS-1 does not fire on them; what is refined is one prose
   sentence about them, and the refinement is recorded here and
   in the line's ledger record, not edited into the pin.

Honesty tiers in this file:
- **T1 (proved):** the bridges, the non-entailment theorems,
  the fixed-ν implications and countermodels, the step-status
  exhibits — all about the statement's LOGICAL SHAPE.
- **NO CLAIM:** existence, smoothness, breakdown — untouched.
  This module proves things about the statement, not about
  Navier–Stokes.
-/

/-- The (A)/(C) solution conjunction as a per-(ν, data)
predicate: `∃ u p`, the system + joint smoothness (6) + bounded
energy (7). This is the concrete `Sol` of the ℝ³ shape. -/
def nsSolR3 (ν : ℝ) (u0 : NSInitialField) (f : NSForcingField) : Prop :=
  ∃ u p, NavierStokesSystem ν u0 f u p ∧ NSSolutionSmooth u p ∧
    NSBoundedEnergy u

/-- The (B)/(D) solution conjunction as a per-(ν, data)
predicate: `∃ u p`, the system + solution periodicity (10 +
errata clause) + joint smoothness (11) + bounded energy on the
torus. The concrete `Sol` of the torus shape. -/
def nsSolTorus (ν : ℝ) (u0 : NSInitialField) (f : NSForcingField) : Prop :=
  ∃ u p, NavierStokesSystem ν u0 f u p ∧ NSSolutionPeriodic u p ∧
    NSSolutionSmooth u p ∧ NSBoundedEnergyTorus u

section Shape

variable {ι φ : Type*}

/-- **The existence shape** (alternatives (A) and (B)): for
every `ν > 0`, every admissible initial datum, and every
zero forcing, a solution exists. `Sol` is the per-(ν, data)
solution predicate; `Init` and `Zero` are the admissibility
predicates for initial data and for the (zero) forcing. -/
def nsAShape (Sol : ℝ → ι → φ → Prop) (Init : ι → Prop)
    (Zero : φ → Prop) : Prop :=
  ∀ ν, 0 < ν → ∀ u0, Init u0 → ∀ f, Zero f → Sol ν u0 f

/-- **The breakdown shape** (alternatives (C) and (D)): for
every `ν > 0` there is admissible data — initial datum and
forcing in the admissible class — with no solution. -/
def nsCShape (Sol : ℝ → ι → φ → Prop) (Init : ι → Prop)
    (Force : φ → Prop) : Prop :=
  ∀ ν, 0 < ν → ∃ u0 f, Init u0 ∧ Force f ∧ ¬ Sol ν u0 f

/-- **Bridge (T1):** alternative (A) IS the existence shape at
the concrete ℝ³ packages. Definitional — `Iff.rfl`. Asserts
nothing about Navier–Stokes. -/
theorem nsAlternativeA_as_shape :
    NSAlternativeA ↔ nsAShape nsSolR3 NSInitialDataR3 NSZeroForcing :=
  Iff.rfl

/-- **Bridge (T1):** alternative (C) IS the breakdown shape at
the concrete ℝ³ packages. Definitional — `Iff.rfl`. -/
theorem nsAlternativeC_as_shape :
    NSAlternativeC ↔ nsCShape nsSolR3 NSInitialDataR3 NSForcingDataR3 :=
  Iff.rfl

/-- **Bridge (T1):** alternative (D) IS the breakdown shape at
the concrete torus packages. Definitional — `Iff.rfl`. -/
theorem nsAlternativeD_as_shape :
    NSAlternativeD ↔ nsCShape nsSolTorus NSInitialDataTorus
      NSForcingDataTorus :=
  Iff.rfl

/-- **Bridge (T1):** alternative (B) IS the existence shape at
the concrete torus packages, with (B)'s two zero-forcing
hypotheses (periodicity + `f ≡ 0`) read as one package — a
currying conversion, proved (not definitional: `P → Q → R` is
not `(P ∧ Q) → R` on the nose). -/
theorem nsAlternativeB_as_shape :
    NSAlternativeB ↔ nsAShape nsSolTorus NSInitialDataTorus
      (fun f => NSForcingPeriodic f ∧ NSZeroForcing f) := by
  constructor
  · intro h ν hν u0 hu f hf
    exact h ν hν u0 hu f hf.1 hf.2
  · intro h ν hν u0 hu f hp hz
    exact h ν hν u0 hu f ⟨hp, hz⟩

/-! ## The two viscosity assignments and the master lemmas

`fun ν _ _ => ν = 1`: solvable exactly at the single viscosity
`ν = 1`. `fun ν _ _ => ν ≠ 1`: solvable except at `ν = 1`. Both
ignore the data entirely, and the master lemmas are stated for
ARBITRARY admissibility predicates — the blockage they exhibit
is the ν-quantification alone, with every admissibility
inclusion granted. -/

/-- **Master lemma:** under the `ν = 1` assignment the breakdown
shape fails outright — at `ν = 1` no datum is unsolvable, so
the shape's `∀ ν` fails at its first test viscosity. For
arbitrary admissibility predicates. -/
theorem cmEqOne_not_breakdown (Init : ι → Prop) (Force : φ → Prop) :
    ¬ nsCShape (fun ν _ _ => ν = 1) Init Force := by
  intro hC
  obtain ⟨u0, f, -, -, hnsol⟩ := hC 1 one_pos
  exact hnsol rfl

/-- **Master lemma:** under the `ν = 1` assignment the existence
shape fails outright — at `ν = 2` the (granted) admissible datum
has no solution. For arbitrary admissibility predicates; the
datum is exhibited. -/
theorem cmEqOne_not_existence (Init : ι → Prop) (Zero : φ → Prop)
    (u0 : ι) (hu : Init u0) (f : φ) (hf : Zero f) :
    ¬ nsAShape (fun ν _ _ => ν = 1) Init Zero := by
  intro hA
  have h := hA 2 (by norm_num) u0 hu f hf
  exact (by norm_num : ¬ (2 : ℝ) = 1) h

/-- **Master lemma:** under the `ν ≠ 1` assignment the existence
shape fails outright — at `ν = 1` the (granted) admissible datum
has no solution. For arbitrary admissibility predicates; the
datum is exhibited. -/
theorem cmNeOne_not_existence (Init : ι → Prop) (Zero : φ → Prop)
    (u0 : ι) (hu : Init u0) (f : φ) (hf : Zero f) :
    ¬ nsAShape (fun ν _ _ => ν ≠ 1) Init Zero := by
  intro hA
  have h := hA 1 one_pos u0 hu f hf
  exact h rfl

/-- **Master lemma:** under the `ν ≠ 1` assignment the breakdown
shape fails outright — at `ν = 2` every datum is solvable, so no
breakdown witness exists there. For arbitrary admissibility
predicates. -/
theorem cmNeOne_not_breakdown (Init : ι → Prop) (Force : φ → Prop) :
    ¬ nsCShape (fun ν _ _ => ν ≠ 1) Init Force := by
  intro hC
  obtain ⟨u0, f, -, -, hnsol⟩ := hC 2 (by norm_num)
  exact hnsol (by norm_num)

/-! ## The twelve negation steps at the pin's regime — all blocked

Each theorem is the negation of the corresponding entailment at
shape level: an assignment (on the pin's own field types, with
trivial — i.e. fully granting — admissibility predicates) under
which the negated source shape holds and the target shape
fails. The (A)/(C) theorems use the ℝ³ reading of the shapes,
the (B)/(D) theorems the torus reading; the shape pair is one
(see the bridges), and the assignments are the master lemmas'
two. -/

/-- **¬C does NOT entail A** (the headline step): the `ν = 1`
assignment makes ¬(C-shape) true and (A-shape) false. -/
theorem nsNotC_not_entails_A :
    ∃ (Sol : ℝ → NSInitialField → NSForcingField → Prop)
      (Init : NSInitialField → Prop) (Force Zero : NSForcingField → Prop),
      ¬ nsCShape Sol Init Force ∧ ¬ nsAShape Sol Init Zero := by
  refine ⟨fun ν _ _ => ν = 1, fun _ => True, fun _ => True, fun _ => True,
    cmEqOne_not_breakdown _ _, ?_⟩
  exact cmEqOne_not_existence (fun _ => True) (fun _ => True) (fun _ => 0) trivial (fun _ _ => 0) trivial

/-- **¬A does NOT entail C** (as composed — see the header's
CT-3 fence): the `ν ≠ 1` assignment makes ¬(A-shape) true and
(C-shape) false. The step needs the ambient-ν reading AND the
admissibility inclusion; as a bare shape entailment it fails. -/
theorem nsNotA_not_entails_C :
    ∃ (Sol : ℝ → NSInitialField → NSForcingField → Prop)
      (Init : NSInitialField → Prop) (Force Zero : NSForcingField → Prop),
      ¬ nsAShape Sol Init Zero ∧ ¬ nsCShape Sol Init Force := by
  refine ⟨fun ν _ _ => ν ≠ 1, fun _ => True, fun _ => True, fun _ => True,
    ?_, cmNeOne_not_breakdown _ _⟩
  exact cmNeOne_not_existence (fun _ => True) (fun _ => True) (fun _ => 0) trivial (fun _ _ => 0) trivial

/-- **¬D does NOT entail B** (torus mirror of the headline
step): the `ν = 1` assignment. -/
theorem nsNotD_not_entails_B :
    ∃ (Sol : ℝ → NSInitialField → NSForcingField → Prop)
      (Init : NSInitialField → Prop) (Force Zero : NSForcingField → Prop),
      ¬ nsCShape Sol Init Force ∧ ¬ nsAShape Sol Init Zero := by
  refine ⟨fun ν _ _ => ν = 1, fun _ => True, fun _ => True, fun _ => True,
    cmEqOne_not_breakdown _ _, ?_⟩
  exact cmEqOne_not_existence (fun _ => True) (fun _ => True) (fun _ => 0) trivial (fun _ _ => 0) trivial

/-- **¬B does NOT entail D** (torus mirror): the `ν ≠ 1`
assignment. -/
theorem nsNotB_not_entails_D :
    ∃ (Sol : ℝ → NSInitialField → NSForcingField → Prop)
      (Init : NSInitialField → Prop) (Force Zero : NSForcingField → Prop),
      ¬ nsAShape Sol Init Zero ∧ ¬ nsCShape Sol Init Force := by
  refine ⟨fun ν _ _ => ν ≠ 1, fun _ => True, fun _ => True, fun _ => True,
    ?_, cmNeOne_not_breakdown _ _⟩
  exact cmNeOne_not_existence (fun _ => True) (fun _ => True) (fun _ => 0) trivial (fun _ _ => 0) trivial

/-- **¬C does NOT entail B** (cross-domain): the `ν = 1`
assignment blocks it on ν already; domain blocks it at every
regime (CT-0's table). -/
theorem nsNotC_not_entails_B :
    ∃ (Sol : ℝ → NSInitialField → NSForcingField → Prop)
      (InitR : NSInitialField → Prop) (ForceR : NSForcingField → Prop)
      (InitT : NSInitialField → Prop) (ZeroT : NSForcingField → Prop),
      ¬ nsCShape Sol InitR ForceR ∧ ¬ nsAShape Sol InitT ZeroT := by
  refine ⟨fun ν _ _ => ν = 1, fun _ => True, fun _ => True, fun _ => True,
    fun _ => True, cmEqOne_not_breakdown _ _, ?_⟩
  exact cmEqOne_not_existence (fun _ => True) (fun _ => True) (fun _ => 0) trivial (fun _ _ => 0) trivial

/-- **¬D does NOT entail A** (cross-domain): the `ν = 1`
assignment. -/
theorem nsNotD_not_entails_A :
    ∃ (Sol : ℝ → NSInitialField → NSForcingField → Prop)
      (InitT : NSInitialField → Prop) (ForceT : NSForcingField → Prop)
      (InitR : NSInitialField → Prop) (ZeroR : NSForcingField → Prop),
      ¬ nsCShape Sol InitT ForceT ∧ ¬ nsAShape Sol InitR ZeroR := by
  refine ⟨fun ν _ _ => ν = 1, fun _ => True, fun _ => True, fun _ => True,
    fun _ => True, cmEqOne_not_breakdown _ _, ?_⟩
  exact cmEqOne_not_existence (fun _ => True) (fun _ => True) (fun _ => 0) trivial (fun _ _ => 0) trivial

/-- **¬A does NOT entail B** (cross-domain, existence to
existence): the `ν ≠ 1` assignment. -/
theorem nsNotA_not_entails_B :
    ∃ (Sol : ℝ → NSInitialField → NSForcingField → Prop)
      (InitR : NSInitialField → Prop) (ZeroR : NSForcingField → Prop)
      (InitT : NSInitialField → Prop) (ZeroT : NSForcingField → Prop),
      ¬ nsAShape Sol InitR ZeroR ∧ ¬ nsAShape Sol InitT ZeroT := by
  refine ⟨fun ν _ _ => ν ≠ 1, fun _ => True, fun _ => True, fun _ => True,
    fun _ => True, ?_, ?_⟩
  · exact cmNeOne_not_existence (fun _ => True) (fun _ => True) (fun _ => 0) trivial (fun _ _ => 0) trivial
  · exact cmNeOne_not_existence (fun _ => True) (fun _ => True) (fun _ => 0) trivial (fun _ _ => 0) trivial

/-- **¬B does NOT entail A** (cross-domain, existence to
existence): the `ν ≠ 1` assignment. -/
theorem nsNotB_not_entails_A :
    ∃ (Sol : ℝ → NSInitialField → NSForcingField → Prop)
      (InitT : NSInitialField → Prop) (ZeroT : NSForcingField → Prop)
      (InitR : NSInitialField → Prop) (ZeroR : NSForcingField → Prop),
      ¬ nsAShape Sol InitT ZeroT ∧ ¬ nsAShape Sol InitR ZeroR := by
  refine ⟨fun ν _ _ => ν ≠ 1, fun _ => True, fun _ => True, fun _ => True,
    fun _ => True, ?_, ?_⟩
  · exact cmNeOne_not_existence (fun _ => True) (fun _ => True) (fun _ => 0) trivial (fun _ _ => 0) trivial
  · exact cmNeOne_not_existence (fun _ => True) (fun _ => True) (fun _ => 0) trivial (fun _ _ => 0) trivial

/-- **¬A does NOT entail D** (cross-domain): the `ν ≠ 1`
assignment. -/
theorem nsNotA_not_entails_D :
    ∃ (Sol : ℝ → NSInitialField → NSForcingField → Prop)
      (InitR : NSInitialField → Prop) (ZeroR : NSForcingField → Prop)
      (InitT : NSInitialField → Prop) (ForceT : NSForcingField → Prop),
      ¬ nsAShape Sol InitR ZeroR ∧ ¬ nsCShape Sol InitT ForceT := by
  refine ⟨fun ν _ _ => ν ≠ 1, fun _ => True, fun _ => True, fun _ => True,
    fun _ => True, ?_, cmNeOne_not_breakdown _ _⟩
  exact cmNeOne_not_existence (fun _ => True) (fun _ => True) (fun _ => 0) trivial (fun _ _ => 0) trivial

/-- **¬B does NOT entail C** (cross-domain): the `ν ≠ 1`
assignment. -/
theorem nsNotB_not_entails_C :
    ∃ (Sol : ℝ → NSInitialField → NSForcingField → Prop)
      (InitT : NSInitialField → Prop) (ZeroT : NSForcingField → Prop)
      (InitR : NSInitialField → Prop) (ForceR : NSForcingField → Prop),
      ¬ nsAShape Sol InitT ZeroT ∧ ¬ nsCShape Sol InitR ForceR := by
  refine ⟨fun ν _ _ => ν ≠ 1, fun _ => True, fun _ => True, fun _ => True,
    fun _ => True, ?_, cmNeOne_not_breakdown _ _⟩
  exact cmNeOne_not_existence (fun _ => True) (fun _ => True) (fun _ => 0) trivial (fun _ _ => 0) trivial

/-- **¬C does NOT entail D** (cross-domain, breakdown to
breakdown): the `ν = 1` assignment. -/
theorem nsNotC_not_entails_D :
    ∃ (Sol : ℝ → NSInitialField → NSForcingField → Prop)
      (InitR : NSInitialField → Prop) (ForceR : NSForcingField → Prop)
      (InitT : NSInitialField → Prop) (ForceT : NSForcingField → Prop),
      ¬ nsCShape Sol InitR ForceR ∧ ¬ nsCShape Sol InitT ForceT :=
  ⟨fun ν _ _ => ν = 1, fun _ => True, fun _ => True, fun _ => True,
    fun _ => True, cmEqOne_not_breakdown _ _, cmEqOne_not_breakdown _ _⟩

/-- **¬D does NOT entail C** (cross-domain, breakdown to
breakdown): the `ν = 1` assignment. -/
theorem nsNotD_not_entails_C :
    ∃ (Sol : ℝ → NSInitialField → NSForcingField → Prop)
      (InitT : NSInitialField → Prop) (ForceT : NSForcingField → Prop)
      (InitR : NSInitialField → Prop) (ForceR : NSForcingField → Prop),
      ¬ nsCShape Sol InitT ForceT ∧ ¬ nsCShape Sol InitR ForceR :=
  ⟨fun ν _ _ => ν = 1, fun _ => True, fun _ => True, fun _ => True,
    fun _ => True, cmEqOne_not_breakdown _ _, cmEqOne_not_breakdown _ _⟩

/-! ## The fixed-ν shapes: what is NOT blocked, stated exactly

At a single shared viscosity (Fefferman's ambient reading) the
same-domain steps are exactly as strong as the admissibility
inclusion `∀ f, Zero f → Force f`: with it, both directions are
pure logic; without it, both fail (one countermodel serves
both: solutions exist exactly on the admissible class, and the
zero forcing is not in it). -/

/-- **The existence shape at one fixed viscosity** (the
ambient-ν reading of (A)/(B)): at this `ν`, every admissible
datum with zero forcing has a solution. -/
def nsAShapeAt (Sol : ℝ → ι → φ → Prop) (Init : ι → Prop)
    (Zero : φ → Prop) (ν : ℝ) : Prop :=
  ∀ u0, Init u0 → ∀ f, Zero f → Sol ν u0 f

/-- **The breakdown shape at one fixed viscosity** (the
ambient-ν reading of (C)/(D)): at this `ν`, some admissible
datum has no solution. -/
def nsCShapeAt (Sol : ℝ → ι → φ → Prop) (Init : ι → Prop)
    (Force : φ → Prop) (ν : ℝ) : Prop :=
  ∃ u0 f, Init u0 ∧ Force f ∧ ¬ Sol ν u0 f

/-- **Fixed ν, ¬C → A, WITH the inclusion (T1):** at a single
shared viscosity, if the zero forcing is admissible, then
¬(breakdown at `ν`) gives existence at `ν` — pure logic: a
datum with no solution would be a breakdown witness, and the
inclusion is exactly what lets the zero-forcing datum serve
as one. -/
theorem nsFixedNu_notC_imp_A (Sol : ℝ → ι → φ → Prop)
    (Init : ι → Prop) (Force Zero : φ → Prop)
    (hIncl : ∀ f, Zero f → Force f) (ν : ℝ) :
    ¬ nsCShapeAt Sol Init Force ν → nsAShapeAt Sol Init Zero ν := by
  intro hNC u0 hu f hf
  by_contra hcon
  exact hNC ⟨u0, f, hu, hIncl f hf, hcon⟩

/-- **Fixed ν, ¬A → C, WITH the inclusion (T1):** at a single
shared viscosity, if the zero forcing is admissible, then
¬(existence at `ν`) gives breakdown at `ν` — pure logic: the
¬A witness (admissible datum, zero forcing, no solution) is a
breakdown witness once the inclusion admits its forcing.
**Shape theorem only** — about `nsAShapeAt`/`nsCShapeAt`, NOT
about the pin's `NSAlternativeA`/`NSAlternativeC`; the CT-3
reading fence of CT-0 stands. -/
theorem nsFixedNu_notA_imp_C (Sol : ℝ → ι → φ → Prop)
    (Init : ι → Prop) (Force Zero : φ → Prop)
    (hIncl : ∀ f, Zero f → Force f) (ν : ℝ) :
    ¬ nsAShapeAt Sol Init Zero ν → nsCShapeAt Sol Init Force ν := by
  intro hNA
  by_contra hcon
  apply hNA
  intro u0 hu f hf
  by_contra hsol
  exact hcon ⟨u0, f, hu, hIncl f hf, hsol⟩

/-- **Fixed ν, ¬C does NOT entail A without the inclusion
(T1):** one countermodel for both directions — forcings are
`Bool`, the admissible class is `{false}`, the zero forcing is
`true` (NOT admissible), and solutions exist exactly on the
admissible class. Then at any `ν`: no admissible datum fails
(¬C holds), yet the zero-forcing datum has no solution (A
fails). The inclusion is load-bearing, not decorative. -/
theorem nsFixedNu_notC_not_entails_A_without_inclusion :
    ∃ (Sol : ℝ → Unit → Bool → Prop) (Init : Unit → Prop)
      (Force Zero : Bool → Prop) (ν : ℝ),
      ¬ nsCShapeAt Sol Init Force ν ∧ ¬ nsAShapeAt Sol Init Zero ν := by
  refine ⟨fun _ _ f => f = false, fun _ => True, fun f => f = false,
    fun f => f = true, 1, ?_, ?_⟩
  · intro hC
    obtain ⟨u0, f, -, hf, hnsol⟩ := hC
    exact hnsol hf
  · intro hA
    have h := hA () trivial true rfl
    exact (by decide : ¬ ((true : Bool) = false)) h

/-- **Fixed ν, ¬A does NOT entail C without the inclusion
(T1):** the same countermodel read the other way — the
zero-forcing datum has no solution (¬A holds), yet no
admissible datum fails (C fails), because the failing datum's
forcing is outside the admissible class. -/
theorem nsFixedNu_notA_not_entails_C_without_inclusion :
    ∃ (Sol : ℝ → Unit → Bool → Prop) (Init : Unit → Prop)
      (Force Zero : Bool → Prop) (ν : ℝ),
      ¬ nsAShapeAt Sol Init Zero ν ∧ ¬ nsCShapeAt Sol Init Force ν := by
  refine ⟨fun _ _ f => f = false, fun _ => True, fun f => f = false,
    fun f => f = true, 1, ?_, ?_⟩
  · intro hA
    have h := hA () trivial true rfl
    exact (by decide : ¬ ((true : Bool) = false)) h
  · intro hC
    obtain ⟨u0, f, -, hf, hnsol⟩ := hC
    exact hnsol hf

/-! ## Q3 exhibits: the frozen table, evaluated

The step-status table of CT-0, evaluated at the headline steps —
the tester's Q3 answers, as theorems. -/

/-- **Q3 exhibit:** at the pin's regime the ¬C → A step's
status is `blockedByNuQuantification` — justified by
`nsNotC_not_entails_A` above. -/
theorem nsStepStatus_notC_to_A_pin :
    nsStepStatus .quantifiedInside ⟨.C, .A⟩
      = .blockedByNuQuantification := rfl

/-- **Q3 exhibit:** at the pin's regime the ¬A → C step is
likewise blocked by the ν-quantification — justified by
`nsNotA_not_entails_C`; the CT-3 reading is not a step the
pinned statement licenses. -/
theorem nsStepStatus_notA_to_C_pin :
    nsStepStatus .quantifiedInside ⟨.A, .C⟩
      = .blockedByNuQuantification := rfl

/-- **Q3 exhibit:** at the fixed-global regime the ¬C → A step's
status is `needsAdmissibilityAtFixedNu` — justified by
`nsFixedNu_notC_imp_A` and
`nsFixedNu_notC_not_entails_A_without_inclusion`. -/
theorem nsStepStatus_notC_to_A_fixed :
    nsStepStatus .fixedGlobal ⟨.C, .A⟩
      = .needsAdmissibilityAtFixedNu := rfl

/-- **Q3 exhibit:** a cross-domain step (¬C → B) is
`blockedByDomain` at the pin's regime — and at every regime,
by the definition of the table. -/
theorem nsStepStatus_crossDomain :
    nsStepStatus .quantifiedInside ⟨.C, .B⟩ = .blockedByDomain := rfl

/-- **Q3 exhibit:** a route through ¬C → A is flagged by the
headline Q3 function. -/
theorem nsRoute_notCtoA_flagged :
    nsRouteUsesNotCtoA (.viaNeg ⟨.C, .A⟩ .direct) = true := rfl

/-- **Q3 exhibit:** a route through ¬A → C is flagged by the
general blocked-step function. -/
theorem nsRoute_blockedStep_flagged :
    nsRouteUsesBlockedStep (.viaNeg ⟨.A, .C⟩ .direct) = true := rfl

/-- **Q3 exhibit:** the direct route uses no blocked step. -/
theorem nsRoute_direct_clean :
    nsRouteUsesBlockedStep .direct = false := rfl

end Shape

end ThetLogos
