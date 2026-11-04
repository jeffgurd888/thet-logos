import Mathlib.Tactic
import ThetLogos.ModularVariance
import ThetLogos.ThermalProfileSeparation
import ThetLogos.PoissonTotalMassBlindness

/-!
# ThetLogos.ThermalSourceComposite — SR-5: the thermal-source composite (T1)

HONESTY LEDGER (read before citing):

- **Working label only.** SR-5 and this module name are working
  labels from the shadow scoping dossier
  (`~/workspace/your_files/dial2-shadow-scoping-2026-11-04.md`,
  §2/SR-5); Jeff names.
- **What this is.** Pure bookkeeping, assembly-grade: the
  composite chain the corpus can actually build today —
  *thermal state → source → potential* — with every arrow a
  landed theorem. A Gibbs state's site-energy density
  (`ModularVariance.gibbsProb` weighted by the site energies)
  is read as a source function on the `BridgeLaplacian` seat
  and fed through T2's Poisson channel in the canonical form
  SHADOW-TEST-1 packaged (`poissonPotential` / `poissonField` /
  `poissonFlow` of `PoissonTotalMassBlindness`). Nothing is
  built, generated, or set in motion: charges + a fixed
  operator + a thermal state's data determine a potential and
  its field. Determination, not self-organization; statics,
  not dynamics.
- **What it earns — exactly one shadow check.** **SH-5**: the
  source map is specified without any gravitational vocabulary
  anywhere — it is an energy-expectation density of a thermal
  state, built entirely from owned thermal data (§1). It earns
  SH-5 and **nothing downstream**: no SH-6 (nothing responds —
  the graph, the weights, and the operator are fixtures chosen
  before the source), no SH-8 (there is no test body and no
  universality statement is even formable at this seat), no
  SH-9 (no attraction sign is derived; none is stated).
- **The ceiling, on the face, as theorems (§4).** The composite
  is defined through the mean-subtraction projection — that is
  its well-definedness (§2: the composite potential solves
  `L φ = meanSub (thermalSource)`, and the projected source is
  always in T2's compatibility class). By SHADOW-TEST-1, the
  composite's field and flow therefore factor through the
  mean-subtracted source alone: two thermal states whose
  sources have the same mean-subtraction have the same
  composite field and flow; shifting the fed source by a
  constant (changing its total — the state's mean energy —
  at fixed contrast) changes nothing the channel returns; no
  quantity of the composite field data detects the source's
  total; and a constant thermal source returns the zero field.
  **Total-mass blindness is inherited, and the isolated-mass
  signature is unreachable by this composite.** This is
  CT-1 of the shadow scoping, applied at the composite's own
  source.
- **Pre-registered disposition (scoping §2/SR-5(f), honored).**
  This brick is **Dial-INELIGIBLE**: Dial 2 stays 0 under
  every outcome, including this landing. It seats no gravity
  object, defines no response law, and states no universality.
  **K-SR-5 is armed**: the word for the Dial-2 target attaches
  to the composite's output potential nowhere in this module
  except inside this ledger's NOT-CLAIMED fences; any draft
  that lets it attach fires K-GR-LAUNDER at full rank.
- **The T1 consumption, stated exactly.** The Gibbs state's
  weight is T1's profiled weight at a constant profile:
  `gibbsProb E β = profWeight (fun _ => β) E` pointwise
  (§1, `gibbsProb_eq_profWeight_const`), so the source is
  equally T1's constant-profile weight times the site energy.
  At a single finite seat this is the same data
  `ModularVariance` carries; T3's marginal machinery is the
  product-seat form of site data and is not consumed here —
  the inversion lives on the graph seat, and the composite
  is stated there.
- Everything here is T1 finite linear algebra / finite Gibbs
  statics, consuming landed modules at their landed shapes.
  Zero sorrys, no `native_decide`, headline axioms exactly
  the standard three (`propext`, `Classical.choice`,
  `Quot.sound`).
- SEP FENCES, STANDING. No operator acting on a thermal
  density matrix separates charge by its own action (SEP-0);
  no charge operator and no electromagnetic field object is
  claimed at this seat (K-SEP-3, K-PUMP-5). The source is a
  real-valued function on vertices (data); the potential a
  real-valued function (determined data). Finite statics
  only. **NO CLAIM; dials 0/4. Dial 2 = 0.**
-/

namespace ThetLogos

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-! ## §1. The source: a Gibbs state's site-energy density

The source map (SH-5): from a thermal state's own data — its
energies `E` and inverse temperature `β`, both entered as
data — to a source function on the seat. No vocabulary from
outside the thermal line appears in its construction. -/

/-- **The thermal source of a Gibbs state**: the state's
site-energy density — at each site, the Gibbs probability of
the site times the site's energy,
`thermalSource E β i = gibbsProb E β i * E i`. A function of
owned thermal data only (the state of `ModularVariance` at
energies `E`, inverse temperature `β`). -/
noncomputable def thermalSource (E : V → ℝ) (β : ℝ) : V → ℝ :=
  fun i => ModularVariance.gibbsProb E β i * E i

omit [DecidableEq V] [Nonempty V] in
theorem thermalSource_apply (E : V → ℝ) (β : ℝ) (i : V) :
    thermalSource E β i
      = ModularVariance.gibbsProb E β i * E i := rfl

omit [DecidableEq V] [Nonempty V] in
/-- **The Gibbs state is T1's constant-profile weight.** The
probability `ModularVariance` assigns to site `i` is exactly
the profiled weight `ThermalProfileSeparation` assigns at the
constant profile `fun _ => β`: the two landed Gibbs dialects
agree on the nose, so the source below is equally the
constant-profile weight times the site energy. -/
theorem gibbsProb_eq_profWeight_const (E : V → ℝ) (β : ℝ)
    (i : V) :
    ModularVariance.gibbsProb E β i
      = profWeight (fun _ => β) E i := rfl

omit [DecidableEq V] [Nonempty V] in
/-- The thermal source in T1's dialect: the constant-profile
weight times the site energy. -/
theorem thermalSource_eq_profWeight_mul (E : V → ℝ) (β : ℝ)
    (i : V) :
    thermalSource E β i
      = profWeight (fun _ => β) E i * E i := by
  rw [thermalSource_apply, gibbsProb_eq_profWeight_const]

omit [DecidableEq V] [Nonempty V] in
/-- **The source's total is the state's mean energy.** Summing
the site-energy density over the seat returns exactly
`ModularVariance.meanEnergy E β` — the bookkeeping identity
that says what the source's "total mass" analogue is at this
seat: a thermal expectation, nothing else. (What the Poisson
channel does with that total is §4's subject.) -/
theorem sum_thermalSource (E : V → ℝ) (β : ℝ) :
    ∑ i, thermalSource E β i = ModularVariance.meanEnergy E β :=
  rfl

omit [DecidableEq V] [Nonempty V] in
/-- The mean of the thermal source is the state's mean energy
spread over the seat: `meanVal (thermalSource E β) =
meanEnergy E β / card V`. This mean is exactly what the
mean-subtraction projection removes before T2 ever sees the
source (§2, §4). -/
theorem meanVal_thermalSource (E : V → ℝ) (β : ℝ) :
    meanVal (thermalSource E β)
      = ModularVariance.meanEnergy E β / (Fintype.card V : ℝ) := by
  show (∑ i, thermalSource E β i) / (Fintype.card V : ℝ) = _
  rw [sum_thermalSource]

/-! ## §2. The composite: source → potential, field, flow

The composite is T2's canonical channel (SHADOW-TEST-1's
packaging) evaluated at the thermal source. Its
well-definedness is stated honestly: the composite is
defined **through the mean-subtraction projection** — the
canonical potential solves Poisson's equation for the
projected source, and the projection always lands in T2's
compatibility class. -/

/-- **The composite potential**: T2's canonical potential for
the thermal source — i.e. a potential for its
mean-subtraction, chosen by T2 existence. The choice is
immaterial: §3 shows every potential for the projected
source has this one's field and flow, and differs from it
by at most a constant. -/
noncomputable def thermalPotential (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (E : V → ℝ) (β : ℝ) :
    V → ℝ :=
  poissonPotential w hw hw0 hpos (thermalSource E β)

/-- **The composite field**: the edge drop of the composite
potential — T2's canonical field of the thermal source,
well-defined on the nose by T2 uniqueness. -/
noncomputable def thermalField (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (E : V → ℝ) (β : ℝ) :
    V → V → ℝ :=
  poissonField w hw hw0 hpos (thermalSource E β)

/-- **The composite Ohm flow**: the current field of the
composite potential — T2's canonical flow of the thermal
source. -/
noncomputable def thermalFlow (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (E : V → ℝ) (β : ℝ) :
    V → V → ℝ :=
  poissonFlow w hw hw0 hpos (thermalSource E β)

omit [DecidableEq V] [Nonempty V] in
/-- **Compatibility of the fed source.** The projected
thermal source always has total zero — it is always a
legitimate T2 input. The composite never feeds T2 anything
else: this is the whole of its well-definedness, and it is
bought by the projection, not by any property of the
thermal source (whose own total is the mean energy, §1,
generically nonzero). -/
theorem sum_meanSub_thermalSource (E : V → ℝ) (β : ℝ) :
    ∑ i, meanSub (thermalSource E β) i = 0 :=
  sum_meanSub_eq_zero _

omit [Nonempty V] in
/-- **The composite solves the projected problem.** The
composite potential is a potential for the mean-subtracted
thermal source: `L (thermalPotential) = meanSub
(thermalSource)`. Stated in this form — not in the bare
form `L φ = thermalSource`, which is false whenever the
mean energy is nonzero (K-TCS-POIS's obstruction, inherited
honestly). -/
theorem laplacianOp_thermalPotential (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (E : V → ℝ) (β : ℝ) :
    laplacianOp w (thermalPotential w hw hw0 hpos E β)
      = meanSub (thermalSource E β) :=
  laplacianOp_poissonPotential w hw hw0 hpos (thermalSource E β)

/-! ## §3. Uniqueness, inherited from T2

Everything in this section is T2's uniqueness read at the
composite's source: the potential is unique up to an
additive constant, and its field and flow are unique on the
nose — any potential for the projected thermal source,
however produced, returns the composite's field and flow. -/

omit [Nonempty V] in
/-- **The field of the composite potential is the composite
field** — the definitional hinge between §2's two
packagings (`poissonField` is `dropVec` of
`poissonPotential`). -/
theorem dropVec_thermalPotential (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (E : V → ℝ) (β : ℝ) :
    dropVec (thermalPotential w hw hw0 hpos E β)
      = thermalField w hw hw0 hpos E β := rfl

omit [Nonempty V] in
/-- **The flow of the composite potential is the composite
flow** — the same hinge for `flowVec` / `poissonFlow`. -/
theorem flowVec_thermalPotential (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (E : V → ℝ) (β : ℝ) :
    flowVec w (thermalPotential w hw hw0 hpos E β)
      = thermalFlow w hw hw0 hpos E β := rfl

omit [Nonempty V] in
/-- **Uniqueness modulo constants, inherited.** Any
potential for the projected thermal source differs from
the composite potential by an additive constant — T2's
`exists_add_const_of_laplacianOp_eq` at the composite's
equation. -/
theorem thermalPotential_unique_mod_const (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (E : V → ℝ) (β : ℝ)
    (f : V → ℝ)
    (hf : laplacianOp w f = meanSub (thermalSource E β)) :
    ∃ c : ℝ, ∀ i, thermalPotential w hw hw0 hpos E β i
      = f i + c :=
  exists_add_const_of_laplacianOp_eq w hw hw0 hpos f
    (thermalPotential w hw hw0 hpos E β)
    (by rw [hf, laplacianOp_thermalPotential])

omit [Nonempty V] in
/-- **Every potential for the projected source has the
composite field.** The field is a property of the source,
not of the chosen potential: the additive constant cancels
in every edge difference (T2). -/
theorem dropVec_eq_thermalField (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (E : V → ℝ) (β : ℝ)
    (f : V → ℝ)
    (hf : laplacianOp w f = meanSub (thermalSource E β)) :
    dropVec f = thermalField w hw hw0 hpos E β := by
  have h := dropVec_eq_of_laplacianOp_eq w hw hw0 hpos
    (thermalPotential w hw hw0 hpos E β) f
    ((laplacianOp_thermalPotential w hw hw0 hpos E β).trans
      hf.symm)
  rwa [dropVec_thermalPotential] at h

omit [Nonempty V] in
/-- **Every potential for the projected source drives the
composite flow.** The Ohm current is likewise a property
of the source alone (T2). -/
theorem flowVec_eq_thermalFlow (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (E : V → ℝ) (β : ℝ)
    (f : V → ℝ)
    (hf : laplacianOp w f = meanSub (thermalSource E β)) :
    flowVec w f = thermalFlow w hw hw0 hpos E β := by
  have h := flowVec_eq_of_laplacianOp_eq w hw hw0 hpos
    (thermalPotential w hw hw0 hpos E β) f
    ((laplacianOp_thermalPotential w hw hw0 hpos E β).trans
      hf.symm)
  rwa [flowVec_thermalPotential] at h

/-! ## §4. The ceiling, inherited from SHADOW-TEST-1

The composite's output factors through the mean-subtracted
source — SHADOW-TEST-1's class theorem read at the thermal
source. Everything T2's channel returns for this composite
is a function of the source's contrast alone; the source's
total (the state's mean energy, §1) is exactly what the
channel cannot see. These are fence theorems about the
composite, stated as theorems — the ceiling is on the
module's face, in kernel-checked form. -/

omit [Nonempty V] in
/-- **The composite field factors through the projection.**
Two thermal states — any energies, any inverse
temperatures — whose sources have the same mean-subtraction
have the same composite field. The field is a function of
`meanSub (thermalSource)`, not of the state. -/
theorem thermalField_eq_of_meanSub_eq (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (E E' : V → ℝ)
    (β β' : ℝ)
    (h : meanSub (thermalSource E β)
      = meanSub (thermalSource E' β')) :
    thermalField w hw hw0 hpos E β
      = thermalField w hw hw0 hpos E' β' :=
  poissonField_eq_of_meanSub_eq w hw hw0 hpos _ _ h

omit [Nonempty V] in
/-- **The composite flow factors through the projection.**
The same factorization for the Ohm flow. -/
theorem thermalFlow_eq_of_meanSub_eq (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (E E' : V → ℝ)
    (β β' : ℝ)
    (h : meanSub (thermalSource E β)
      = meanSub (thermalSource E' β')) :
    thermalFlow w hw hw0 hpos E β
      = thermalFlow w hw hw0 hpos E' β' :=
  poissonFlow_eq_of_meanSub_eq w hw hw0 hpos _ _ h

omit [Nonempty V] in
/-- **The fed channel is shift-blind at the composite's own
source.** Even if the source handed to T2's channel were
the thermal source shifted by a constant — its total
changed, its contrast fixed — the channel would return
exactly the composite field. The composite's field is what
the shifted source would give; there is no version of this
composite that responds to the total. -/
theorem thermalField_shifted_source (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (E : V → ℝ) (β : ℝ)
    (c : ℝ) :
    poissonField w hw hw0 hpos
        (fun i => thermalSource E β i + c)
      = thermalField w hw hw0 hpos E β :=
  poissonField_add_const w hw hw0 hpos (thermalSource E β) c

omit [Nonempty V] in
/-- **The decision, at the composite's source.** No quantity
of the composite field data, and no nonzero constant shift
of the fed source, exhibits a response to the shift:
detecting the source's total through this composite is
impossible. SHADOW-TEST-1's
`not_exists_fieldFactor_detects_totalMass`, inherited —
the isolated-mass signature is unreachable by this
composite. Pre-registered Dial-ineligible: Dial 2 = 0. -/
theorem not_exists_thermalField_detects_sourceTotal
    (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (E : V → ℝ) (β : ℝ) :
    ¬ ∃ (F : (V → V → ℝ) → ℝ) (c : ℝ), c ≠ 0 ∧
      F (poissonField w hw hw0 hpos
          (fun i => thermalSource E β i + c))
        ≠ F (thermalField w hw hw0 hpos E β) := by
  rintro ⟨F, c, hc, hne⟩
  exact not_exists_fieldFactor_detects_totalMass w hw hw0
    hpos ⟨F, thermalSource E β, c, hc, hne⟩

/-- **A constant thermal source returns no field.** If the
state's site-energy density is constant across the seat —
pure total, zero contrast — the composite field is
identically zero. The strongest single form of the
ceiling: the part of the source that is a total with no
contrast produces nothing at all. -/
theorem thermalField_eq_zero_of_thermalSource_const
    (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (E : V → ℝ) (β : ℝ)
    (c : ℝ) (hc : ∀ i, thermalSource E β i = c) :
    thermalField w hw hw0 hpos E β = 0 := by
  have hsrc : thermalSource E β = fun _ => c := funext hc
  have hdef : thermalField w hw hw0 hpos E β
      = poissonField w hw hw0 hpos (thermalSource E β) :=
    rfl
  rw [hdef, hsrc]
  exact poissonField_const w hw hw0 hpos c

end ThetLogos
