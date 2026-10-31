import ThetLogos.SpectralActionA2
import ThetLogos.InnerFluctuations
import ThetLogos.MaxwellQuadPost

namespace ThetLogos

/-!
# ThetLogos.GravityPosePost - GR-POSE-0: the gravity pose registration pin

**Working label only.** The module name `GravityPosePost` and the
line name GR-POSE are working labels; Jeff names. Nothing in this
module is a name Jeff has given.

**Status: REGISTRATION ONLY - definitions, pose statements as
def-Props, two named-absence registration structures, and
pin-grade read-backs of landed theorems. NO CLAIM. No gravity
object is defined, constructed, or asserted to exist. Dials 0/4.**

Governing memo: `routeb-general-scratch/scoping-gravity-pose-2026-10-31.md`
(the section-0 fences, the section-1 vocabulary census, the
section-2 pose inventory and grades, the section-5 pin spec, the
section-6 kills). The grades and ceilings in that memo are PINNED:
this pin registers them; it does not re-grade, soften, or raise
any of them.

## Section-0 fence (verbatim-grade, on the face)

The strongest landing this line could ever produce is a proved
statement about which gravity questions the corpus can and cannot
pose - a map of the chair's seat-shape - and it seats NO gravity
object, moves Dial 2 not at all, and brings the continuum no
closer. Dial 2 = 0 under EVERY outcome of this line, including
total success.

Ceiling fence for fenced vocabulary: the words metric, geodesic,
curvature, Einstein, stress-energy, propagation, spacetime, and
the expression 1/r are FRONTIER vocabulary in this line, owned
by nothing in the corpus. In this module each of them appears
only inside this fence, inside a named-absence registration
below, or inside the frozen-pair registration of `PoseKillGravC`
(the one place the governing memo's own wording for that
predicate is quoted). Any other use is a fence breach.

## Pre-registered kills, named on the face (memo section 6)

- K-GR-VAC (vacuity): a registered pose that is satisfiable by
  construction - true because the house defined it true - is
  struck at full rank, not quietly weakened. Watch item in this
  pin: `PoseObjU`, registered only with its vacuity grade
  adjacent to it, as a definitional remark, never as evidence.
- K-GR-SMUG (type-smuggling): fenced vocabulary imported
  unowned - a would-be spatial separation that is secretly the
  state-space Connes distance material, the abstract `scalarR`
  re-narrated as a computed quantity, or a static finite form
  re-narrated as the missing object of `PoseObjB` - is dead on
  sight at full rank.
- K-GR-LAUNDER (ceiling-laundering): any statement, in a
  dossier, a draft post, or this module, that raises a pose's
  ceiling above the grade registered here - the pin sold as
  progress toward an object, the decision sold as understanding,
  the response law sold as a seed - is a correction at full
  rank, same volume.
- K-GR-STAB (undisclosed instability): a pose or response law
  whose answer flips at a parameter boundary the brick did not
  disclose. A boundary flip found later is reported as the
  finding, never repaired by silently narrowing a statement.
  Watch item in this pin: the fluctuation path of `PoseVarA`,
  whose boundary behavior is disclosed in its registration.
- K-GR-BUY (buy inflation): this line's output described,
  anywhere, as seating, nearly seating, or warming the chair.
  The section-0 sentence above is the whole buy, forever.

## What is registered here

1. `PoseCoef` - pose P-coef, grade CLOSED / discharged.
2. `PoseVarR` - pose P-var-R, grade CLOSED / discharged,
   inventoried beside P-coef as the second discharged pose.
3. `PoseObjU` - pose P-obj-U, grade STATABLE /
   VACUITY-ADJACENT, a definitional remark only.
4. `PoseObjF` - a NAMED ABSENCE registration (pose P-obj-F,
   grade unstatable today), as a registration structure with
   labeled opaque fields; no pose statement is supplied.
5. `PoseObjB` - a NAMED ABSENCE registration (pose P-obj-B,
   grade unstatable today), likewise.
6. `PoseVarAPathData`, `poseVarAPath`, `PoseVarA` - pose
   P-var-A, grade SURVIVES-reduced (the finite shadow of the
   variational pose), with its one-parameter fluctuation path
   frozen in parameterized form - see the path registration
   for the decision and its reason.
7. `PoseKillClassC`, `PoseKillGravC`, `PoseKill` - pose
   P-kill, the decision pose, with its (C, GRAV_C) pair frozen
   verbatim in substance as named pin components, so the
   follow-on decision brick GR-POSE-1 builds against exactly
   these. `PoseKill` is registered, NOT proved or asserted
   here.

The only proved content is pin-grade read-backs: restatements
and projections of theorems already landed in
`SpectralActionA2` and `InnerFluctuations`, each cited at its
read-back. No pose beyond the two discharged ones is asserted
to hold.
-/

/-! ## P-var-R and P-coef: the two discharged poses -/

/-- **Pose P-var-R - grade CLOSED / discharged.**
The R-response pose, inventoried beside P-coef as the second
discharged pose (governing memo section 2): in the stated
Gilkey form of `SpectralActionA2`, `gilkeyA2` responds to its
R-slot argument affinely, with constant slope `a2GravCoeff`
and no other R-dependence. The affine law IS the R-response,
by citation of the landed `seely_dewitt_a2_affine`
(SA-FLIP-1). CEILING, on the face: a response law in a
variable nothing in the corpus computes - if an R ever
arrived, the action's answer is already law-shaped; no R is
owned, supplied, or asserted here. Stability verdict, split
and disclosed by the source module: the slope's nonvanishing
is convention-robust, its value is convention-carrying
(it is the coefficient of the stated form). -/
def PoseVarR : Prop :=
  ∀ (R : ℂ) (X : Matrix I32 I32 ℂ),
    gilkeyA2 R X
      = a2GravCoeff * R
        + ((4 * (Real.pi : ℂ)) ^ 2)⁻¹ * (4 * Matrix.trace X)

/-- **P-var-R discharged, as a read-back.** This is the landed
`seely_dewitt_a2_affine` restated in the pin's name; nothing
new is proved. -/
theorem poseVarR_discharged : PoseVarR :=
  seely_dewitt_a2_affine

/-- **Pose P-coef - grade CLOSED / discharged.**
SA-FLIP-1's own pose (governing memo section 2): the spectral
action's a2, in its stated Gilkey form, separates into an
R-slot and a matter slot, and the R-slot coefficient
`a2GravCoeff` is nonzero. Formally: the affine law
`PoseVarR` holds and `a2GravCoeff ≠ 0`. CEILING, on the face:
a coefficient inside a chosen standard form over an abstract
scalar that nothing in the corpus computes. The pose is
well-formed because it quantifies over a form the house
stated, not over anything else; reading it as an existence
statement about gravity is exactly the ill-posed reading the
memo fences. Stability split, on the face: the coefficient's
nonvanishing is robust, its value is conventional
(form-dependent). -/
def PoseCoef : Prop :=
  PoseVarR ∧ a2GravCoeff ≠ 0

/-- **P-coef discharged, as a read-back.** The two landed
pieces, cited and not re-proved: `seely_dewitt_a2_affine`
(via `poseVarR_discharged`) and `a2_grav_coeff_ne_zero`. -/
theorem poseCoef_discharged : PoseCoef :=
  ⟨poseVarR_discharged, a2_grav_coeff_ne_zero⟩

/-- **Read-back.** P-coef projects to P-var-R: the two
discharged poses share the one landed affine law, and this
pin keeps them as two registered entries over it. -/
theorem poseCoef_varR_readback (h : PoseCoef) : PoseVarR :=
  h.1

/-! ## P-obj-U: the vacuity-adjacent pose, as a definitional remark -/

/-- **Pose P-obj-U - grade STATABLE / VACUITY-ADJACENT.**
The finite proxy for universal coupling that the census
found formally statable (governing memo section 2): for any
two finite matter squares `X` and `Y` and any R-slot value
`R`, the separated a2 at `X` and at `Y` carries one and the
same R-slot coefficient, the constant `a2GravCoeff`.
GRADE, ADJACENT ON THE FACE (K-GR-VAC watch): this pose is
true BY CONSTRUCTION of the chosen Gilkey form -
`a2GravCoeff` is one constant, defined once in
`SpectralActionA2`, taking no sector argument, so its
sector-independence was put in by hand when the form was
stated. This registration is a DEFINITIONAL REMARK ONLY. It
is not evidence for any coupling claim, it discharges no
part of the P-obj demand, and no later brick may cite it as
evidence; citing it as evidence fires K-GR-VAC and
K-GR-LAUNDER on the citing text. -/
def PoseObjU : Prop :=
  ∀ (X Y : Matrix I32 I32 ℂ) (R : ℂ),
    (gilkeyA2 R X
        = a2GravCoeff * R
          + ((4 * (Real.pi : ℂ)) ^ 2)⁻¹ * (4 * Matrix.trace X))
    ∧ (gilkeyA2 R Y
        = a2GravCoeff * R
          + ((4 * (Real.pi : ℂ)) ^ 2)⁻¹ * (4 * Matrix.trace Y))

/-- **Definitional read-back for P-obj-U - NOT evidence.**
Both conjuncts are the landed affine law
`seely_dewitt_a2_affine` applied twice; the sameness of the
coefficient is the sameness of the one defined constant.
This read-back exhibits the vacuity grade on the pose's
face: the pose's only model is the definitional one. It is
registered so the grade is checkable, and it must never be
reported as a result about coupling. -/
theorem poseObjU_definitional_readback : PoseObjU :=
  fun X Y R => ⟨seely_dewitt_a2_affine R X, seely_dewitt_a2_affine R Y⟩

/-! ## P-obj-F: a NAMED ABSENCE registration

The registration below is OF THE ABSENCE, in the repaired-pin
spirit: what is registered is that this pose cannot be stated
in current vocabulary, with the missing vocabulary named.
The structure is a registration record with labeled opaque
`Prop` fields; no inhabitant is supplied, no field is
asserted, and the structure is not a pose statement. -/

/-- **NAMED ABSENCE - pose P-obj-F, grade UNSTATABLE today.**
The field-law pose would need an owned spatial separation
`r` between masses, carrying a falloff law of 1/r^2 shape.
No such separation exists in the corpus (governing memo
sections 1-2). Named on the face as NOT spendable as `r`
(K-GR-SMUG): the Connes distance material of the corpus is
distance between STATES of the finite algebra, not a spatial
separation, and spending it in this seat is smuggling by
definition in this line. The two fields are the registration
of exactly that absence; both are labeled opaque - the pin
asserts no content for either. -/
structure PoseObjF where
  /-- Opaque (labeled): the missing owned spatial separation,
  a distance on an owned space that could carry the falloff
  law. Not supplied anywhere in the corpus. -/
  missingSeparation : Prop
  /-- Opaque (labeled): the fence field recording that the
  state-space Connes distance material is not the field
  above and may not be spent as it. -/
  connesDistanceNotThisField : Prop

/-! ## P-obj-B: a NAMED ABSENCE registration

Registered in the same form as `PoseObjF`: a registration of
an absence, with the missing vocabulary named and the
nearest owned neighbor named as a neighbor, not as the
missing object. -/

/-- **NAMED ABSENCE - pose P-obj-B, grade UNSTATABLE today.**
The bending pose would need a propagation object - a path,
frequency, or ray - that a candidate could bend or tax. No
such object exists in the corpus (governing memo sections
1-2). Named on the face as the nearest neighbor, NOT as a
propagation object: `maxwellOp` of `MaxwellQuadPost` is a
registered finite static quadratic form on link angles -
finite, static, registered rather than landed as a theorem
set, with no path, no frequency, and no ray. Any later
spectral-shift proxy over its registered spectrum is gated
on the MAX line landing on its own merits and would be a
NEW entry, not a follow-on of this pin. The two fields are
the registration of exactly that absence; both are labeled
opaque - the pin asserts no content for either. -/
structure PoseObjB where
  /-- Opaque (labeled): the missing object of the kind
  named in this registration's docstring. Not supplied
  anywhere in the corpus. -/
  missingObject : Prop
  /-- Opaque (labeled): the fence field recording that the
  nearest owned neighbor named in this registration's
  docstring is a static finite form, not the field above. -/
  nearestNeighborNotThisObject : Prop

/-- The nearest neighbor named in the `PoseObjB` absence
registration, cited as a definition so the name is
code-checked: `maxwellOp N`, the registered finite static
quadratic form's operator on link angles, from
`MaxwellQuadPost`. Registered here as a neighbor only; it
is not the missing object of `PoseObjB`, and nothing about
it is asserted in this pin. -/
noncomputable def poseObjBNearestNeighbor (N : ℕ) [NeZero N] :
    (LayerLink N → ℝ) →ₗ[ℝ] (LayerLink N → ℝ) :=
  maxwellOp N

/-! ## P-var-A: the surviving pose, reduced, and its frozen path

PATH DECISION, on the face: the path is registered as a
PARAMETERIZED pin field, not as a concrete path. Reason:
the landed vocabulary at the smDirac seat does not
determine a one-parameter fluctuation path uniquely. What
is landed (`InnerFluctuations`) is the fluctuation
construction `fluctuatedDirac D_F A = D_F + A + oppositeOneForm A`
for an algebraic one-form `A`, its order-one preservation
(`inner_fluctuation_preserves_order_one`, and the smDirac
instance `inner_fluctuation_preserves_order_one_smDirac`),
and self-adjointness preservation
(`fluctuatedDirac_self_adjoint`). No fixed self-adjoint
algebra element, and no fixed algebraic one-form, is named
at this seat by any landed module, so there is no landed
datum to scale. Choosing one here would invent vocabulary
to force uniqueness - K-GR-SMUG. The path is therefore
frozen as the parameterized family below: the data
(Yukawa parameters, one algebraic one-form, its
self-adjointness) ride as labeled fields of
`PoseVarAPathData`, the parameter is a real scalar `t`, and
the path at `t` is the landed `fluctuatedDirac` of the
`smDirac` seat operator by the scaled one-form `(t : ℂ) • A`.

BOUNDARY AND DEGENERACY DISCLOSURE (K-GR-STAB watch,
OP-1 lesson): at `t = 0` the path is the unfluctuated seat
operator (read back below); at `t = 1` it is the landed
fluctuated Dirac, where the landed order-one and
self-adjointness theorems apply directly (read back below).
For general `t` this pin asserts NOTHING about the scaled
one-form: no landed theorem states that the existential
form of `IsAlgebraicOneForm` is closed under scaling, so
order-one preservation at general `t` is not claimed here
and is GR-POSE-2's to settle, not this pin's to assume.
Degeneracy: if the supplied one-form is `0`, the path is
constant; if it is nonzero, the trace-of-square response
registered in `PoseVarA` may still have vanishing first or
second coefficient at special data, and any named-coefficient
extraction in a later brick must carry its own boundary
disclosure - a flip at such a boundary is a finding, not a
repair (K-GR-STAB). -/

/-- **The frozen path data for P-var-A - a parameterized pin
field, labeled as such.** The Yukawa parameters of the
smDirac seat, one algebraic one-form at that seat
(`oneForm_isAlgebraic`: `IsAlgebraicOneForm` in landed
vocabulary, consumed not discharged), and its
self-adjointness (`oneForm_selfAdjoint`, a labeled hypothesis
field). No element is chosen: supplying a member of this
structure is the later brick's act, and different members
give different paths - that non-uniqueness is the disclosed
reason the path is parameterized (registration header
above). -/
structure PoseVarAPathData where
  /-- Yukawa parameter of the smDirac seat. -/
  yNu : ℂ
  /-- Yukawa parameter of the smDirac seat. -/
  yE : ℂ
  /-- Yukawa parameter of the smDirac seat. -/
  yU : ℂ
  /-- Yukawa parameter of the smDirac seat. -/
  yD : ℂ
  /-- Yukawa parameter of the smDirac seat. -/
  yR : ℂ
  /-- The fixed one-form of the path, an owned matrix at
  the seat. No canonical choice is registered. -/
  oneForm : Matrix I32 I32 ℂ
  /-- Labeled field: the one-form is algebraic for the
  seat operator, in the landed sense of
  `IsAlgebraicOneForm`. -/
  oneForm_isAlgebraic :
    IsAlgebraicOneForm oneForm (smDirac yNu yE yU yD yR)
  /-- Labeled hypothesis field: the one-form is
  self-adjoint. -/
  oneForm_selfAdjoint : IsSelfAdjoint oneForm

/-- **The frozen one-parameter fluctuation path for
P-var-A**, in parameterized form: at parameter `t : ℝ`,
the `smDirac` seat operator fluctuated, by the landed
`fluctuatedDirac` construction, by the scaled one-form
`(t : ℂ) • P.oneForm`. This is a definition over landed
vocabulary only; the boundary disclosure of the section
header applies to every use of it. -/
noncomputable def poseVarAPath (P : PoseVarAPathData) (t : ℝ) :
    Matrix I32 I32 ℂ :=
  fluctuatedDirac (smDirac P.yNu P.yE P.yU P.yD P.yR)
    ((t : ℂ) • P.oneForm)

/-- **Boundary read-back at `t = 0`.** The path at parameter
`0` is the unfluctuated seat operator: the scaled one-form
vanishes, and a zero fluctuation is the identity operation
on the Dirac. Pin-grade only. -/
theorem poseVarAPath_zero (P : PoseVarAPathData) :
    poseVarAPath P 0
      = smDirac P.yNu P.yE P.yU P.yD P.yR := by
  simp [poseVarAPath, fluctuatedDirac, oppositeOneForm]

/-- **Read-back at `t = 1`.** The path at parameter `1` is
exactly the landed fluctuated Dirac of the seat operator by
the path's one-form - the seat at which the landed
preservation theorems below apply. Pin-grade only. -/
theorem poseVarAPath_one (P : PoseVarAPathData) :
    poseVarAPath P 1
      = fluctuatedDirac (smDirac P.yNu P.yE P.yU P.yD P.yR)
          P.oneForm := by
  simp [poseVarAPath]

/-- **Order-one at the landed seat of the path.** At
`t = 1`, the path's operator satisfies the order-one
condition, by the landed smDirac instance
`inner_fluctuation_preserves_order_one_smDirac` consumed
through the path data's algebraic-form field. Asserted at
`t = 1` only; the section header's disclosure governs
general `t`. -/
theorem poseVarAPath_one_orderOne (P : PoseVarAPathData) :
    OrderOneHolds (poseVarAPath P 1) := by
  rw [poseVarAPath_one]
  exact inner_fluctuation_preserves_order_one_smDirac
    P.yNu P.yE P.yU P.yD P.yR P.oneForm P.oneForm_isAlgebraic

/-- **Self-adjointness at the landed seat of the path.** At
`t = 1`, the path's operator is self-adjoint, by the landed
`fluctuatedDirac_self_adjoint` and `smDirac_self_adjoint`
consumed through the path data's self-adjointness field.
Asserted at `t = 1` only. -/
theorem poseVarAPath_one_selfAdjoint (P : PoseVarAPathData) :
    IsSelfAdjoint (poseVarAPath P 1) := by
  rw [poseVarAPath_one]
  exact fluctuatedDirac_self_adjoint _ _
    (smDirac_self_adjoint P.yNu P.yE P.yU P.yD P.yR)
    P.oneForm_selfAdjoint

/-- **Pose P-var-A - grade SURVIVES-reduced.**
The finite shadow of the variational pose (governing memo
section 2), stated along the frozen parameterized path:
the trace of the square of the fluctuated seat operator -
the a2 matter trace's own quantity - is a quadratic
polynomial in the path parameter, with coefficients
`c0, c1, c2`; `c1` is the would-be first-variation
coefficient. GR-POSE-2's registered task, gated on this
pin, is to EXHIBIT `c0, c1, c2` as named trace expressions
in the path data, not merely to assert existence; this pin
asserts that no member of this pose holds. CEILING, on
the face: a statement about how the finite action's numbers
move under finite fluctuation - a theorem about the finite
factor's own arithmetic if it ever lands. It is not an
object, it seats nothing, and Dial 2 is unmoved by it under
every outcome. The degeneracy and boundary disclosure of
the section header is part of this registration. -/
def PoseVarA (P : PoseVarAPathData) : Prop :=
  ∃ c0 c1 c2 : ℂ, ∀ t : ℝ,
    Matrix.trace ((poseVarAPath P t) ^ 2)
      = c0 + c1 * (t : ℂ) + c2 * (t : ℂ) ^ 2

/-! ## P-kill: the decision pose, with its (C, GRAV_C) pair frozen

The pair below is frozen verbatim in substance from the
governing memo section 2, as named pin components, so
GR-POSE-1 builds against exactly these definitions. The
formal shapes are the memo's own: the class is frozen by
its dependence property (a member may be built from
spectra, traces, and moments of owned Dirac operators -
the SA0 / SA2 / SA-FLIP-1 closure - and by that origin it
cannot take the R-slot as an input), and the predicate is
a dependence-and-response statement over that class. -/

/-- **The frozen class C for the decision (GR-POSE-1).**
A coefficient functional of the finite spectral data alone:
a function `F` of an R-slot value and a finite Dirac square
that factors through the finite data alone - there is a
`G` of the finite square with `F R X = G X` for every `R`
and `X`. The domain types are the owned ones of
`SpectralActionA2` (`R : ℂ`, `X : Matrix I32 I32 ℂ`); the
factorization is the class's frozen formal form, per the
section header. -/
def PoseKillClassC (F : ℂ → Matrix I32 I32 ℂ → ℂ) : Prop :=
  ∃ G : Matrix I32 I32 ℂ → ℂ,
    ∀ (R : ℂ) (X : Matrix I32 I32 ℂ), F R X = G X

/-- **Read-back for the frozen class C.** Membership in `C`
is exactly R-independence: a functional factors through
the finite data alone if and only if its value does not
change when only the R-slot value changes. Proven by
unfolding the frozen definition in both directions;
pin-grade only. -/
theorem poseKillClassC_iff (F : ℂ → Matrix I32 I32 ℂ → ℂ) :
    PoseKillClassC F
      ↔ ∀ (R₁ R₂ : ℂ) (X : Matrix I32 I32 ℂ),
          F R₁ X = F R₂ X := by
  constructor
  · rintro ⟨G, hG⟩ R₁ R₂ X
    rw [hG R₁ X, hG R₂ X]
  · intro h
    exact ⟨fun X => F 0 X, fun R X => h R 0 X⟩

/-- **The frozen predicate GRAV_C for the decision
(GR-POSE-1).** Frozen wording, quoted from the governing
memo under this section's ceiling fence: a functional of
the spectral data alone that separates a curvature
response. Frozen formal form: `F` lies in the class `C`
(`PoseKillClassC`) AND at some finite square `X` it
responds to the R-slot affinely with the landed slope -
for every `R`, `F R X = a2GravCoeff * R + F 0 X`, where
`a2GravCoeff` is the one landed nonzero coefficient.
Both conjuncts are part of the frozen predicate; dropping
either is a new entry, not a reading of this one. -/
def PoseKillGravC (F : ℂ → Matrix I32 I32 ℂ → ℂ) : Prop :=
  PoseKillClassC F ∧
    ∃ X : Matrix I32 I32 ℂ,
      ∀ R : ℂ, F R X = a2GravCoeff * R + F 0 X

/-- **Pose P-kill - the decision pose, grade SURVIVES.**
For the frozen pair (`PoseKillClassC`, `PoseKillGravC`):
no member of the class satisfies the predicate. In the
shape of the house's landed decision theorems, this is
the posed statement whose proof or kill is GR-POSE-1's
registered work, gated on this pin; a split verdict at
the class boundary, if that is what lands, is a landing
at PARTIAL grade with the boundary on its face (the
memo's pre-named seam), not a failure and not a silent
narrowing. CEILING, on the face: a theorem about this
corpus's own expressive limits for this named class -
that the R-half of the separated coefficient is imported
through the stated form, not derived from finite data.
It closes no physics, seats no object, and Dial 2 = 0
under every outcome. This pin registers the pose; it
does NOT assert that the pose holds. -/
def PoseKill : Prop :=
  ∀ F : ℂ → Matrix I32 I32 ℂ → ℂ,
    PoseKillClassC F → ¬ PoseKillGravC F

/-- **Read-back.** `PoseKill` is exactly its registered
statement, unfolded: for every functional, membership in
the frozen class excludes the frozen predicate. This is
the definition read back, not a proof of the pose -
`PoseKill` itself is not asserted anywhere in this
module. -/
theorem poseKill_unfold :
    PoseKill
      ↔ ∀ F : ℂ → Matrix I32 I32 ℂ → ℂ,
          PoseKillClassC F → ¬ PoseKillGravC F :=
  Iff.rfl

/-- **The R-response shape, as a read-back on the landed
object.** The one landed functional of this signature,
`gilkeyA2`, does separate an affine R-response at every
finite square: `gilkeyA2 R X = a2GravCoeff * R + gilkeyA2 0 X`,
by the landed affine law at `R` and at `0`. Registered
here only to fix what the response conjunct of
`PoseKillGravC` names; whether `gilkeyA2` or any other
functional lies in the frozen class is GR-POSE-1's
question, and nothing about it is asserted here. -/
theorem gilkeyA2_response_readback (R : ℂ)
    (X : Matrix I32 I32 ℂ) :
    gilkeyA2 R X = a2GravCoeff * R + gilkeyA2 0 X := by
  rw [seely_dewitt_a2_affine R X, seely_dewitt_a2_affine 0 X]
  ring

end ThetLogos
