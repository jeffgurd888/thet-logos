import Mathlib

/-!
# ThetLogos.FlowSeat — the finite flow seat (spectral-wind / Le Sage failure-mode exhibit)

Charter: `flow-seat-charter-draft-2026-11-05.md`; scoping and pin:
`flow-seat-scoping-2026-11-05.md` (§2 is the pin, §3 the D2 verdict, §4
the menu FS-0…FS-3 and the kill register). Jeff's framing, verbatim
(2026-11-05 16:18 EST): "when I think of something with mass it makes
me think that it creates spectral drag." Jeff originates; this module
audits. Working label only ("FlowSeat"); public naming is Jeff's hand.

## The identity is dead, and stays dead

Spectral drag = gravity as a literal identity is **NO-GO** (audited
2026-11-05 00:46, refined 10:30, pinned on the charter's face before
any build). Drag is zero at rest, so static weight needs a flowing
medium (the Le Sage lineage), incurring shielding/saturation against
gravity's exact linearity in mass, heating/orbital-drag costs with no
room in measured energy accounts, and a clean-passing light channel
that cannot bend light, whereas lensing is measured and achromatic.
Weight tracks energy-momentum; spin is a correction, never the
coupling. **This module is the finite failure-mode exhibit that
survives those fences**: one seat where the identity's three classical
obstructions are theorems of a finite model rather than arguments in
prose — the same species and standing as the surface-tension seat
(`SurfaceTensionSeat.lean`, bulk-blindness proved inside its model).
It is not a gravity candidate, and nothing in it is Dial evidence.

## The pin (Register A — no gravity words)

Sites `Fin n` in their natural order. Three declared inputs and
nothing else: a **mass field** `m : Fin n → ℝ` (declared regime
`m i ≥ 0`); a **flux** `F : ℝ` (declared regime `F ≥ 0`), one global
scalar, the same at every site; and the **exposure rule**, pinned
here before any theorem is stated, in the charter's zero-attaining
hard-shadow form:

> `flowExposure m i = 0` whenever some site `j < i` strictly upstream
> carries positive mass (`flowShadowed m i`); `= 1` otherwise.

Derived quantities, all definitions, no solves: the **force on a
site**, `flowForce m F i := F * flowExposure m i * m i` (the charter's
proportionality form); the **total force**, the sum over sites. The
**second channel** is a parallel declared structure with coupling
constant `flowCleanCoupling = 0`: its path is the site sequence along
the line (`flowCleanPath`), its update rule is the identity
(`flowCleanUpdate`), and its deflection is measured by the impulse
functional `flowChannelImpulse` evaluated at its coupling
(`flowCleanDeflection`).

Stripped of every borrowed word, the object is: *a finite ordered set
carrying a nonnegative field, one global nonnegative scalar, and an
upstream-occlusion rule; a per-site product of the three, summed.* A
reader meeting only Register A recognises a shadow-and-flux
bookkeeping model — momentum transfer through an occluding line; a
historically informed reader identifies the Le Sage mechanism in
miniature, which is the exhibit's purpose, stated here, not a
discovery about it. Nothing in Register A falls, orbits, attracts,
or responds: **the sites are sources, and there is no body in the
seat distinct from the field that sources it.**

**What the seat is NOT.** Not a response law (no test body; no
configuration factorizes into background × body — the RL-7 break,
present here in a second seat). Not a field equation (the force is a
pinned product, not the solution of any equation; nothing is
inverted, solved, or made stationary; there is no stationarity in
the seat at all). Not RL-P1 (no body sector, no action, no medium
there; no body sector or action here — the two objects share no
definition). No `laplacianOp`, no `greenOp`, no `meanSub` occurs
in it.

## Pin-stage checks and decisions, on the face

- **K-FLOW-SAT, pin-stage shape (ii) — checked at FS-0, does NOT
  fire.** The pinned rule attains exposure `0` at every site with
  positive mass strictly upstream, by construction; this is proved
  as `flowExposure_eq_zero`. Shape (i) — exact mass-linearity of
  total force — is refuted by FS-2 (`flowTotalForce_not_linear`), so
  the kill does not fire in that shape either. No re-tuning of the
  shadowing rule was needed or made.
- **Target 3's vacuity risk — discharged at the pin; K-FLOW-BEND
  does NOT fire.** A content-carrying deflection functional *can*
  be stated: the impulse family `flowChannelImpulse c m F p` takes
  the value `n ≠ 0` at unit coupling, unit constant mass, unit flux
  (`flowChannelImpulse_one_const`), so the functional is not
  vacuous. The clean channel is its `c = 0` instance, and the
  declaration is honoured in the formalisation: channel force
  identically `0`, path-update the identity, deflection `0`
  (FS-1). Per the scoping's grade, that is Target 3's ceiling — its
  theorems certify the formalisation honours the declaration, and
  no more; they are not bending theorems and are not stated as such.
- **Weighting (scoping §1/§4).** Target 1 and Target 3 are
  **pin-checks**: their theorems certify the formalisation matches
  the charter. Target 2 (FS-2) is the seat's one theorem with real
  content. This weighting is part of the exhibit's face.
- **Disclosed generality.** The theorems are stated at the
  generality their proofs actually need: several need neither
  `F ≥ 0` nor `m i ≥ 0` (the seat's declared regime, recorded
  above). Where a hypothesis is load-bearing (`a ≥ 0` and the
  shadow-support condition in FS-2; `F ≠ 0` in
  `flowTotalForce_not_linear`) it is on the statement's face.

## D2 eligibility — the §3 verdict, in substance verbatim

**The flow seat is DIAL-INELIGIBLE.** Graded against D2-4 exactly,
it fails on both halves. *Field half:* the total force is a raw sum,
not a contrast — it does not factor through `meanSub`, it uses no
inversion, and adding mass at an exposed site strictly increases it,
so the seat does not inherit the corpus's landed blindness classes
(neither CT-1, `PoissonTotalMassBlindness`, nor the STS count
class); its failure is the opposite one, and it is the seat's own
chartered theorem (FS-2): adding mass in the shadow changes the
total mass and changes the total force **not at all**. A field that
answers total mass only where unoccluded, and is provably
non-linear in it, is not the field D2-4's first signature names —
and there is no field *equation* here at all whose finite shadow
could be Poisson or anything else; the force is a pinned product,
so the field half fails on form before it fails on content.
*Universality half:* universality **cannot even be stated** in this
seat. It is a theorem-shape only where a body carries parameters
besides its mass — a composition variable — and the response is
proved independent of them; here a site carries exactly one datum,
its mass, there is no second parameter to vary, no body to carry
one, and no response of a body to be independent of anything. The
SH-8 check cannot be run. This is CT-8 in its pure form, arrived at
from the opposite direction: there the bodies had no parameters;
here there is no body.

**Verdict: the flow seat is not a gravity candidate, not a
response law, and not Dial evidence of any kind. Its honest
standing is an analog / failure-mode exhibit. Dial 2 = 0.**

## Kill register (all armed at the build; status at landing)

- **K-FLOW-REST** — the pinned force law is not flux-proportional
  in the chartered form. *Does not fire:* the law is pinned as
  `F * exposure * (site mass)` and Target 1 (FS-1) is its tripwire.
- **K-FLOW-SAT** — (i) exact mass-linearity, or (ii) exposure `0`
  attained nowhere. *Does not fire:* see the pin-stage checks above.
- **K-FLOW-BEND** — the zero-coupling declaration not honoured,
  including the case that no content-carrying deflection functional
  can be stated at all. *Does not fire:* see above.
- **K-FLOW-LAUNDER** — any text presenting this seat or any theorem
  of it as a gravity candidate, a response law, or evidence bearing
  on Dial 2. This header is written under it: the §3 verdict above
  must be quoted wherever the seat is summarised.

**NO CLAIM. Dials 0/4. Dial 2 = 0 before this module and 0 after it.**
-/

namespace ThetLogos

-- Classical decidability of the seat's pinned conditions is local
-- to this file (the `AxiomTet.lean` precedent): the exposure rule's
-- `if` is decided by `Classical.propDecidable`, and every theorem
-- below speaks only through the rule's characterisation lemmas
-- (`flowExposure_eq_zero` / `flowExposure_eq_one`), never through an
-- instance computation.
attribute [local instance] Classical.propDecidable

/-! ## FS-0 — the pin (definitions and definitional lemmas only) -/

/-- Shadowing at a site: some site strictly upstream carries
    positive mass. This is the seat's named shadow region — the set
    of sites whose exposure the pinned rule sets to `0`. -/
def flowShadowed {n : ℕ} (m : Fin n → ℝ) (i : Fin n) : Prop :=
  ∃ j : Fin n, j < i ∧ 0 < m j

/-- The exposure rule, pinned on the module's face before any
    theorem: `0` at every shadowed site (positive mass strictly
    upstream), `1` otherwise. It depends only on the mass strictly
    upstream of `i`, and it is zero-attaining by construction — the
    hard-shadow form the charter names. The `if` is decided by
    classical choice (`Classical.propDecidable`), hence
    `noncomputable`. -/
noncomputable def flowExposure {n : ℕ} (m : Fin n → ℝ) (i : Fin n) : ℝ :=
  if flowShadowed m i then 0 else 1

/-- Attainment of exposure `0` (the K-FLOW-SAT pin-stage check,
    shape (ii)): every shadowed site has exposure exactly `0`. -/
theorem flowExposure_eq_zero {n : ℕ} {m : Fin n → ℝ} {i : Fin n}
    (h : flowShadowed m i) : flowExposure m i = 0 := by
  unfold flowExposure
  exact ite_eq_left h

/-- Exposure away from the shadow: with no positive mass strictly
    upstream, the site is fully exposed. -/
theorem flowExposure_eq_one {n : ℕ} {m : Fin n → ℝ} {i : Fin n}
    (h : ¬ flowShadowed m i) : flowExposure m i = 1 := by
  unfold flowExposure
  exact ite_eq_right h

/-- The pinned rule's stated range: exposure always lies in
    `[0, 1]`, as the pin requires. -/
theorem flowExposure_mem_Icc {n : ℕ} (m : Fin n → ℝ) (i : Fin n) :
    flowExposure m i ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases h : flowShadowed m i
  · rw [flowExposure_eq_zero h]
    exact Set.mem_Icc.mpr ⟨le_refl 0, zero_le_one⟩
  · rw [flowExposure_eq_one h]
    exact Set.mem_Icc.mpr ⟨zero_le_one, le_refl 1⟩

/-- The force on a site, in the charter's proportionality form:
    flux × exposure × the site's own mass. A definition — a pinned
    product, not the solution of any equation. -/
noncomputable def flowForce {n : ℕ} (m : Fin n → ℝ) (F : ℝ) (i : Fin n) : ℝ :=
  F * flowExposure m i * m i

/-- The total force: the raw sum of the site forces. Not a
    contrast; it factors through no mean-subtraction and no
    inversion. -/
noncomputable def flowTotalForce {n : ℕ} (m : Fin n → ℝ) (F : ℝ) : ℝ :=
  ∑ i, flowForce m F i

/-- The total mass: the raw sum of the mass field. -/
def flowTotalMass {n : ℕ} (m : Fin n → ℝ) : ℝ :=
  ∑ i, m i

/-- The second channel's coupling constant, declared: `0`. The
    channel passes cleanly by construction of the model, not by a
    theorem smuggled in. -/
def flowCleanCoupling : ℝ := 0

/-- The force the second channel carries at a site: its coupling
    constant times flux times mass — the same product shape as the
    mass channel's law, at coupling `0`. -/
def flowCleanForce {n : ℕ} (m : Fin n → ℝ) (F : ℝ) (i : Fin n) : ℝ :=
  flowCleanCoupling * F * m i

/-- The impulse functional of a channel with coupling `c`: the
    total transverse impulse accumulated along a path `p` (a
    sequence of sites) under mass field `m` and flux `F`. This is
    the seat's deflection functional family; it has content — at
    nonzero coupling it takes nonzero values
    (`flowChannelImpulse_one_const`). -/
def flowChannelImpulse {n : ℕ} (c : ℝ) (m : Fin n → ℝ) (F : ℝ)
    (p : Fin n → Fin n) : ℝ :=
  ∑ k, c * F * m (p k)

/-- The clean channel's deflection: its impulse at its declared
    coupling `0`. -/
def flowCleanDeflection {n : ℕ} (m : Fin n → ℝ) (F : ℝ)
    (p : Fin n → Fin n) : ℝ :=
  flowChannelImpulse flowCleanCoupling m F p

/-- The clean channel's declared path: the site sequence along the
    line, stage `k` at site `k`. -/
def flowCleanPath {n : ℕ} : Fin n → Fin n :=
  fun k => k

/-- The clean channel's path-update rule: the identity, for every
    mass configuration and every flux. The channel's trajectory is
    not steered by the seat's data — by construction of the model,
    which is the declaration FS-1's pin-check certifies. -/
def flowCleanUpdate {n : ℕ} (_m : Fin n → ℝ) (_F : ℝ)
    (p : Fin n → Fin n) : Fin n → Fin n :=
  p

/-! ## FS-1 — rest and the clean channel (PIN-CHECKS)

Both targets in this brick are pin-checks: their theorems certify
that the formalisation matches the charter — that the pinned law
*is* a drag law (force exists only as flux response; K-FLOW-REST's
tripwire) and that the zero-coupling declaration is honoured in the
formalisation. They are not discoveries, and they are not bending
theorems. The seat's one theorem with real content is FS-2. -] -/

/-- Target 1 (pin-check) — no flow, no force: at flux `F = 0` the
    force on every site is `0`, for every mass configuration. A
    resting mass in a still spectrum weighs nothing in this model:
    failure mode 1 of the identity, as a theorem. The proof is one
    simp step because the content is definitional — the pinned law
    has `F` as a factor. -/
theorem flowForce_eq_zero_of_flux_zero {n : ℕ} {m : Fin n → ℝ} {F : ℝ}
    (hF : F = 0) (i : Fin n) : flowForce m F i = 0 := by
  simp [flowForce, hF]

/-- Target 1, total form (pin-check): at flux `0` the total force
    vanishes for every configuration. -/
theorem flowTotalForce_eq_zero_of_flux_zero {n : ℕ} {m : Fin n → ℝ}
    {F : ℝ} (hF : F = 0) : flowTotalForce m F = 0 := by
  unfold flowTotalForce
  exact Finset.sum_eq_zero fun i _ => flowForce_eq_zero_of_flux_zero hF i

/-- Target 3, force form (pin-check): the clean channel's force is
    identically `0` — at every site, every mass configuration,
    every flux — because its declared coupling is `0`. -/
theorem flowCleanForce_eq_zero {n : ℕ} (m : Fin n → ℝ) (F : ℝ)
    (i : Fin n) : flowCleanForce m F i = 0 := by
  simp [flowCleanForce, flowCleanCoupling]

/-- Target 3, path form (pin-check): the clean channel's update
    rule is the identity — the updated path is the declared path,
    for every mass configuration and every flux. This is the
    declaration itself, stated as a theorem so the fence can check
    it; it certifies the formalisation honours the declaration and
    nothing more. -/
theorem flowCleanUpdate_eq {n : ℕ} (m : Fin n → ℝ) (F : ℝ)
    (p : Fin n → Fin n) : flowCleanUpdate m F p = p :=
  rfl

/-- Target 3, deflection form (pin-check): the clean channel's
    deflection is `0` along every path, for every mass
    configuration and every flux — what passes cleanly cannot be
    steered in this model: failure mode 3 of the identity, as a
    theorem, at the ceiling the charter fixes for it (it certifies
    the declaration is honoured; it is not a bending theorem). -/
theorem flowCleanDeflection_eq_zero {n : ℕ} (m : Fin n → ℝ) (F : ℝ)
    (p : Fin n → Fin n) : flowCleanDeflection m F p = 0 := by
  unfold flowCleanDeflection flowChannelImpulse
  exact Finset.sum_eq_zero fun k _ => by simp [flowCleanCoupling]

/-- The deflection functional has content (the Target-3 vacuity
    check): at unit coupling, unit constant mass and unit flux, the
    impulse along any path over `Fin n` is exactly `n` — nonzero
    whenever the line is nonempty. The functional family therefore
    takes nonzero values; the clean channel's deflection vanishes
    because its coupling is `0`, not because the functional is
    vacuous. -/
theorem flowChannelImpulse_one_const {n : ℕ} (p : Fin n → Fin n) :
    flowChannelImpulse (1 : ℝ) (fun _ => 1) 1 p = (n : ℝ) := by
  unfold flowChannelImpulse
  simp

/-! ## FS-2 — saturation (the seat's one theorem with real content)

Target 2: mass added entirely inside the shadow changes the total
mass and changes the total force **not at all**. The workhorse is
pointwise: at every site the force of the augmented configuration
equals the force of the original. At a shadowed site both forces
vanish (the site stays shadowed — the original witness still has
positive mass, since the addition is nonnegative). At an exposed
site the addition vanishes at the site and at every site upstream
of it (mass of the addition anywhere upstream would sit in the
shadow of the original configuration, which is downstream-closed),
so the site's exposure and mass are unchanged. -/

/-- The FS-2 workhorse (pointwise): if the addition `a` is
    nonnegative and supported on the shadow of `m` (it can be
    nonzero only at sites shadowed in `m`), then adding it changes
    the force at **no** site, at any flux. -/
theorem flowForce_add_supported_on_shadow {n : ℕ} {m a : Fin n → ℝ}
    {F : ℝ} (ha0 : ∀ i, 0 ≤ a i)
    (hsupp : ∀ i, a i ≠ 0 → flowShadowed m i) (k : Fin n) :
    flowForce (m + a) F k = flowForce m F k := by
  by_cases hk : flowShadowed m k
  · have hk' : flowShadowed (m + a) k := by
      obtain ⟨j, hjk, hjm⟩ := hk
      refine ⟨j, hjk, ?_⟩
      have haj := ha0 j
      rw [Pi.add_apply]
      linarith
    simp [flowForce, flowExposure_eq_zero hk, flowExposure_eq_zero hk']
  · have ha_up : ∀ j : Fin n, j < k → a j = 0 := by
      intro j hjk
      by_contra haj
      obtain ⟨j', hj'j, hj'm⟩ := hsupp j haj
      exact hk ⟨j', hj'j.trans hjk, hj'm⟩
    have hak : a k = 0 := by
      by_contra haj
      exact hk (hsupp k haj)
    have hk' : ¬ flowShadowed (m + a) k := by
      rintro ⟨j, hjk, hjpos⟩
      rw [Pi.add_apply, ha_up j hjk, add_zero] at hjpos
      exact hk ⟨j, hjk, hjpos⟩
    simp only [flowForce, flowExposure_eq_one hk, flowExposure_eq_one hk',
      Pi.add_apply, hak, add_zero]

/-- Target 2, universal form: total force is unchanged by any
    nonnegative addition supported on the shadow. -/
theorem flowTotalForce_add_supported_on_shadow {n : ℕ}
    {m a : Fin n → ℝ} {F : ℝ} (ha0 : ∀ i, 0 ≤ a i)
    (hsupp : ∀ i, a i ≠ 0 → flowShadowed m i) :
    flowTotalForce (m + a) F = flowTotalForce m F := by
  unfold flowTotalForce
  exact Finset.sum_congr rfl fun k _ =>
    flowForce_add_supported_on_shadow ha0 hsupp k

/-- The witness base configuration on two sites: unit mass at the
    upstream site, none downstream. -/
def flowSeatBase : Fin 2 → ℝ := ![1, 0]

/-- The witness loaded configuration: the base configuration with
    five more units of mass placed at the downstream site — which
    lies entirely in the base configuration's shadow. -/
def flowSeatLoaded : Fin 2 → ℝ := flowSeatBase + ![0, 5]

/-- The two witness configurations have equal total force at every
    flux (the loaded configuration's extra mass is invisible to the
    force, being entirely shadowed). -/
theorem flowTotalForce_witness (F : ℝ) :
    flowTotalForce flowSeatLoaded F = flowTotalForce flowSeatBase F := by
  apply flowTotalForce_add_supported_on_shadow (m := flowSeatBase)
    (a := ![0, 5])
  · intro i
    fin_cases i <;> simp
  · intro i hi
    fin_cases i
    · simp at hi
    · exact ⟨0, by decide, by simp [flowSeatBase]⟩

/-- Saturation / shielding — the seat's blindness-form headline
    (Target 2), in the form of the landed precedent
    `tensionCount_does_not_determine_mass`: the two witness
    configurations have the *same* total force (at every flux) but
    *different* total masses (`1 ≠ 6`). The total force does not
    determine the total mass: failure mode 2 of the identity, as a
    theorem. -/
theorem flowTotalForce_does_not_determine_mass (F : ℝ) :
    flowTotalForce flowSeatBase F = flowTotalForce flowSeatLoaded F ∧
      flowTotalMass flowSeatBase ≠ flowTotalMass flowSeatLoaded := by
  refine ⟨(flowTotalForce_witness F).symm, ?_⟩
  simp [flowTotalMass, flowSeatLoaded, flowSeatBase, Fin.sum_univ_two]

/-- Corollary, on the face: total force is **not** a linear
    function of total mass in this seat. At any nonzero flux there
    is no constant `c` with `flowTotalForce m F = c * flowTotalMass
    m` for all nonnegative configurations on two sites — the base
    configuration forces `c = F` (mass `1`, force `F`), the loaded
    configuration forces `c = F / 6` (mass `6`, same force). This
    refutes K-FLOW-SAT's firing shape (i): the pinned rule does not
    yield exact mass-linearity. -/
theorem flowTotalForce_not_linear {F : ℝ} (hF : F ≠ 0) :
    ¬ ∃ c : ℝ, ∀ m : Fin 2 → ℝ, (∀ i, 0 ≤ m i) →
      flowTotalForce m F = c * flowTotalMass m := by
  rintro ⟨c, hc⟩
  have hbase_nn : ∀ i, 0 ≤ flowSeatBase i := by
    intro i
    fin_cases i <;> simp [flowSeatBase]
  have hloaded_nn : ∀ i, 0 ≤ flowSeatLoaded i := by
    intro i
    fin_cases i <;> simp [flowSeatLoaded, flowSeatBase]
  have hm1 : flowTotalMass flowSeatBase = 1 := by
    simp [flowTotalMass, flowSeatBase, Fin.sum_univ_two]
  have hm2 : flowTotalMass flowSeatLoaded = 6 := by
    simp only [flowTotalMass, flowSeatLoaded, flowSeatBase, Fin.sum_univ_two,
      Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  have hf : flowTotalForce flowSeatBase F = F := by
    have hexp0 : flowExposure flowSeatBase 0 = 1 := by
      apply flowExposure_eq_one
      rintro ⟨j, hj, -⟩
      exact absurd hj (by simp)
    have hsite0 : flowForce flowSeatBase F 0 = F := by
      simp only [flowSeatBase] at hexp0
      simp [flowForce, flowSeatBase, hexp0]
    have hsite1 : flowForce flowSeatBase F 1 = 0 := by
      simp [flowForce, flowSeatBase]
    rw [flowTotalForce, Fin.sum_univ_two, hsite0, hsite1, add_zero]
  have e1 := hc flowSeatBase hbase_nn
  have e2 := hc flowSeatLoaded hloaded_nn
  rw [hm1] at e1
  rw [hm2, flowTotalForce_witness F, hf] at e2
  rw [hf] at e1
  have hcF : c = F := by linarith
  subst hcF
  rw [mul_comm] at e2
  apply hF
  linarith

end ThetLogos
