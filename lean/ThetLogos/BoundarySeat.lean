import Mathlib.Tactic
import ThetLogos.PoissonTotalMassBlindness
import ThetLogos.BridgeCompletion

/-!
# ThetLogos.BoundarySeat — UA-2: the boundary / open seat (Gate A, standalone) (T1)

HONESTY LEDGER (read before citing):

- **Working label only.** UA-2 and this module name are working
  labels from the untried-gravity-angles scoping dossier
  (`~/workspace/your_files/gravity-untried-angles-scoping-2026-11-06.md`,
  §2/§5); Jeff names.
- **What this is.** The **Gate A** seat of the response-law
  scoping (`response-law-scoping-2026-11-05.md`, §7), scoped
  standalone: the closed seat of T2 (`ThermalChargePoisson`)
  with one site `b` **grounded** — its potential value is pinned
  to `0` (a Dirichlet condition) — and the Poisson equation
  imposed at every *other* site. On the closed seat, a
  potential exists iff the source total vanishes, and every
  quantity factoring through the inversion is **total-mass
  blind** (CT-1 / K-SR-4, landed T1 in
  `PoissonTotalMassBlindness`: `poissonField (g + c) =
  poissonField g`). On this seat the ground absorbs the
  incompatibility: a grounded potential exists for an
  **arbitrary** source — no `∑ i, g i = 0` hypothesis — it is
  unique, and the inversion is **total-mass sensitive**:
  sources differing by a constant (a pure total-mass
  difference, at fixed contrast) have *different* grounded
  potentials and *different* fields here
  (`groundedPotential_add_const_ne`,
  `groundedField_add_const_ne`,
  `exists_groundedField_detects_totalMass`) — the exact
  negation of the closed seat's blindness, on the record as
  its contrast.
- **Pre-registered disposition (scoping §5, honored).** This
  brick is **Dial-INELIGIBLE**, on its face, under every
  outcome. It buys D2-4's **field half only**: a field
  channel that can see a total. It seats **no test body**,
  defines **no response law**, and nothing in it falls,
  descends, or is attracted. Any presentation of this module
  as Dial progress, a gravity object, or a response law
  fires **K-UA2-LAUNDER** (pre-registered). **NO CLAIM;
  dials 0/4. Dial 2 = 0.**
- **The dictionary (G-READ discipline, stated once).**
  *Source*: a real-valued function `g` on the vertices —
  data; "total mass" in this module means exactly the
  number `∑ i, g i`, the usage the closed seat's blindness
  theorems already fixed. *Potential*: the determined
  function `φ` with `laplacianOp w φ = g` at every
  ungrounded site and `φ b = 0`. *Field*: its edge drop
  `dropVec φ`. The sign is the landed one (`laplacianOp`
  as in `BridgeLaplacian`, the same operator T2 inverts);
  no sign is chosen here. Every other word a gravitational
  reading would want — attraction, falling, force — is a
  **reading, not a theorem**, and appears nowhere below.
- **Pre-registered kill K-UA2-CLOSED, disposition.** If the
  grounded construction had collapsed to the closed seat —
  the grounded minor singular, the inversion secretly
  re-imposing `∑ i, g i = 0` — this module would land as
  that negative instead. It does not: existence below is
  proved for arbitrary `g` by absorbing the total at the
  ground, and uniqueness by the current law plus the
  kernel characterization. K-UA2-CLOSED does **not** fire;
  the sensitivity theorems are the standing witness that
  the constants are *not* killed by this inversion.
- **The one-site seat.** If `V = {b}` there is no ungrounded
  site, the grounded potential is `0`, and the sensitivity
  statements are vacuous — they carry an explicit witness
  hypothesis (`i ≠ b`) saying so. No hypothesis is hidden.
- Everything here is T1 finite linear algebra on the
  `BridgeLaplacian` seat, consuming T2 and SHADOW-TEST-1 at
  their landed shapes. Zero sorrys, no `native_decide`,
  headline axioms exactly the standard three (`propext`,
  `Classical.choice`, `Quot.sound`).
- SEP FENCES, STANDING. No operator separates charge by its
  own action; no charge operator and no electromagnetic
  field object is claimed at this seat; β appears nowhere.
  Determination, not self-organization. Finite graph statics
  only.
-/

namespace ThetLogos

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## §1. The absorbed source: the ground takes the total

Name-collision note, at full rank: the pointwise difference
lemma this brick first drafted as `laplacianOp_sub` already
exists in the corpus at function grade (`BridgeCompletion`,
T1) — the draft was dropped and the landed lemma consumed
instead; the frozen interface's one name change, recorded
here rather than silently. Every other frozen name is
unchanged from the pin. -/

/-- The **absorbed source**: `g` itself at every ungrounded
site, and at the ground `b` the value that makes the total
vanish — `g b` minus the total of `g`. This is the whole
construction: the closed seat's compatibility condition is
met by letting the ground carry the imbalance, instead of
imposing it on the source. -/
noncomputable def groundedSource (b : V) (g : V → ℝ) : V → ℝ :=
  fun i => if i = b then g b - ∑ j, g j else g i

/-- The absorbed source is the source itself away from the
ground: the absorption touches exactly one site. -/
theorem groundedSource_apply_of_ne (b : V) (g : V → ℝ) {i : V}
    (hi : i ≠ b) : groundedSource b g i = g i :=
  if_neg hi

/-- The absorbed source always has total zero — it is always
a legitimate input to the closed seat's inversion (T2). -/
theorem sum_groundedSource_eq_zero (b : V) (g : V → ℝ) :
    ∑ i, groundedSource b g i = 0 := by
  have hsplit := (Finset.add_sum_erase Finset.univ (groundedSource b g)
    (Finset.mem_univ b)).symm
  have hrest : ∑ i ∈ Finset.univ.erase b, groundedSource b g i
      = ∑ i ∈ Finset.univ.erase b, g i :=
    Finset.sum_congr rfl fun i hi =>
      groundedSource_apply_of_ne b g (Finset.mem_erase.mp hi).1
  have hsum := Finset.add_sum_erase Finset.univ g (Finset.mem_univ b)
  have hb : groundedSource b g b = g b - ∑ j, g j := if_pos rfl
  rw [hsplit, hb, hrest]
  linarith

/-! ## §2. A pointwise fact about the landed operator -/

/-- Shifting a potential by a constant does not change its
Laplacian — the closed seat's kernel fact, pointwise. (On
the grounded seat the shift is what *sets* the ground
value.) The difference law this section also drafted is
the corpus's own `laplacianOp_sub` (`BridgeCompletion`,
function grade) and is consumed from there. -/
theorem laplacianOp_sub_const (w : V → V → ℝ) (f : V → ℝ)
    (c : ℝ) (i : V) :
    laplacianOp w (fun k => f k - c) i = laplacianOp w f i := by
  show (∑ j, w i j * ((f i - c) - (f j - c)))
      = ∑ j, w i j * (f i - f j)
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  ring

/-! ## §3. The Dirichlet inversion: existence and uniqueness -/

/-- **Existence, for arbitrary sources.** For every source
`g` — no total-vanishing hypothesis — there is a potential
pinned to `0` at the ground and solving the Poisson
equation at every ungrounded site. The ground absorbs the
total; that is the entire difference from the closed seat,
where the bare ∀-form is false. -/
theorem exists_groundedPotential (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (b : V) (g : V → ℝ) :
    ∃ φ : V → ℝ, φ b = 0 ∧
      ∀ i ≠ b, laplacianOp w φ i = g i := by
  obtain ⟨φ₀, hφ₀⟩ := exists_potential_of_sum_eq_zero w hw hw0 hpos
    (groundedSource b g) (sum_groundedSource_eq_zero b g)
  refine ⟨fun k => φ₀ k - φ₀ b, sub_self _, ?_⟩
  intro i hi
  rw [laplacianOp_sub_const w φ₀ (φ₀ b) i, congrFun hφ₀ i]
  exact groundedSource_apply_of_ne b g hi

/-- **Uniqueness.** Two grounded potentials for the same
source agree everywhere: their difference is grounded,
its Laplacian vanishes at every ungrounded site, the
current law (`∑ i, (L u) i = 0`) forces it to vanish at
the ground too, and a function in the kernel is constant
— here, constantly `0`. -/
theorem groundedPotential_unique (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (b : V) (g : V → ℝ)
    (φ ψ : V → ℝ) (hφb : φ b = 0) (hψb : ψ b = 0)
    (hφ : ∀ i ≠ b, laplacianOp w φ i = g i)
    (hψ : ∀ i ≠ b, laplacianOp w ψ i = g i) :
    φ = ψ := by
  have hLu : ∀ i ≠ b,
      laplacianOp w (fun k => φ k - ψ k) i = 0 := by
    intro i hi
    have hsub := congrFun (laplacianOp_sub w φ ψ) i
    simp only [Pi.sub_apply] at hsub
    have hfun : (fun k => φ k - ψ k) = φ - ψ := by
      funext k
      simp [Pi.sub_apply]
    rw [hfun, hsub, hφ i hi, hψ i hi, sub_self]
  have hsum : ∑ i, laplacianOp w (fun k => φ k - ψ k) i = 0 :=
    sum_laplacianOp_eq_zero w hw _
  have herase : ∑ i ∈ Finset.univ.erase b,
      laplacianOp w (fun k => φ k - ψ k) i = 0 :=
    Finset.sum_eq_zero fun i hi => hLu i (Finset.mem_erase.mp hi).1
  have hsplit := Finset.add_sum_erase Finset.univ
    (fun i => laplacianOp w (fun k => φ k - ψ k) i) (Finset.mem_univ b)
  have hLb : laplacianOp w (fun k => φ k - ψ k) b = 0 := by
    rw [herase, add_zero] at hsplit
    rw [hsplit, hsum]
  have hL : laplacianOp w (fun k => φ k - ψ k) = 0 := by
    funext i
    by_cases hi : i = b
    · subst hi; exact hLb
    · exact hLu i hi
  have hconst := eq_const_of_laplacianOp_eq_zero w hw hw0 hpos _ hL
  funext i
  have hi : φ i - ψ i = φ b - ψ b := hconst i b
  rw [hφb, hψb, sub_self] at hi
  exact sub_eq_zero.mp hi

/-- **The canonical grounded potential** of a source: the
unique potential pinned at the ground, by §3. -/
noncomputable def groundedPotential (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (b : V) (g : V → ℝ) :
    V → ℝ :=
  Classical.choose (exists_groundedPotential w hw hw0 hpos b g)

/-- The canonical grounded potential is pinned at the
ground. -/
theorem groundedPotential_at_ground (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (b : V) (g : V → ℝ) :
    groundedPotential w hw hw0 hpos b g b = 0 :=
  (Classical.choose_spec
    (exists_groundedPotential w hw hw0 hpos b g)).1

/-- The canonical grounded potential solves the Poisson
equation at every ungrounded site, for the source itself —
not for a projection of it. -/
theorem laplacianOp_groundedPotential (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (b : V) (g : V → ℝ)
    {i : V} (hi : i ≠ b) :
    laplacianOp w (groundedPotential w hw hw0 hpos b g) i
      = g i :=
  (Classical.choose_spec
    (exists_groundedPotential w hw hw0 hpos b g)).2 i hi

/-! ## §4. The field of the grounded seat -/

/-- **The field of a source on the grounded seat**: the edge
drop of its grounded potential. Well-defined because the
grounded potential is unique (§3). -/
noncomputable def groundedField (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (b : V) (g : V → ℝ) :
    V → V → ℝ :=
  dropVec (groundedPotential w hw hw0 hpos b g)

/-! ## §5. Total-mass sensitivity: the blindness, negated -/

/-- **The grounded potential sees a constant shift.** Two
sources differing by a nonzero constant — the same
contrast, a different total — have *different* grounded
potentials, as soon as one ungrounded site exists to
witness the equation there. This is the pointwise
negation of the closed seat's `poissonField_add_const`
invariance. -/
theorem groundedPotential_add_const_ne (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (b : V) (g : V → ℝ)
    (c : ℝ) (hc : c ≠ 0) {i : V} (hi : i ≠ b) :
    groundedPotential w hw hw0 hpos b (fun j => g j + c)
      ≠ groundedPotential w hw hw0 hpos b g := by
  intro hEq
  have h1 := laplacianOp_groundedPotential w hw hw0 hpos b
    (fun j => g j + c) hi
  have h2 := laplacianOp_groundedPotential w hw hw0 hpos b g hi
  rw [hEq] at h1
  rw [h2] at h1
  have h1' : g i = g i + c := h1
  have hc0 : c = 0 := by linarith
  exact hc hc0

/-- **The grounded field sees a constant shift.** The same
sensitivity at the field: were the two fields equal, the
two potentials would differ by a constant (the drop sees
every difference), and two *grounded* potentials differing
by a constant are equal — contradiction with §5's first
theorem. -/
theorem groundedField_add_const_ne (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (b : V) (g : V → ℝ)
    (c : ℝ) (hc : c ≠ 0) {i : V} (hi : i ≠ b) :
    groundedField w hw hw0 hpos b (fun j => g j + c)
      ≠ groundedField w hw hw0 hpos b g := by
  intro hEq
  have hpot : groundedPotential w hw hw0 hpos b (fun j => g j + c)
      = groundedPotential w hw hw0 hpos b g := by
    funext k
    have hd : dropVec (groundedPotential w hw hw0 hpos b
          (fun j => g j + c)) k b
        = dropVec (groundedPotential w hw hw0 hpos b g) k b :=
      congrFun (congrFun hEq k) b
    rw [dropVec_apply, dropVec_apply,
      groundedPotential_at_ground, groundedPotential_at_ground] at hd
    linarith
  exact groundedPotential_add_const_ne w hw hw0 hpos b g c hc hi hpot

/-- **A quantity of the grounded field detects total
mass.** The positive counterpart of the closed seat's
decision theorem (`not_exists_fieldFactor_detects_totalMass`,
SHADOW-TEST-1): on the grounded seat there *is* a quantity
of the field data, a source, and a nonzero constant shift
at which the quantity responds to the shift — the identity
quantity at the zero source and the unit shift already
does. Detecting a total is all this says: the channel sees
`∑ i, g i`; no body answers it, and no law of response is
stated or implied. -/
theorem exists_groundedField_detects_totalMass (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (b : V)
    (hi : ∃ i, i ≠ b) :
    ∃ (F : (V → V → ℝ) → ℝ) (g : V → ℝ) (c : ℝ), c ≠ 0 ∧
      F (groundedField w hw hw0 hpos b (fun j => g j + c))
        ≠ F (groundedField w hw hw0 hpos b g) := by
  obtain ⟨i, hi⟩ := hi
  have hne := groundedField_add_const_ne w hw hw0 hpos b (0 : V → ℝ) 1
    one_ne_zero hi
  rw [Function.ne_iff] at hne
  obtain ⟨p, hp⟩ := hne
  rw [Function.ne_iff] at hp
  obtain ⟨q, hq⟩ := hp
  exact ⟨fun X => X p q, 0, 1, one_ne_zero, hq⟩

/-- **The grounded potential determines the source at
every ungrounded site.** Equal grounded potentials have
the same Laplacian there, and the Laplacian there *is*
the source: the inversion loses nothing except the
ground's own value, which the ground absorbs by design. -/
theorem interior_eq_of_groundedPotential_eq (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (b : V) (g g' : V → ℝ)
    (h : groundedPotential w hw hw0 hpos b g
       = groundedPotential w hw hw0 hpos b g')
    {i : V} (hi : i ≠ b) : g i = g' i := by
  have h1 := laplacianOp_groundedPotential w hw hw0 hpos b g hi
  have h2 := laplacianOp_groundedPotential w hw hw0 hpos b g' hi
  rw [h] at h1
  rw [h2] at h1
  exact h1.symm

end ThetLogos
