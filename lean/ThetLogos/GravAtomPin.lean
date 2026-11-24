import Mathlib.Tactic
import ThetLogos.BoundarySeat
import ThetLogos.BridgeLaplacian
import ThetLogos.BridgeCompletion
import ThetLogos.FallPin
import ThetLogos.FallFloorPin
import ThetLogos.GravAtomContinuum

/-!
# ThetLogos.GravAtomPin — the gravitational atom, finite register
(Form 2 of the gravitational-atom pin)

Scope of record:
`~/workspace/your_files/gravitational-atom-scope-2026-11-21.md`
(§§2–6). Commissioned by Zero 2026-11-21 12:45 EST
("Gravitational atomic structure must be next"), clarified
12:48 EST ("i want to prove it mathematically"), fired 16:21
EST ("build it"). The continuum statement register is
`GravAtomContinuum` (Form 1); this module is the finite-seat
build, in the `fall1` lineage (imports FallPin + FallFloorPin
+ BridgeCompletion), riding the same future integration as
FallFloorPin. **Working labels only; Zero names.**

## What this is

The composition the gravity bench had never made (scope §2.7):
one datum carrying a finite seat, its weights, a centre, and a
light source — with the well the source's own grounded
potential (FALL-1), selection by the fall energy (FF-7), the
floor dichotomy (FF-3/FF-5/FF-6), and the seat Laplacian's
excitation spectrum (the Bridge Fiedler package) read as the
atom's levels. The genuinely new matter is exactly: the datum
itself (GA-0), the first computed wells in the corpus (GA-2),
the first spectrum attached to a sourced well (GA-3), the
rhyme verdict against Form 1's ladder (GA-4), and the
stability composition (GA-5, Form 3's non-collapsing residue).

## Fences (checked at every brick, not once)

- **The analog fence, in the OrbifoldGapPin fence's own
  words: a finite graph gap, not a continuum gap, not a
  measured number.** The "levels" are eigenvalues of a finite
  graph Laplacian. `atomGap` is never called a "mass gap"
  (**K-GA-NAME**). The seat weights and the well are never
  called "gravity" without this fence. No `G` anywhere in
  this module. No dynamics, no orbits in time, no force.
- **K-GA-SELF:** self-seating is DEFINITIONAL here — the
  source `ρ` is datum, the well is its grounded potential,
  and the recovery of `ρ` as `laplacianOp` of the well
  off-ground is FALL-1's `laplacianOp_groundedPotential`,
  cited. No fixed point is solved, no self-consistency
  existence theorem is proved or claimed, and none may be
  presented as discovered.
- **K-GA-DUP (standing audit):** GA-1 IS packaging over
  FallFloorPin, disclosed on its face below. The pin earns
  its module at GA-2 / GA-3 / GA-5. If those bricks fail or
  come back as restatements, the pin collapses to the GA-0
  registration card and must be reported as such.
- **K-GA-DUP-FLOOR:** floor uniqueness is fenced by the
  datum's regime field (`∃ i ≠ b, 0 < ρ i`). Any statement of
  floor uniqueness with that hypothesis dropped or weakened
  fires this kill automatically; GA-1(iv) names the excluded
  regime on the pin's own face (FF-5b; FF-6 is the standing
  Fin 2 exhibit).
- **K-GA-SELECT** is armed over every future generalization
  that drops completeness (`hpos`): FALL-1's
  `fall_countermodel_strands` shows sparse seats strand.
- **Dial 2 = 0 under every outcome, including a full
  landing. NO CLAIM; dials 0/4.** Zero sorrys, no
  `native_decide`; headline axioms exactly the standard three
  (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace ThetLogos

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## GA-0 — the datum (registration; 0 strict by design) -/

/-- **The gravitational-atom datum.** A finite seat `V` with
complete symmetric nonnegative weights `w` (completeness
`hpos` carried as a hypothesis, as everywhere on this bench),
a centre `b`, and a light source `ρ` in the **atomic regime**:
`ρ ≥ 0`, no source at the centre (`ρ b = 0`), and source
strictly positive at at least one ungrounded site — exactly
the hypothesis that separates FF-5a's unique floor from
FF-6's dup. The datum states the object; it proves nothing. -/
structure GravAtom (V : Type*) [Fintype V] [DecidableEq V] where
  /-- The seat weights (the gravity-analog; see the header
  fence — never "gravity" without it). -/
  w : V → V → ℝ
  /-- Symmetry of the weights. -/
  hw : ∀ i j, w i j = w j i
  /-- Nonnegativity of the weights. -/
  hw0 : ∀ i j, 0 ≤ w i j
  /-- Completeness: every off-diagonal weight is positive. -/
  hpos : ∀ i j, i ≠ j → 0 < w i j
  /-- The centre. -/
  b : V
  /-- The light source — the atom's own mass distribution. -/
  ρ : V → ℝ
  /-- The source is nonnegative. -/
  hρ : ∀ i, 0 ≤ ρ i
  /-- No source sits at the centre. -/
  hρb : ρ b = 0
  /-- The atomic regime: some ungrounded site carries
  positive source. -/
  hregime : ∃ i ≠ b, 0 < ρ i

/-- **The atom's well**: the grounded potential of its own
source, pinned to zero at the centre. Self-seating is
definitional (K-GA-SELF, header): `ρ` is datum, the well is
`groundedPotential` of it, nothing is solved. -/
noncomputable def atomWell (A : GravAtom V) : V → ℝ :=
  groundedPotential A.w A.hw A.hw0 A.hpos A.b A.ρ

/-- **The atom's excitation gap**: the Fiedler value of the
seat weights — a finite graph gap, not a continuum gap, not
a measured number, and never a "mass gap" (K-GA-NAME). -/
noncomputable def atomGap (A : GravAtom V) : ℝ :=
  fiedler A.w

/-! ## GA-1 — selection in atom vocabulary

**Disclosure (K-GA-DUP, standing): this brick is packaging
over FallFloorPin.** Each theorem is FF-3 / FF-5a / FF-7b /
FF-5b composed through the datum. Its strict count is honest
but thin; the pin's new matter is GA-2 / GA-3 / GA-5. -/

/-- **GA-1(i) — the atom's floor.** The well's floor value is
exactly `0`, attained at the centre, and the well is
nonnegative everywhere. (FF-3 composed.) -/
theorem atomWell_floor_value (A : GravAtom V) :
    (∀ j, 0 ≤ atomWell A j) ∧ atomWell A A.b = 0 :=
  groundedPotential_floor_value A.w A.hw A.hw0 A.hpos A.b A.ρ
    A.hρ

/-- **GA-1(ii) — the floor is attained uniquely at the
centre.** The datum's regime field is what fences
K-GA-DUP-FLOOR here. (FF-5a composed.) -/
theorem atomWell_unique_floor (A : GravAtom V) {m : V}
    (hm : IsFallMin (atomWell A) m) : m = A.b := by
  obtain ⟨i, hi, hρi⟩ := A.hregime
  exact groundedPotential_unique_floor_of_pos A.w A.hw A.hw0
    A.hpos A.b A.ρ A.hρ hi hρi hm

/-- **GA-1(iii) — selection.** The atom's well is the unique
minimizer of the fall energy among grounded candidates: the
gravity-analog functional selects the own-mass well.
(FF-7b composed; K-GA-SELECT does not fire on complete
seats.) -/
theorem atomWell_unique_minimizer (A : GravAtom V) (ψ : V → ℝ)
    (hψb : ψ A.b = 0)
    (hmin : fallEnergy A.w A.b A.ρ ψ
      ≤ fallEnergy A.w A.b A.ρ (atomWell A)) :
    ψ = atomWell A :=
  groundedPotential_unique_minimizer_fallEnergy A.w A.hw
    A.hw0 A.hpos A.b A.ρ ψ hψb hmin

/-- **GA-1(iv) — the boundary of the datum.** Drop the
regime field: if a source vanishes at every ungrounded site,
its grounded potential — the would-be atom well — is
identically zero: the empty atom is floor-everywhere, and
uniqueness dies with it. (FF-5b composed; FF-6,
`fall_floor_not_unique`, is the standing exhibit of the
failure, and K-GA-DUP-FLOOR is the kill this boundary
names.) Stated over the bare grounded potential because a
`GravAtom` datum cannot, by construction, leave the atomic
regime — the boundary lives exactly where the datum ends. -/
theorem atomWell_eq_zero_of_source_vanishes (w : V → V → ℝ)
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : ∀ i j, i ≠ j → 0 < w i j) (b : V) (ρ : V → ℝ)
    (hρ : ∀ i ≠ b, ρ i = 0) :
    groundedPotential w hw hw0 hpos b ρ = 0 :=
  groundedPotential_eq_zero_of_source_vanishes w hw hw0 hpos
    b ρ hρ

/-! ## GA-2 — the headline exhibit: the three-site atom

**DUAL CREDIT.** This brick is also the queued Fall Floor
Fin-3 census (Zero's seeing, 2026-11-21 11:15 EST, verbatim:
"I think that when you find the three-site seat you will find
the uniqueness" — clarified by Zero: "for the fall floor").
The Fin-3 dichotomy is built ONCE here, by exhibit, and
credited to both commissions: the positive regime (the atom's
regime) has its well computed exactly and its floor unique at
the centre; the flat regime (`ρ ≡ 0` off-ground) has
`φ ≡ ![0,0,0]` with the floor at all three sites — the
seeing's counter-form, which on Fin 3 is a flat floor TRIPLE,
firing the seeing's kill in exactly the regime FF-5b names.
The seeing survives precisely in the positive regime. (FF-5a
is already proved in full generality; this brick is the
census made concrete, and says so.) -/

/-- The headline seat weights: complete unit weights on
`Fin 3` — every pair of distinct sites joined with weight 1. -/
def gravAtomSeatW : Fin 3 → Fin 3 → ℝ :=
  ![![0, 1, 1], ![1, 0, 1], ![1, 1, 0]]

/-- **The headline three-site atom**: centre `0`, one light
quantum of source on each outer site (`ρ = ![0, 1, 1]`). -/
def gravAtomSeat : GravAtom (Fin 3) where
  w := gravAtomSeatW
  hw := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [gravAtomSeatW, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two]
  hw0 := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [gravAtomSeatW, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two]
  hpos := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [gravAtomSeatW, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two]
  b := 0
  ρ := ![0, 1, 1]
  hρ := by
    intro i
    fin_cases i <;>
      simp [Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two]
  hρb := by
    simp [Matrix.cons_val_zero]
  hregime := ⟨1, by decide, by
    norm_num [Matrix.cons_val_one, Matrix.head_cons]⟩

/-- **GA-2 headline: the three-site atom's well, computed
exactly.** `atomWell gravAtomSeat = ![0, 1, 1]` — the well
rises one unit at each outer site. The first computed well
in the corpus. Route: `groundedPotential_unique` against
the exhibited vector (the FF-6 pattern): with `φ₀ = 0`, the
Poisson equations at sites 1, 2 read `2φ₁ - φ₂ = 1` and
`-φ₁ + 2φ₂ = 1`, solved by `φ₁ = φ₂ = 1`. -/
theorem gravAtomSeat_well : atomWell gravAtomSeat = ![0, 1, 1] := by
  classical
  have hwA : ∀ i j : Fin 3,
      ((![![0, 1, 1], ![1, 0, 1], ![1, 1, 0]] : Fin 3 → Fin 3 → ℝ) i j)
        = ((![![0, 1, 1], ![1, 0, 1], ![1, 1, 0]]
            : Fin 3 → Fin 3 → ℝ) j i) := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two]
  have hw0A : ∀ i j : Fin 3,
      0 ≤ ((![![0, 1, 1], ![1, 0, 1], ![1, 1, 0]]
        : Fin 3 → Fin 3 → ℝ) i j) := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two]
  have hposA : ∀ i j : Fin 3, i ≠ j →
      0 < ((![![0, 1, 1], ![1, 0, 1], ![1, 1, 0]]
        : Fin 3 → Fin 3 → ℝ) i j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two]
  have hpot : groundedPotential
        ![![0, 1, 1], ![1, 0, 1], ![1, 1, 0]] hwA hw0A hposA 0
        ![0, 1, 1]
      = ![0, 1, 1] := by
    refine groundedPotential_unique _ hwA hw0A hposA 0 ![0, 1, 1]
      (groundedPotential _ hwA hw0A hposA 0 ![0, 1, 1]) _ ?_ ?_ ?_ ?_
    · exact groundedPotential_at_ground _ _ _ _ _ _
    · simp [Matrix.cons_val_zero]
    · intro i hi
      exact laplacianOp_groundedPotential _ _ _ _ _ _ hi
    · intro i hi
      have h3 : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
      rcases h3 i with rfl | rfl | rfl
      · exact absurd rfl hi
      · rw [laplacianOp_apply, Fin.sum_univ_three]
        norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two]
      · rw [laplacianOp_apply, Fin.sum_univ_three]
        norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two]
  exact hpot

/-- **GA-2: the three-site floor is unique at the centre.**
(GA-1(ii) at the exhibit — the positive half of the Fin-3
dichotomy, Zero's three-site seeing in its surviving
regime.) -/
theorem gravAtomSeat_floor_unique {m : Fin 3}
    (hm : IsFallMin (atomWell gravAtomSeat) m) : m = 0 :=
  atomWell_unique_floor gravAtomSeat hm

/-- **GA-2: the fall energy at the three-site well is
exactly `-1`.** `½·(∑ ψ·Lψ) - ∑_{i ≠ 0} ρᵢψᵢ = ½·2 - 2`
at `ψ = ![0, 1, 1]`. -/
theorem gravAtomSeat_fallEnergy :
    fallEnergy gravAtomSeatW 0 ![0, 1, 1] (atomWell gravAtomSeat)
      = -1 := by
  classical
  rw [gravAtomSeat_well]
  unfold fallEnergy
  rw [Fin.sum_univ_three]
  simp only [laplacianOp_apply, Fin.sum_univ_three, gravAtomSeatW,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two]
  rw [show Finset.univ.erase (0 : Fin 3) = {1, 2} from by decide,
    Finset.sum_pair (by decide : (1 : Fin 3) ≠ 2)]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two]

/-- **GA-2: the flat half of the Fin-3 dichotomy.** With the
vanishing source `ρ = ![0, 0, 0]` on the same seat, the
grounded potential is `![0, 0, 0]` and EVERY site attains
the floor — the flat floor triple, the counter-form of
Zero's three-site seeing, exhibited on Fin 3. (FF-5b at the
seat; FF-6 remains the Fin 2 standing exhibit.) -/
theorem gravAtomSeat_flat_floor :
    groundedPotential gravAtomSeatW gravAtomSeat.hw
        gravAtomSeat.hw0 gravAtomSeat.hpos 0 ![0, 0, 0]
        = ![0, 0, 0]
      ∧ ∀ m, IsFallMin (groundedPotential gravAtomSeatW
          gravAtomSeat.hw gravAtomSeat.hw0 gravAtomSeat.hpos 0
          ![0, 0, 0]) m := by
  classical
  have h0 : groundedPotential gravAtomSeatW gravAtomSeat.hw
      gravAtomSeat.hw0 gravAtomSeat.hpos 0 ![0, 0, 0] = 0 :=
    atomWell_eq_zero_of_source_vanishes _ _ _ _ 0 ![0, 0, 0] (by
      intro i hi
      fin_cases i
      · simp at hi
      · simp [Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two]
      · simp [Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two])
  constructor
  · rw [h0]
    funext i
    fin_cases i <;> simp [Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two]
  · intro m j _
    rw [h0]
    simp

/-! ## GA-3 — the spectrum of the atom seat -/

/-- **GA-3(i) — the atom's gap is strictly positive** on a
general atom seat. Route: the Fiedler minimizer exists
(BridgeCompletion) and is an eigenvector at `fiedler w`;
were the gap `0`, its energy would be `0`, forcing it
constant on the complete seat (`eq_const_of_energy_eq_zero`)
— against its mean-zero unit-norm admissibility. The two
distinct sites the attainment needs are the centre and the
regime witness, which the datum carries. (A finite graph
gap, not a continuum gap, not a measured number — header
fence.) -/
theorem atomGap_pos (A : GravAtom V) : 0 < atomGap A := by
  classical
  obtain ⟨i, hi, -⟩ := A.hregime
  obtain ⟨F, hFmem, hFeig⟩ :=
    laplacianOp_fiedler_minimizer A.w A.hw A.hw0 hi
  have hnn : 0 ≤ fiedler A.w := fiedler_nonneg A.w A.hw A.hw0
  suffices h : fiedler A.w ≠ 0 from lt_of_le_of_ne hnn (Ne.symm h)
  intro h0
  have hE : energy A.w F = 0 := by
    rw [energy_of_eigenvector A.w F (fiedler A.w) hFeig, h0,
      hFmem.2]
    norm_num
  rw [energy_def] at hE
  have hconst := eq_const_of_energy_eq_zero A.w A.hw A.hw0
    A.hpos F hE
  have hFb : F A.b = 0 := by
    have hsum : ∑ j, F j = 0 := hFmem.1
    rw [Finset.sum_congr rfl (fun j _ => hconst j A.b)] at hsum
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
    rcases mul_eq_zero.mp hsum with h | h
    · exfalso
      have hc : Fintype.card V = 0 := by exact_mod_cast h
      have hpos : 0 < Fintype.card V :=
        Fintype.card_pos_iff.mpr ⟨A.b⟩
      omega
    · exact h
  have h2 := hFmem.2
  have hsq : ∑ j, F j ^ 2 = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [hconst j A.b, hFb]
    norm_num
  rw [hsq] at h2
  exact one_ne_zero h2.symm

/-- **GA-3(ii), the Rayleigh identity at the headline seat.**
For the complete unit weights on `Fin 3`, the energy of any
potential is `3·∑ Fᵢ² - (∑ Fᵢ)²` — a finite sum manipulation,
hand-verified at scoping. On a mean-zero potential the second
term dies and the energy is exactly `3·∑ Fᵢ²`. -/
theorem gravAtomSeat_energy_identity (F : Fin 3 → ℝ) :
    energy gravAtomSeatW F
      = 3 * (∑ i, F i ^ 2) - (∑ i, F i) ^ 2 := by
  simp only [energy_def, laplacianOp_apply, Fin.sum_univ_three,
    gravAtomSeatW, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.tail_cons, Matrix.cons_val_two]
  ring

/-- **GA-3(ii) — the headline seat's gap is exactly 3.**
Upper bound: `![1, -1, 0]` is a mean-zero eigenvector at `3`
(`fiedler_le_of_eigenvector`). Lower bound: every admissible
energy equals `3` by the Rayleigh identity, so the infimum
defining `fiedler` is `3` (`le_csInf` + attainment of the
value by the admissible set's elements). -/
theorem gravAtomSeat_gap : atomGap gravAtomSeat = 3 := by
  classical
  have hgap : atomGap gravAtomSeat = fiedler gravAtomSeatW := rfl
  rw [hgap, fiedler_def]
  apply le_antisymm
  · have heig : ∀ i : Fin 3,
        laplacianOp gravAtomSeatW ![1, -1, 0] i
          = 3 * ![1, -1, 0] i := by
      intro i
      fin_cases i <;>
        norm_num [laplacianOp_apply, Fin.sum_univ_three,
          gravAtomSeatW, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_two]
    exact fiedler_le_of_eigenvector gravAtomSeatW gravAtomSeat.hw
      gravAtomSeat.hw0 ![1, -1, 0] 3
      (by rw [Fin.sum_univ_three]
          norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_two])
      (by intro hcon
          have h0 := congrFun hcon 0
          simp [Matrix.cons_val_zero] at h0)
      heig
  · apply le_csInf
      (fiedlerSet_nonempty_of_exists_ne gravAtomSeatW
        (by decide : (0 : Fin 3) ≠ 1))
    rintro x ⟨F, hF0, hF1, rfl⟩
    rw [← energy_def]
    have hE : energy gravAtomSeatW F = 3 := by
      rw [gravAtomSeat_energy_identity, hF0, hF1]
      norm_num
    exact hE.ge

/-- **GA-3(iii) — degeneracy of the first shell.** Both
`![1, -1, 0]` and `![1, 1, -2]` are eigenvectors at `3`, and
they are linearly independent: the first excited level's
eigenspace is (at least) the whole mean-zero plane,
degenerate, carried by the seat's `S₃` symmetry. This is
the one place the finite ladder genuinely rhymes with the
continuum atom — shell degeneracy from symmetry — stated in
exactly that narrow form (see GA-4 for what does NOT
rhyme). -/
theorem gravAtomSeat_degeneracy :
    (∀ i, laplacianOp gravAtomSeatW ![1, -1, 0] i
        = 3 * ![1, -1, 0] i)
    ∧ (∀ i, laplacianOp gravAtomSeatW ![1, 1, -2] i
        = 3 * ![1, 1, -2] i)
    ∧ LinearIndependent ℝ
        (![![1, -1, 0], ![1, 1, -2]] : Fin 2 → Fin 3 → ℝ) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i <;>
      norm_num [laplacianOp_apply, Fin.sum_univ_three,
        gravAtomSeatW, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_two]
  · intro i
    fin_cases i <;>
      norm_num [laplacianOp_apply, Fin.sum_univ_three,
        gravAtomSeatW, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_two]
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_two] at hg
    have hsite2 : g 0 * (0 : ℝ) + g 1 * (-2) = 0 := by
      have h := congrFun hg 2
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
        Matrix.cons_val_two, Pi.zero_apply] at h
      linarith
    have hg1 : g 1 = 0 := by linarith
    have hsite1 : g 0 * (-1) + g 1 * (1 : ℝ) = 0 := by
      have h := congrFun hg 1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
        Matrix.cons_val_two, Pi.zero_apply] at h
      linarith
    have hg0 : g 0 = 0 := by linarith
    intro k
    fin_cases k
    · exact hg0
    · exact hg1

/-! ## GA-4 — the rhyme verdict

**K-GA-RHYME FIRES on the strong form**, banked here as
exact exhibits. The strong form — "the finite ladder mirrors
the continuum ladder's shape", read as spacing ratios — is
FALSE: Form 1's ladder has its first two excitation energies
(measured from the ground) in ratio `32/27`; the headline
seat's ladder is `{0, 3, 3}` — there is no second distinct
rung at all — and the path seat's ladder is `{0, 1, 3}`, gap
ratio `2 ≠ 32/27`. What survives of the rhyme is exactly:
the ground level is unique (GA-4(i)), the first excitation
is strictly positive (GA-3(i)), and the first shell is
degenerate by symmetry (GA-3(iii)). Nothing more may be
claimed anywhere. -/

/-- **GA-4(i) — the ground level is unique.** On any atom
seat, a potential in the kernel of the seat Laplacian is
constant: the `0`-eigenspace is exactly the constants.
(Energy vanishes, then `eq_const_of_energy_eq_zero`.) -/
theorem gravAtom_kernel_eq_const (A : GravAtom V)
    (F : V → ℝ) (hF : ∀ i, laplacianOp A.w F i = 0) :
    ∀ i j, F i = F j := by
  apply eq_const_of_energy_eq_zero A.w A.hw A.hw0 A.hpos F
  apply Finset.sum_eq_zero
  intro i _
  rw [hF i, mul_zero]

/-- **GA-4(ii) — the continuum ratio is `32/27`.** For
positive parameters, Form 1's ladder has
`(E₃ - E₁) / (E₂ - E₁) = ((1 - 1/9)·E₁) / ((1 - 1/4)·E₁)
= (8/9)/(3/4) = 32/27`, where the levels are
`gravLevel · · · n = -E₁/n²` and `E₁ > 0` is the ground
binding scale. Pure algebra over the symbolic parameters —
the one continuum-side computation in the pin, and it is
about the STATED ladder, not about any operator. -/
theorem gravLevel_excitation_ratio (G hbar m_e m_p : ℝ)
    (hG : 0 < G) (hh : 0 < hbar) (he : 0 < m_e) (hp : 0 < m_p) :
    (gravLevel G hbar m_e m_p 3 - gravLevel G hbar m_e m_p 1)
      / (gravLevel G hbar m_e m_p 2 - gravLevel G hbar m_e m_p 1)
      = 32 / 27 := by
  have hE : 0 < gravGroundEnergy G hbar m_e m_p := by
    unfold gravGroundEnergy gravReducedMass gravCoupling
    positivity
  set E := gravGroundEnergy G hbar m_e m_p with hEdef
  have hE0 : E ≠ 0 := ne_of_gt hE
  have key : ∀ n : ℕ, gravLevel G hbar m_e m_p n
      = -E / (n : ℝ) ^ 2 := fun n => rfl
  rw [key 3, key 1, key 2]
  push_cast
  have hnum : (-E / (3 : ℝ) ^ 2 - -E / (1 : ℝ) ^ 2)
      = 8 / 9 * E := by ring
  have hden : (-E / (2 : ℝ) ^ 2 - -E / (1 : ℝ) ^ 2)
      = 3 / 4 * E := by ring
  rw [hnum, hden, mul_div_mul_right _ _ hE0]
  norm_num

/-- **GA-4(iii) — the headline ladder has no second distinct
rung.** Every eigenvalue of the headline seat's Laplacian is
`0` or `3`: the ladder is `{0, 3, 3}`. Route: an eigenvector
at `μ ≠ 0` is mean-zero (the total current vanishes), and
then the Rayleigh identity forces `μ·∑ Fᵢ² = 3·∑ Fᵢ²` with
`∑ Fᵢ² > 0`. Together with GA-3(ii)/(iii) (both values
occur, `3` with a two-dimensional eigenspace), the ladder
is exactly `{0, 3, 3}` — against the continuum's infinite
ladder of distinct rungs. **This is K-GA-RHYME's exhibit
on the headline seat.** -/
theorem gravAtomSeat_eigenvalue_mem (F : Fin 3 → ℝ) (μ : ℝ)
    (hF : F ≠ 0) (heig : ∀ i, laplacianOp gravAtomSeatW F i
      = μ * F i) :
    μ = 0 ∨ μ = 3 := by
  classical
  by_cases hμ : μ = 0
  · exact Or.inl hμ
  · right
    have hsum : ∑ i, F i = 0 := by
      have h := sum_laplacianOp_eq_zero gravAtomSeatW
        gravAtomSeat.hw F
      rw [Finset.sum_congr rfl (fun i _ => heig i),
        ← Finset.mul_sum] at h
      exact (mul_eq_zero.mp h).resolve_left hμ
    have hE := energy_of_eigenvector gravAtomSeatW F μ heig
    rw [gravAtomSeat_energy_identity, hsum] at hE
    have hsq : (0 : ℝ) < ∑ i, F i ^ 2 :=
      sum_sq_pos_of_fun_ne_zero hF
    have : μ * ∑ i, F i ^ 2 = 3 * ∑ i, F i ^ 2 := by linarith
    exact (mul_right_cancel₀ (ne_of_gt hsq) this)

/-- The path seat weights on `Fin 3`: sites `0-1-2` in a
line, unit weights on the two edges. NOT complete — carried
here as bare weights (no `GravAtom` datum: completeness is
the atom's regime), purely as the rhyme verdict's second
exhibit. -/
def gravPathSeatW : Fin 3 → Fin 3 → ℝ :=
  ![![0, 1, 0], ![1, 0, 1], ![0, 1, 0]]

/-- **GA-4(iv) — the path seat's ladder is `{0, 1, 3}`, and
its gap ratio is `2 ≠ 32/27`.** Both excitations occur
(exhibited eigenvectors), and no other eigenvalue exists:
an eigenvector at `μ ≠ 0` is mean-zero; the site equations
then give `(1 - μ)·(F 2 - F 0) = 0`; at `μ = 1` it is the
first rung, and otherwise `F 2 = F 0` forces `F 1 = -2·F 0`
and `μ = 3` off the site-0 equation. **K-GA-RHYME's second
exhibit**: even where a second distinct rung exists, the
ratio is `2`, not the continuum's `32/27`. -/
theorem gravPathSeat_ladder :
    (∀ i, laplacianOp gravPathSeatW ![1, 0, -1] i
        = 1 * ![1, 0, -1] i)
    ∧ (∀ i, laplacianOp gravPathSeatW ![1, -2, 1] i
        = 3 * ![1, -2, 1] i)
    ∧ (∀ (F : Fin 3 → ℝ) (μ : ℝ), F ≠ 0 →
        (∀ i, laplacianOp gravPathSeatW F i = μ * F i) →
        μ = 0 ∨ μ = 1 ∨ μ = 3)
    ∧ (3 : ℝ) / 1 ≠ 32 / 27 := by
  classical
  have hwP : ∀ i j : Fin 3, gravPathSeatW i j
      = gravPathSeatW j i := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [gravPathSeatW, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_two]
  refine ⟨?_, ?_, ?_, by norm_num⟩
  · intro i
    fin_cases i <;>
      norm_num [laplacianOp_apply, Fin.sum_univ_three,
        gravPathSeatW, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_two]
  · intro i
    fin_cases i <;>
      norm_num [laplacianOp_apply, Fin.sum_univ_three,
        gravPathSeatW, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_two]
  · intro F μ hF heig
    by_cases hμ : μ = 0
    · exact Or.inl hμ
    · have hsum : ∑ i, F i = 0 := by
        have h := sum_laplacianOp_eq_zero gravPathSeatW hwP F
        rw [Finset.sum_congr rfl (fun i _ => heig i),
          ← Finset.mul_sum] at h
        exact (mul_eq_zero.mp h).resolve_left hμ
      rw [Fin.sum_univ_three] at hsum
      have h0 := heig 0
      have h2 := heig 2
      simp only [laplacianOp_apply, Fin.sum_univ_three,
        gravPathSeatW, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_two, zero_mul, one_mul,
        mul_zero, add_zero, zero_add] at h0 h2
      -- h0 : F 0 - F 1 = μ * F 0 ; h2 : F 2 - F 1 = μ * F 2
      -- (after norm_num-free expansion; coefficients are 0/1)
      have hF1 : F 1 = (1 - μ) * F 0 := by linarith
      have hkey : (1 - μ) * (F 2 - F 0) = 0 := by linarith
      rcases mul_eq_zero.mp hkey with h1μ | hF20
      · right; left
        linarith
      · right; right
        have hF2 : F 2 = F 0 := by linarith
        have hF1' : F 1 = -2 * F 0 := by linarith
        by_cases hF0 : F 0 = 0
        · exfalso
          apply hF
          funext i
          fin_cases i <;> simp [hF0, hF1', hF2]
        · have : μ * F 0 = 3 * F 0 := by linarith
          exact mul_right_cancel₀ hF0 this

/-! ## GA-5 — the stability weld (Form 3's residue)

Form 3 (the conditional weld) collapsed at scoping: its
clauses (a)/(b) are GA-1 restated, and (c) is GA-3. The one
residue neither parent module contains is the quantitative
stability of the seating, banked here: FF-7's energy
identity composed with the Bridge variational gap bound.
The own-mass seating is not merely unique; its energy
penalty for displacement is exactly half the displacement's
energy, and — for mean-zero displacements — at least half
the atom gap times the squared displacement.

**Disclosure on the norm form (scope §3.2, GA-5):** the
gap bound is banked in ADMISSIBLE form. A general grounded
displacement `ψ - atomWell` vanishes at the centre but is
not mean-zero, and `fiedler_le_energy` speaks only about
mean-zero potentials; the unrestricted
`(1/2)·atomGap·‖ψ - atomWell‖²` inequality therefore does
NOT follow from the Fiedler value, and this brick does not
state it. What is stated: the identity for every grounded
candidate, and the gap bound for mean-zero displacements. -/

/-- **GA-5(i) — the stability identity.** For any grounded
candidate `ψ`,
`fallEnergy ψ - fallEnergy (atomWell)
  = (1/2)·energy (ψ - atomWell)`.
FF-7a's identity, composed here from `energy_add_smul` and
the Poisson pairing (the cross term is the erased source
pairing, since the well solves the Poisson equation
off-ground and the displacement vanishes at the centre). -/
theorem atomWell_energy_identity (A : GravAtom V) (ψ : V → ℝ)
    (hψb : ψ A.b = 0) :
    fallEnergy A.w A.b A.ρ ψ - fallEnergy A.w A.b A.ρ (atomWell A)
      = (1 / 2) * energy A.w (ψ - atomWell A) := by
  classical
  have hub : (ψ - atomWell A) A.b = 0 := by
    rw [Pi.sub_apply, hψb, (atomWell_floor_value A).2, sub_self]
  have hψ : atomWell A + (ψ - atomWell A) = ψ := add_sub_cancel _ _
  have hexp : energy A.w ψ = energy A.w (atomWell A)
      + 2 * bilin A.w (atomWell A) (ψ - atomWell A)
      + energy A.w (ψ - atomWell A) := by
    have h := energy_add_smul A.w A.hw (atomWell A)
      (ψ - atomWell A) 1
    rw [one_smul, hψ] at h
    linarith
  have hpair : bilin A.w (atomWell A) (ψ - atomWell A)
      = ∑ i ∈ Finset.univ.erase A.b, A.ρ i * (ψ - atomWell A) i := by
    rw [bilin_def]
    have h := Finset.sum_erase_add Finset.univ
      (fun i => (ψ - atomWell A) i
        * laplacianOp A.w (atomWell A) i) (Finset.mem_univ A.b)
    rw [hub, zero_mul, add_zero] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≠ A.b := (Finset.mem_erase.mp hi).1
    have hL : laplacianOp A.w (atomWell A) i = A.ρ i :=
      laplacianOp_groundedPotential A.w A.hw A.hw0 A.hpos
        A.b A.ρ hi'
    rw [hL, mul_comm]
  have hpairψ : ∑ i ∈ Finset.univ.erase A.b, A.ρ i * ψ i
      = ∑ i ∈ Finset.univ.erase A.b, A.ρ i * atomWell A i
        + ∑ i ∈ Finset.univ.erase A.b, A.ρ i
            * (ψ - atomWell A) i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hψi : ψ i = atomWell A i + (ψ - atomWell A) i := by
      rw [Pi.sub_apply]
      ring
    rw [hψi, Pi.sub_apply]
    ring
  rw [hpair] at hexp
  simp only [energy_def] at hexp
  unfold fallEnergy
  simp only [energy_def]
  linarith

/-- **GA-5(ii) — the gap bound, admissible form.** For a
grounded candidate whose displacement from the well is
mean-zero, the energy penalty is at least
`(1/2)·atomGap·∑ (displacement)²`. (Normalization of the
displacement to the admissible set, then
`fiedler_le_energy` — the route of
`fiedler_le_of_eigenvector`'s proof.) -/
theorem atomWell_energy_ge_gap (A : GravAtom V) (ψ : V → ℝ)
    (hψb : ψ A.b = 0)
    (hmean : ∑ i, (ψ - atomWell A) i = 0) :
    (1 / 2) * atomGap A * (∑ i, (ψ - atomWell A) i ^ 2)
      ≤ fallEnergy A.w A.b A.ρ ψ
        - fallEnergy A.w A.b A.ρ (atomWell A) := by
  classical
  rw [atomWell_energy_identity A ψ hψb]
  suffices h : atomGap A * (∑ i, (ψ - atomWell A) i ^ 2)
      ≤ energy A.w (ψ - atomWell A) by linarith
  by_cases hu : (∑ i, (ψ - atomWell A) i ^ 2) = 0
  · rw [hu, mul_zero]
    exact energy_nonneg A.w A.hw A.hw0 _
  · have hspos : (0 : ℝ) < ∑ i, (ψ - atomWell A) i ^ 2 :=
      lt_of_le_of_ne
        (Finset.sum_nonneg fun i _ => sq_nonneg _) (Ne.symm hu)
    set s : ℝ := ∑ i, (ψ - atomWell A) i ^ 2 with hs
    set c : ℝ := (Real.sqrt s)⁻¹ with hc
    have hc2 : c ^ 2 = s⁻¹ := by
      rw [hc, inv_pow, Real.sq_sqrt hspos.le]
    have h1 : (∑ i, (c • (ψ - atomWell A)) i) = 0 := by
      simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum,
        hmean, mul_zero]
    have h2 : (∑ i, (c • (ψ - atomWell A)) i ^ 2) = 1 := by
      have hterm : ∀ i : V, (c • (ψ - atomWell A)) i ^ 2
          = c ^ 2 * ((ψ - atomWell A) i ^ 2) := fun i => by
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rw [Finset.sum_congr rfl (fun i _ => hterm i),
        ← Finset.mul_sum, hc2, inv_mul_cancel₀ (ne_of_gt hspos)]
    have h3 : fiedler A.w ≤ energy A.w (c • (ψ - atomWell A)) :=
      fiedler_le_energy A.w A.hw A.hw0 _ h1 h2
    rw [energy_smul, hc2] at h3
    calc atomGap A * s = fiedler A.w * s := rfl
      _ ≤ (s⁻¹ * energy A.w (ψ - atomWell A)) * s :=
          mul_le_mul_of_nonneg_right h3 hspos.le
      _ = energy A.w (ψ - atomWell A) := by
          rw [mul_comm (s⁻¹) (energy A.w (ψ - atomWell A)),
            mul_assoc, inv_mul_cancel₀ (ne_of_gt hspos), mul_one]

/-- **GA-5 — the stability weld, assembled.** The own-mass
seating is quadratically stable: exact energy identity for
every grounded candidate, and the gap-strengthened bound
for mean-zero displacements (admissible form — see the
section disclosure). -/
theorem atomWell_stability (A : GravAtom V) (ψ : V → ℝ)
    (hψb : ψ A.b = 0)
    (hmean : ∑ i, (ψ - atomWell A) i = 0) :
    fallEnergy A.w A.b A.ρ ψ - fallEnergy A.w A.b A.ρ (atomWell A)
      = (1 / 2) * energy A.w (ψ - atomWell A)
    ∧ (1 / 2) * atomGap A * (∑ i, (ψ - atomWell A) i ^ 2)
      ≤ fallEnergy A.w A.b A.ρ ψ
        - fallEnergy A.w A.b A.ρ (atomWell A) :=
  ⟨atomWell_energy_identity A ψ hψb,
   atomWell_energy_ge_gap A ψ hψb hmean⟩

end ThetLogos
