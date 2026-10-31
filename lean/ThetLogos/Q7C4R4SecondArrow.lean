import Mathlib.Tactic
import ThetLogos.Q7C4R4Trifecta
import ThetLogos.Q7C4R4LinkC4
import ThetLogos.Q7C4R4Dynamics
import ThetLogos.Q7C4R4EnergySplit

namespace ThetLogos

open TensorProduct

/-!
# ThetLogos.Q7C4R4SecondArrow — T-C4-2: the W2 (grading-form) test
of the Q7C4R4 trifecta's Second leg (C4 to Second Law), on the
composite

**Status: TEST EXECUTED — W2 PROVED at the instantiated seat in
the extracted form below. K-T-C4-2 does NOT fire. NO CLAIM.
Dials 0/4. No measured number.** Governing pack:
`routeb-general-scratch/pack-t-c4-2.md`; governing scoping:
`scoping-q7c4r4-trifecta-2026-10-30.md` (section 2.2(ii) + section
4); registration: `ThetLogos.Q7C4R4Trifecta` (Q7CR-T0), which
stays untouched as the record. Gates consumed, all landed:
Q7CR-3 (`Q7C4R4Charge`: `sectorComp` / `sectorC4` / `chargeC4`),
Q7CR-6b (`Q7C4R4LinkC4`: the graded correspondence
`mem_sectorComp_tmul`, `chargeComp_tmul_fourierC4`), Q7CR-5
(`Q7C4R4Dynamics`: `dynHeat` / `dynGen`, `dynGibbs`), Q7CR-2
(`Q7C4R4Spectrum`: `eigComp` / `basisComp` / `compIndex`), and
T-Q7-2 (`Q7C4R4EnergySplit`: `compEnergy_prod_weighted`, the
factor energy expectations). T-ENT is NOT consumed: no entropy
language is used or needed.

## The registered target, verbatim (memo section 2.2(ii))

> **(ii) FINITE-TESTABLE — weakened form W2, the arrow relocated
> (brick T-C4-2).** The form T0 registers as `LegSecondArrow`:
> the clock does not generate the flow; it **grades the step**.
> A stated step on the composite (heat/ternary-step form), graded
> by the C4 characters, has nonnegative defect on every character
> sector — the defect in the corpus's owned form,
> `ViscousLine.traceDefect` (`traceDefect_nonneg`, T1 at the
> diagonal seat: the step loses exactly
> `sum w_i (1 - e^{-2t lam_i}) >= 0`). Irreversibility lives
> where the corpus has always kept it — in steps, not flows.
> Kill: one character sector with negative defect at the
> instantiated seat kills W2's composite form; the leg then
> stands on W1 alone, or reverts to pure definition (W3),
> whichever the record shows, labeled.

The registered Prop (landed in `Q7C4R4Trifecta`, not restated or
narrowed here):

```
def LegSecondArrow {N : ℕ} (lam : Fin 4 → Fin N → ℝ) (t : ℝ)
    (w : Fin 4 → Fin N → ℝ) : Prop :=
  ∀ j : Fin 4, 0 ≤ traceDefect (lam j) t (w j)
```

Armed kill **K-T-C4-2:** a negative-defect character sector at
the instantiated seat kills W2 on the composite.

## The obstruction, faced on the face

Q7CR-3 proved the charge sectors are NOT invariant under the
composite Dirac square: `dirac_sq_v₀_not_mem_sectorComp_zero`
and `criterion_fails` (landed, `Q7C4R4Charge`). The generator
`dynGen = diracInst ^ 2` (Q7CR-5's CHOSEN generator) therefore
has NO restriction to a sector, and no eigenvalue of `dynGen`
can honestly be called a sector eigenvalue. Any extraction that
pretended otherwise would be a substituted claim.

## The sense of "graded by the C4 characters" used here

The sector data is the step's **sector-compression (pairing
diagonal) data**, the only sectorwise spectral datum the landed
objects support, in three proved pieces:

- For each character `j : Fin 4`, the C4 factor's character line
  is the real line through the normalized character vector
  `(1/2) • fourierC4 j`. By Q7CR-3, `fourierC4 j` lies in
  `sectorC4 j` (`fourierC4_mem_sectorC4`); by Q7CR-6b's graded
  correspondence (`mem_sectorComp_tmul`), a pure tensor lies in
  the composite sector `sectorComp j` exactly when its C4 factor
  lies in `sectorC4 j` (nonzero spectators). The sector vectors
  of section 2 — spectator eigenlines tensored with the
  character line — are PROVED to lie in `sectorComp j`
  (`sectorVec_mem_sectorComp`).
- The rate of a sector vector is the CHOSEN generator's
  expectation for the registered composite pairing
  (`compositePair`), i.e. the diagonal of the compression of
  `dynGen` to the sector line, read factorwise through
  T-Q7-2's weighted splitting (`sectorVec_dynGen_pairing`):
  the Q7 spectator contributes its landed eigenvalue `s₇c a`,
  the R4 spectator its landed eigenvalue `s_R m`, and the C4
  character line contributes `c4SectorRate j`, the factor energy
  expectation of `factorC4.D ^ 2` on the normalized character
  vector. That C4 contribution is character-independent:
  `c4SectorRate j = 5 / 64` for every `j`
  (`c4SectorRate_eq`), because every character value has unit
  modulus (`fourierC4_normSq`), so the compression of the
  site-diagonal `D₄²` to any character line is the site mean of
  `d₄²` — equivalently the mean of Q7CR-2's C4 factor spectrum
  `s₄c` (`c4SectorRate_eq_mean`). The grading is thus genuinely
  by the characters (the sector, the line, and the membership
  are the characters'), while the compressed rate happens to be
  constant across characters; that constancy is a proved fact
  about this seat, stated here, not an assumption.
- The weights are a NAMED state: the uniform state
  `sectorUniform` on the sector's spectator seat (56 spectator
  indices: 14 Q7 realified times 4 R4 sites), the beta = 0
  (maximally mixed) state of the sector seat. It is a state:
  nonnegative and summing to 1 (`sectorUniform_sum`).

The seat is `N = 56`: spectator indices reindexed to `Fin 56`
by the landed-style product equiv `specEquiv` (section 3). The
per-sector rate and weight families `lamFin` / `wFin` are the
extractions; every tie between them and the landed objects
above is a proved theorem in this module, not prose.

## Verdict

**PROVED.** For every step parameter `t >= 0`,
`LegSecondArrow lamFin t wFin` holds at the instantiated seat
(`w2_legSecondArrow`): each sector's defect is
`traceDefect (lamFin j) t (wFin j) >= 0` by the landed
`traceDefect_nonneg`, the sector data satisfying its hypotheses
by the proved ties (rates nonnegative: `lamSecond_nonneg`;
weights a state: `sectorUniform_sum`). The sector defect's
closed form is computed in `sector_traceDefect_eq`. **No
character sector has negative defect, so K-T-C4-2 does NOT
fire.**

**Leg status line, stated exactly:** W2 (grading form) STANDS
PROVED at the composite seat in the sector-compression sense
stated above; the Second leg's resulting status is: strong form
REFUTED-AS-STATED (T0, unchanged), W1 (section form) DEAD
(K-T-C4-1 fired, T-C4-1, unchanged), W2 PROVED (this brick), and
the W3 floor (pure definition) is NOT engaged, since W2 stands.
The trifecta assignment itself is Jeff's registered DATA; this
brick tests one leg's stated consequence only, and no outcome
here promotes the assignment.

## Standing caveat for this line

Bounded-commutator vacuity: in finite dimension every operator
is bounded and every commutator criterion of that species is
vacuous; nothing in this brick rests on one, and none is
claimed. The generator is Q7CR-5's CHOSEN `dynGen = diracInst²`,
labeled CHOSEN there; this brick consumes it as landed and
derives no dynamics. NO CLAIM; dials 0/4; no measured number.
-/

/-! ## §0. The sector seat: spectator indices, sector vectors,
the C4 sector rate, the rate family, the named state -/

/-- The spectator index type of a sector seat: the Q7 factor's
realified indices (`Fin 7 × Fin 2`, 14 of them) times the R4
factor's sites (`Fin 4`), 56 in all. The C4 factor is not a
spectator: it carries the grading, through its character line.
Tier T2 (definition). -/
abbrev specIndex : Type := (Fin 7 × Fin 2) × Fin 4

/-- The sector vector at character `j`, Q7 spectator index `a`
and R4 site `m`: the product state of the Q7 real site basis
vector `basisC 7 a`, the normalized C4 character vector
`(1/2) • fourierC4 j`, and the R4 site basis vector at `m`.
Its C4 factor is the `j`-th character line, so by Q7CR-6b it
lies in composite sector `j` (proved in section 2). Tier T2
(definition). -/
noncomputable def sectorVec (j : Fin 4) (a : Fin 7 × Fin 2)
    (m : Fin 4) : q7c4r4Composite :=
  prodState (basisC 7 a) ((1 / 2 : ℝ) • fourierC4 j)
    ((Pi.basisFun ℝ (Fin 4)) m)

/-- **The C4 sector rate**: the factor energy expectation of
the instantiated C4 factor square on the normalized character
vector — the diagonal of the compression of `factorC4.D ^ 2`
to the `j`-th character line, in T-Q7-2's owned form
`factorEnergyC`. Proved character-independent (`= 5 / 64`) in
section 1. Tier T2 (definition). -/
noncomputable def c4SectorRate (j : Fin 4) : ℝ :=
  factorEnergyC factorC4 ((1 / 2 : ℝ) • fourierC4 j)

/-- **The sector rate family** on the spectator seat: at
character sector `j` and spectator index `s = (a, m)`, the
rate is the sum of the three factor contributions — the Q7
spectator's landed eigenvalue `s₇c a`, the C4 character line's
compressed rate `c4SectorRate j`, and the R4 spectator's landed
eigenvalue `s_R m`. Proved to be the generator's pairing
diagonal on the sector vectors in section 2
(`sectorVec_dynGen_pairing`). Tier T2 (definition). -/
noncomputable def lamSecond (j : Fin 4) (s : specIndex) : ℝ :=
  s₇c s.1 + c4SectorRate j + s_R s.2

/-- **The named state**: the uniform state on the sector's
spectator seat, `(56 : ℝ)⁻¹` at every one of the 56 spectator
indices — the beta = 0 (maximally mixed) state of the seat.
Tier T2 (definition). -/
noncomputable def sectorUniform : Fin 56 → ℝ := fun _ => (56 : ℝ)⁻¹

/-- The reindexing of the spectator seat to `Fin 56`: the
product equiv `finProdFinEquiv` applied factorwise
(`(Fin 7 × Fin 2) ≃ Fin 14`, then `Fin 14 × Fin 4 ≃ Fin 56`).
Tier T2 (definition). -/
noncomputable def specEquiv : specIndex ≃ Fin 56 :=
  ((finProdFinEquiv (m := 7) (n := 2)).prodCongr
    (Equiv.refl (Fin 4))).trans (finProdFinEquiv (m := 14) (n := 4))

/-- **The extracted rate family at the registered seat**: the
sector rates of `lamSecond`, reindexed from the spectator seat
to `Fin 56`. This is the `lam` that instantiates
`LegSecondArrow`. Tier T2 (definition). -/
noncomputable def lamFin (j : Fin 4) : Fin 56 → ℝ :=
  fun i => lamSecond j (specEquiv.symm i)

/-- **The extracted weight family at the registered seat**:
the uniform state `sectorUniform` on every sector. This is
the `w` that instantiates `LegSecondArrow`. Tier T2
(definition). -/
noncomputable def wFin (_j : Fin 4) : Fin 56 → ℝ := sectorUniform

/-! ## §1. The C4 factor computations: the character line's
self-pairing and compressed rate -/

/-- The registered factor pairing in realified coordinates, at
one coordinate: `realBasisEquiv 4 z (k, b)` is the real part of
`z k` for `b = 0` and the imaginary part for `b = 1` (the same
coordinate read `Q7C4R4Dynamics` lands in
`factorPair_eq_sum_coords`). Tier T1. -/
theorem coord_apply (z : Fin 4 → ℂ) (k : Fin 4) (b : Fin 2) :
    realBasisEquiv 4 z (k, b)
      = if b = 0 then (z k).re else (z k).im := by
  fin_cases b
  · have h : (if (0 : Fin 2) = 0 then (z k).re else (z k).im)
        = (z k).re := if_pos rfl
    exact h
  · have h : (if (1 : Fin 2) = 0 then (z k).re else (z k).im)
        = (z k).im := if_neg (by decide)
    exact h

/-- The real coordinate of `realBasisEquiv`. Tier T1. -/
theorem coord_zero (z : Fin 4 → ℂ) (k : Fin 4) :
    realBasisEquiv 4 z (k, 0) = (z k).re := by
  show (if (0 : Fin 2) = 0 then (z k).re else (z k).im) = (z k).re
  rw [if_pos rfl]

/-- The imaginary coordinate of `realBasisEquiv`. Tier T1. -/
theorem coord_one (z : Fin 4 → ℂ) (k : Fin 4) :
    realBasisEquiv 4 z (k, 1) = (z k).im := by
  show (if (1 : Fin 2) = 0 then (z k).re else (z k).im) = (z k).im
  rw [if_neg (by decide)]

/-- The factor pairing of a vector with itself is the sum of
its sites' norm squares. Tier T1. -/
theorem factorPair_self_eq (y : Fin 4 → ℂ) :
    factorPair 4 y y = ∑ k, Complex.normSq (y k) := by
  rw [factorPair_eq_sum_coords, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  rw [Fin.sum_univ_two, coord_zero, coord_one, Complex.normSq_apply]

/-- The factor pairing of `D₄² y` against `y` is the
`d₄²`-weighted sum of `y`'s site norm squares: the site
diagonal of `factorC4.D ^ 2` (`factorC4_D_sq_apply`) read
through the registered pairing. Tier T1. -/
theorem factorPair_Dsq_eq (y : Fin 4 → ℂ) :
    factorPair 4 ((factorC4.D ^ 2) y) y
      = ∑ k, d₄ k ^ 2 * Complex.normSq (y k) := by
  rw [factorPair_eq_sum_coords, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  have hD : ∀ b : Fin 2,
      realBasisEquiv 4 ((factorC4.D ^ 2) y) (k, b)
        = d₄ k ^ 2 * realBasisEquiv 4 y (k, b) := by
    intro b
    rw [coord_apply, coord_apply, factorC4_D_sq_apply]
    have hcast : (d₄ k : ℂ) ^ 2 = ((d₄ k ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    by_cases hb : b = 0
    · rw [if_pos hb, if_pos hb, hcast]
      simp only [Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im]
      ring
    · rw [if_neg hb, if_neg hb, hcast]
      simp only [Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im]
      ring
  rw [Fin.sum_univ_two, hD 0, hD 1, coord_zero, coord_one,
    Complex.normSq_apply]
  ring

/-- Every character value has unit modulus: the `j`-th
character at site `k` has norm square `1`, for all `j, k`
(the values are `1, i, -1, -i` in some order). Tier T1. -/
theorem fourierC4_normSq (j k : Fin 4) :
    Complex.normSq (fourierC4 j k) = 1 := by
  rw [Complex.normSq_apply]
  fin_cases j <;> fin_cases k <;> simp [fourierC4]

/-- The character vector's self-pairing is `4` (four sites of
unit modulus); hence the normalized character vector
`(1/2) • fourierC4 j` has self-pairing `1`. Tier T1. -/
theorem factorPair_fourier_self (j : Fin 4) :
    factorPair 4 (fourierC4 j) (fourierC4 j) = 4 := by
  rw [factorPair_self_eq]
  simp only [fourierC4_normSq, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  norm_num

/-- Right homogeneity of the factor pairing (the symmetry
transport of the landed `factorPair_smul_left`). Tier T1. -/
theorem factorPair_smul_right (r : ℝ) (x y : Fin 4 → ℂ) :
    factorPair 4 x (r • y) = r * factorPair 4 x y := by
  rw [factorPair_symm, factorPair_smul_left, factorPair_symm,
    smul_eq_mul]

/-- The factor pairing of the C4 square of a character vector
against itself is `5 / 16` — the landed `d₄_sum_sq`, since
every site contributes its full `d₄ k ^ 2` (unit modulus).
Tier T1. -/
theorem factorPair_Dsq_fourier (j : Fin 4) :
    factorPair 4 ((factorC4.D ^ 2) (fourierC4 j)) (fourierC4 j)
      = 5 / 16 := by
  rw [factorPair_Dsq_eq]
  simp only [fourierC4_normSq, mul_one]
  exact d₄_sum_sq

/-- **The C4 sector rate is character-independent**:
`c4SectorRate j = 5 / 64` for every character `j` — the
compression of the site-diagonal `D₄²` to any character line
is the site mean of `d₄²`, because the characters have unit
modulus. (The normalized line contributes the factor
`(1/2) * (1/2) = 1/4` against `factorPair_Dsq_fourier`'s
`5 / 16`.) Tier T1. -/
theorem c4SectorRate_eq (j : Fin 4) : c4SectorRate j = 5 / 64 := by
  unfold c4SectorRate factorEnergyC
  have hsmul : (factorC4.D ^ 2) ((1 / 2 : ℝ) • fourierC4 j)
      = (1 / 2 : ℝ) • ((factorC4.D ^ 2) (fourierC4 j)) :=
    map_smul _ _ _
  rw [hsmul, factorPair_smul_left, factorPair_smul_right,
    smul_eq_mul, factorPair_Dsq_fourier]
  norm_num

/-- The C4 sector rate is the mean of Q7CR-2's landed C4
factor spectrum `s₄c` over its 8 realified indices
(`sum_s₄c`, `sum_s₄`: the sum is `5 / 8`). Tier T1. -/
theorem c4SectorRate_eq_mean (j : Fin 4) :
    c4SectorRate j = (∑ b : Fin 4 × Fin 2, s₄c b) / 8 := by
  rw [c4SectorRate_eq, sum_s₄c, sum_s₄]
  norm_num

/-- The sector rates are nonnegative: each is a sum of the
landed nonnegative spectator eigenvalues and the sector rate
`5 / 64`. Tier T1. -/
theorem lamSecond_nonneg (j : Fin 4) (s : specIndex) :
    0 ≤ lamSecond j s := by
  have h1 := s₇c_nonneg s.1
  have h2 : 0 ≤ c4SectorRate j := by
    rw [c4SectorRate_eq]
    norm_num
  have h3 := s_R_nonneg s.2
  show 0 ≤ s₇c s.1 + c4SectorRate j + s_R s.2
  exact add_nonneg (add_nonneg h1 h2) h3

/-! ## §2. The sector vectors: membership in `sectorComp j`,
and the generator's pairing diagonal on them -/

/-- The normalized character vector's self-pairing is `1`:
the factor `(1/2) * (1/2)` against `factorPair_fourier_self`'s
`4`. Tier T1. -/
theorem factorPair_sector_self (j : Fin 4) :
    factorPair 4 ((1 / 2 : ℝ) • fourierC4 j)
      ((1 / 2 : ℝ) • fourierC4 j) = 1 := by
  rw [factorPair_smul_left, factorPair_smul_right, smul_eq_mul,
    factorPair_fourier_self]
  norm_num

/-- **The sector vectors lie in their composite sector**: the
sector vector at character `j` is a member of `sectorComp j`,
by Q7CR-6b's graded correspondence (`mem_sectorComp_tmul`:
pure-tensor membership is read off the C4 factor, for nonzero
spectators) and Q7CR-3's `fourierC4_mem_sectorC4`. The Q7 and
R4 basis vectors are nonzero (they are basis vectors). Tier
T1. -/
theorem sectorVec_mem_sectorComp (j : Fin 4) (a : Fin 7 × Fin 2)
    (m : Fin 4) :
    sectorVec j a m ∈ sectorComp j := by
  have hx : basisC 7 a ≠ 0 := (basisC 7).ne_zero a
  have hz : (Pi.basisFun ℝ (Fin 4)) m ≠ 0 :=
    (Pi.basisFun ℝ (Fin 4)).ne_zero m
  have hy : (1 / 2 : ℝ) • fourierC4 j ∈ sectorC4 j :=
    (sectorC4 j).smul_mem _ (fourierC4_mem_sectorC4 j)
  exact (mem_sectorComp_tmul hx hz).mpr hy

/-- The sector vector's self-pairing for the registered
composite pairing is the R4 site's η-sign: the factor
self-pairings are `1` (Q7 basis), `1` (normalized character
line), and `minkSign m` (R4 site), multiplied by
`compositePair_tmul`. Tier T1. -/
theorem compositePair_sectorVec_self (j : Fin 4)
    (a : Fin 7 × Fin 2) (m : Fin 4) :
    compositePair (sectorVec j a m) (sectorVec j a m)
      = minkSign m := by
  have h := compositePair_tmul (basisC 7 a) (basisC 7 a)
    ((1 / 2 : ℝ) • fourierC4 j) ((1 / 2 : ℝ) • fourierC4 j)
    ((Pi.basisFun ℝ (Fin 4)) m) ((Pi.basisFun ℝ (Fin 4)) m)
  have h7 : factorPair 7 (basisC 7 a) (basisC 7 a) = 1 := by
    rw [factorPair_basisC]
    simp
  have hR : minkowskiInner ((Pi.basisFun ℝ (Fin 4)) m)
      ((Pi.basisFun ℝ (Fin 4)) m) = minkSign m := by
    rw [minkowskiInner_basisFun]
    simp
  rw [h7, factorPair_sector_self, hR] at h
  have h2 : (1 : ℝ) * 1 * minkSign m = minkSign m := by ring
  rw [h2] at h
  exact h

/-- The generator's pairing, unfolded to T-Q7-2's composite
energy expectation: `dynGen = diracInst ^ 2` is the assembly
Hamiltonian (`hamAssembly_eq_dirac_sq`). Tier T1. -/
theorem compositePair_dynGen (ψ : q7c4r4Composite) :
    compositePair (dynGen ψ) ψ
      = compEnergy factorQ7 factorC4 factorR ψ := by
  show compositePair
      (((diracQ7C4R4 factorQ7 factorC4 factorR) ^ 2) ψ) ψ
    = compositePair (hamAssembly factorQ7 factorC4 factorR ψ) ψ
  rw [hamAssembly_eq_dirac_sq]

/-- **The rate tie**: the CHOSEN generator's pairing diagonal
on the sector vector at `(j, (k₇, b₇), m)` is exactly the
sector rate `lamSecond j ((k₇, b₇), m)` times the vector's
self-pairing sign — the compression of `dynGen` to the sector
line, read factorwise through T-Q7-2's weighted splitting
(`compEnergy_prod_weighted`): Q7 contributes `a₇ k₇ ^ 2`
(= `s₇c (k₇, b₇)`, `factorEnergyC_factorQ7_basis`), C4
contributes `c4SectorRate j` (by definition), R4 contributes
`r_R m ^ 2 * minkSign m` (= `s_R m * minkSign m`,
`factorEnergyR_factorR_basis`), and the spectator
self-pairings are `1, 1, minkSign m`. This is the proved
sense in which `lamSecond` is the step generator's graded
sector data. Tier T1. -/
theorem sectorVec_dynGen_pairing (j : Fin 4) (k₇ : Fin 7)
    (b₇ : Fin 2) (m : Fin 4) :
    compositePair (dynGen (sectorVec j (k₇, b₇) m))
        (sectorVec j (k₇, b₇) m)
      = lamSecond j ((k₇, b₇), m) * minkSign m := by
  have h7 : factorPair 7 (basisC 7 (k₇, b₇)) (basisC 7 (k₇, b₇))
      = 1 := by
    rw [factorPair_basisC]
    simp
  have hR : minkowskiInner ((Pi.basisFun ℝ (Fin 4)) m)
      ((Pi.basisFun ℝ (Fin 4)) m) = minkSign m := by
    rw [minkowskiInner_basisFun]
    simp
  have hw := compEnergy_prod_weighted factorQ7 factorC4 factorR
    (basisC 7 (k₇, b₇)) ((1 / 2 : ℝ) • fourierC4 j)
    ((Pi.basisFun ℝ (Fin 4)) m)
  rw [factorEnergyC_factorQ7_basis, factorPair_sector_self, h7,
    hR, factorEnergyR_factorR_basis] at hw
  calc compositePair (dynGen (sectorVec j (k₇, b₇) m))
          (sectorVec j (k₇, b₇) m)
      = compEnergy factorQ7 factorC4 factorR
          (sectorVec j (k₇, b₇) m) := compositePair_dynGen _
    _ = a₇ k₇ ^ 2 * 1 * minkSign m + 1 * c4SectorRate j
          * minkSign m + 1 * 1 * (r_R m ^ 2 * minkSign m) := hw
    _ = lamSecond j ((k₇, b₇), m) * minkSign m := by
        show a₇ k₇ ^ 2 * 1 * minkSign m + 1 * c4SectorRate j
              * minkSign m + 1 * 1 * (r_R m ^ 2 * minkSign m)
            = (s₇c (k₇, b₇) + c4SectorRate j + s_R m) * minkSign m
        rw [s₇c_apply]
        show a₇ k₇ ^ 2 * 1 * minkSign m + 1 * c4SectorRate j
              * minkSign m + 1 * 1 * (r_R m ^ 2 * minkSign m)
            = (a₇ k₇ ^ 2 + c4SectorRate j + r_R m ^ 2) * minkSign m
        ring

/-- The sector rate family, in closed form: the Q7 spectator
eigenvalue, the character-independent C4 rate `5 / 64`, and
the R4 spectator eigenvalue. Tier T1. -/
theorem lamSecond_eq (j : Fin 4) (s : specIndex) :
    lamSecond j s = s₇c s.1 + 5 / 64 + s_R s.2 := by
  show s₇c s.1 + c4SectorRate j + s_R s.2
    = s₇c s.1 + 5 / 64 + s_R s.2
  rw [c4SectorRate_eq]

/-! ## §3. The registered seat: transport to `Fin 56`, the
state, and the decision -/

/-- The extracted rates are nonnegative at every seat index.
Tier T1. -/
theorem lamFin_nonneg (j : Fin 4) (i : Fin 56) :
    0 ≤ lamFin j i :=
  lamSecond_nonneg j _

/-- The uniform state sums to `1` over the 56 spectator
indices: `56 * (56 : ℝ)⁻¹ = 1`. Tier T1. -/
theorem sectorUniform_sum : ∑ i : Fin 56, sectorUniform i = 1 := by
  show ∑ _i : Fin 56, (56 : ℝ)⁻¹ = 1
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  norm_num

/-- The extracted weights are nonnegative at every seat
index. Tier T1. -/
theorem wFin_nonneg (j : Fin 4) (i : Fin 56) : 0 ≤ wFin j i := by
  show 0 ≤ (56 : ℝ)⁻¹
  positivity

/-- The extracted weights form a state on every sector.
Tier T1. -/
theorem wFin_sum (j : Fin 4) : ∑ i, wFin j i = 1 :=
  sectorUniform_sum

/-- **Sectorwise nonnegativity at the instantiated seat**:
for every character sector `j` and every step parameter
`t >= 0`, the sector's defect is nonnegative — the landed
`traceDefect_nonneg` applied to the extracted data, whose
hypotheses are the proved ties of sections 1-3 (rates
nonnegative by `lamFin_nonneg`; the weights a state by
`wFin_nonneg` / `wFin_sum`). Tier T1. -/
theorem sector_traceDefect_nonneg (j : Fin 4) {t : ℝ}
    (ht : 0 ≤ t) :
    0 ≤ traceDefect (lamFin j) t (wFin j) :=
  traceDefect_nonneg _ ht (lamFin_nonneg j) _ (wFin_nonneg j)
    (wFin_sum j)

/-- **The sector defect, in closed form**: at sector `j` the
defect is the uniform average over the spectator seat of the
per-index step losses `1 - exp (-2 * t * lamSecond j s)` —
the landed closed form `traceDefect_eq_sum`, transported
along `specEquiv`. Tier T1. -/
theorem sector_traceDefect_eq (j : Fin 4) (t : ℝ) :
    traceDefect (lamFin j) t (wFin j)
      = (56 : ℝ)⁻¹ * ∑ s : specIndex,
          (1 - Real.exp (-2 * t * lamSecond j s)) := by
  have h1 : (∑ i : Fin 56, wFin j i
        * (1 - Real.exp (-2 * t * lamFin j i)))
      = (56 : ℝ)⁻¹ * ∑ i : Fin 56,
          (1 - Real.exp (-2 * t * lamSecond j (specEquiv.symm i))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rfl
  rw [traceDefect_eq_sum _ _ _ (wFin_sum j), h1,
    Equiv.sum_comp specEquiv.symm
      (fun s => 1 - Real.exp (-2 * t * lamSecond j s))]

/-- **HEADLINE — W2 DECIDED: PROVED.** The registered Prop
`LegSecondArrow`, instantiated at the extracted sector data
(`lamFin`, `wFin`) of the composite seat, holds for every
step parameter `t >= 0`: every C4 character sector has
nonnegative defect under the composite's stated step, in the
sector-compression sense stated on this module's face.
**K-T-C4-2 does NOT fire** — no character sector has negative
defect. Tier T1. -/
theorem w2_legSecondArrow (t : ℝ) (ht : 0 ≤ t) :
    LegSecondArrow lamFin t wFin :=
  fun j => sector_traceDefect_nonneg j ht

end ThetLogos
