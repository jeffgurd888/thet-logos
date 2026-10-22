import Mathlib.Tactic
import ThetLogos.EdgeSignature
import ThetLogos.FiniteSpectralTriple
import ThetLogos.MartinettiRep
import ThetLogos.InnerFluctuations

open Matrix Finset

namespace ThetLogos

/-!
# ThetLogos.DiracTorsionMap — the D_F torsion map (T1 target)

HONESTY LEDGER (read before citing):

- Status: **STANDS WHOLE (T1) — landed 2026-10-22.** Compiled green
  (`lake build ThetLogos.DiracTorsionMap`, 8,985 jobs) and
  parent-verified: `.olean` present, strict recount 18, placeholder
  census 0/0/0, `#print axioms` on the six headline declarations =
  the standard three only. Both seat verdicts proved exactly as
  drafted — no statement, name, or definition changed in the compile;
  repairs touched proof bodies only. Dossier:
  `whitepaper/dirac-torsion-map-2026-10-22.md`.
- What this brick is: queue item 3 of the unparked fleet line,
  admitted by Jeff 2026-10-19 ("density side first, torsion map
  after"). It is the priced step 1 of the Morley gauntlet dossier
  (`whitepaper/gauntlet-morley-3plus1-2026-10-11.md`, §7): *"build η
  from Dirac data (grading/sign), compute the induced defect T under
  inner fluctuations D ↦ D_A."* `EdgeSignature` (§3, T1) built the
  abstract law and explicitly left this D_F-specific map priced and
  unbuilt; `WeldDuality` carried the law's two faces in a `Fin 4`
  arena with an abstract `D` as INPUT — it never touched the
  corpus's actual Dirac operator. This brick does.

- The law (EdgeSignature §3, quoted): in a ℂ-algebra `R`, for
  `η T : R` with `η * η = 1`,
  `torsion_defect : (η + T) * (η + T) = 1 + (η * T + T * η + T * T)`,
  and `torsion_flat_iff : (η + T) * (η + T) = 1 ↔ η * T + T * η + T * T = 0`.
  Note what the law does NOT assume: no self-adjointness, no
  Hermiticity — `η² = 1` alone. Everything below is instantiated at
  `R := Matrix I32 I32 ℂ`.

- The arena: the corpus's finite Dirac family
  `buildDirac A B C E : Matrix I32 I32 ℂ` on
  `ℂ³² = H_L ⊕ H_R ⊕ H_L^c ⊕ H_R^c` (`FiniteSpectralTriple`), its
  one-generation member `DF_oneGen`, the SM ansatz
  `smDirac yNu yE yU yD yR = buildDirac (yukawaBlock …) (conj …) 0
  (majoranaBlock yR)` (`MartinettiRep`), the grading
  `gammaF = diag(+I₈, −I₈, −I₈, +I₈)` (`Scaffold32`), and inner
  fluctuations `fluctuatedDirac D A = D + A + UJ * Aᵀ * UJ`
  (`InnerFluctuations`). Corpus facts used, all T1/T3 in their home
  modules: `gammaF_involutive` (`γ * γ = 1`),
  `gammaF_self_adjoint`, `buildDirac_gamma_odd`
  (`γ * D + D * γ = 0` for every `buildDirac`),
  `buildDirac_self_adjoint`, `smDirac_grading_odd`,
  `smDirac_self_adjoint`, `majoranaBlock_val`.

- THE TWO SEATS (the identification, on the face). EdgeSignature's
  η must be built from Dirac data; the dossier's own disjunction is
  "(grading/sign)", and this brick carries BOTH seats rather than
  pretending one is forced:
  * **Seat 1 — the grading seat (canonical).** `η := gammaF`. This
    is the triple's own grading, the corpus's unique self-adjoint
    involution carried as triple data, and the object
    EdgeSignature's header calls "the Krein η from Rung 3". The
    instantiation is theorem-level: γ satisfies η's only hypothesis
    (`γ * γ = 1`). Once "η from grading data" is chosen, no
    modelling freedom remains.
  * **Seat 2 — the sign seat (T2 nomenclature).** On the FLAT
    sector of the ansatz — equal real Yukawas
    `yNu = yE = yU = yD = (y : ℂ)`, `y ≠ 0`, Majorana parameter
    `s = 0` — the operator squares to a scalar
    (`smDirac_flat_sq : D₀ * D₀ = (↑y * ↑y) • 1`), so its sign/phase
    `etaSign y := (↑y)⁻¹ • D₀` is an elementary involution built
    from D itself. Calling this operator "the sign of D_F" is a
    modelling choice, labelled T2 on the face; that it is an
    involution, is γ-odd, and is the corpus's named one-generation
    operator rescaled (`smDirac_zero_eq_oneGen`) are theorems.
    Off the flat sector no elementary sign exists; see R1.

- SURVIVAL VERDICTS, AS DRAFTED (the brick's headlines):
  * **Seat 1: SURVIVES, trivially — the torsion map is the zero
    map.** `fluctuatedDirac` never touches γ, and γ-oddness is
    preserved under inner fluctuations
    (`fluctuatedDirac_gamma_odd`, via `gammaF_UJ_anticomm` and
    `oppositeOneForm_gamma_odd`): the fluctuated operator still
    lives in the same edge-pair frame, so the η read off the
    grading is unchanged, the induced correction is `T = 0`, and
    the defect vanishes (`grading_seat_survival`). The content is
    the invariance theorem, not the trivial defect arithmetic.
    D_F itself is purely off-diagonal across γ's edge pair
    (`buildDirac_edge_odd`): the projection from D_F carries no
    torsion in this seat.
  * **Seat 2: SURVIVAL FAILS under the Majorana deformation, for
    every `s ≠ 0`.** The corpus's standard one-parameter
    deformation of the flat sector is the Majorana line
    `s ↦ smDirac ↑y ↑y ↑y ↑y s`. The induced correction on η is
    `torsionMajorana y s := (↑y)⁻¹ • (D(s) − D(0))`, supported
    exactly on the Majorana (E) blocks
    (`deltaDirac_eq`). Its EdgeSignature defect does not vanish:
    the single entry
    `defect (etaSign y) (torsionMajorana y s) ⟨0⟩ ⟨24⟩
      = (↑y)⁻¹ * star s`
    (`defect_entry`) — the (ν_L, ν̄_R) corner, where the
    anticommutator term `η₀ * T` lands and where `T * η₀` and
    `T * T` are both zero because T's row `⟨0⟩` vanishes. Hence
    `majorana_survival_iff : (η₀ + T) * (η₀ + T) = 1 ↔ s = 0`:
    survival holds exactly at the undeformed point and breaks
    everywhere else on the line, with the obstruction linear in
    `star s`. A kill is a result: in the sign seat, the Majorana
    block IS D_F's torsion, and it is not flat.

- Fences. Finite level only: `Matrix I32 I32 ℂ`, the corpus's own
  blocks, no continuum operator, no connection, no spectral
  functional calculus. Seat 2 is stated only on the flat sector
  (equal real Yukawas, `y ≠ 0`); nothing is claimed about the sign
  of a general `buildDirac`. The Majorana line is the corpus's own
  deformation (`smDirac`'s fifth parameter); no other deformation
  is mapped. Nothing here touches the killed ℂ⁷-torsion claim
  (kill ledger stands; it is not resurrected, renamed, or
  approached), `signature_not_determined` (EdgeSignature §4: the
  signature numbers remain extra data), Yang–Mills, or any
  Millennium statement.

- Named remainders (K3 — what this brick does NOT build):
  R1. The sign of a GENERAL `buildDirac A B C E` (non-scalar `D²`)
  via spectral functional calculus. HermitianReduction landed
  eigen-decomposition transport machinery, but a sign-of-D
  construction with fluctuation covariance is a separate build.
  R2. The third seat: `UJ` also satisfies `UJ * UJ = 1`
  (`UJ_mul_self`, Scaffold32) and is a fundamental-symmetry
  candidate in its own right. Not developed here; the J-seat
  torsion map is unbuilt.
  R3. The three-generation triplication `smDirac3diag = D₁ ⊗ I₃`
  (ThreeGen): the map is stated for the one-generation arena;
  triplicated torsion is not computed.
  R4. The gauntlet dossier's step 3 — connecting torsion-flatness
  to the twisted first-order condition machinery — and any
  continuum notion of torsion. Pointers only; unbuilt.

- Pre-named kill conditions. K1: if D_F had no canonical seat in
  EdgeSignature's frame, the brick would narrow to the
  least-ambiguous identification and label it T2 — outcome: two
  seats carried instead, γ canonical (theorem-level) and the sign
  seat labelled T2 on its face, exactly as recorded above; no
  single "the torsion of D_F" is asserted beyond what each seat
  proves. K2: any placeholder proof, and this file does not
  count. K3: any part needing machinery beyond the finite matrices
  present is a named remainder above (R1–R4), never an aspiration
  stated as a theorem.
-/

-- ============================================================================
-- §0. The defect, at the Dirac arena
-- ============================================================================

/-- The EdgeSignature torsion defect `ηT + Tη + T²`, at
    `R := Matrix I32 I32 ℂ`. Tier T2 (definition; the law about it is
    T1, cited next). -/
def defect (η T : Matrix I32 I32 ℂ) : Matrix I32 I32 ℂ :=
  η * T + T * η + T * T

/-- Torsion-flatness at the Dirac arena (T1 — proved, by citation):
    EdgeSignature's `torsion_flat_iff` instantiated at
    `Matrix I32 I32 ℂ`. `η + T` is a fundamental symmetry iff the
    defect vanishes. -/
theorem dirac_torsion_flat_iff (η T : Matrix I32 I32 ℂ) (h : η * η = 1) :
    (η + T) * (η + T) = 1 ↔ defect η T = 0 := by
  unfold defect
  exact torsion_flat_iff η T h

-- ============================================================================
-- §1. Seat 1 — the grading seat: η := gammaF
-- ============================================================================

/-- The edge projections of γ_F, entrywise (T1 target): `edgePlus γ_F`
    is the diagonal projection onto the `+` sectors `H_L ⊕ H_R^c`
    (indices `< 8` or `≥ 24`), `edgeMinus` onto the `−` sectors.
    This is the corpus's "projection from D_F" made explicit: the
    spectral projections of the triple's grading. -/
theorem edgePlus_gammaF_apply (i j : I32) :
    edgePlus gammaF i j
      = if (i = j ∧ (i.val < 8 ∨ 24 ≤ i.val)) then 1 else 0 := by
  have hdiag : ∀ k : I32, gammaF k k
      = if k.val < 8 then (1 : ℂ) else if k.val < 16 then -1
        else if k.val < 24 then -1 else 1 := by
    intro k
    unfold gammaF
    simp
  unfold edgePlus
  rw [Matrix.smul_apply, Matrix.add_apply]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq, hdiag, smul_eq_mul]
    by_cases h1 : i.val < 8
    · rw [if_pos h1, if_pos ⟨rfl, Or.inl h1⟩]
      have h2 : (1 : ℂ) + 1 = 2 := by norm_num
      rw [h2]
      exact inv_mul_cancel₀ (by norm_num)
    · by_cases h2 : i.val < 16
      · have hcond : ¬ (i = i ∧ (i.val < 8 ∨ 24 ≤ i.val)) := by
          rintro ⟨-, h⟩
          rcases h with h | h
          · exact h1 h
          · omega
        rw [if_neg h1, if_pos h2, if_neg hcond]
        simp
      · by_cases h3 : i.val < 24
        · have hcond : ¬ (i = i ∧ (i.val < 8 ∨ 24 ≤ i.val)) := by
            rintro ⟨-, h⟩
            rcases h with h | h
            · exact h1 h
            · omega
          rw [if_neg h1, if_neg h2, if_pos h3, if_neg hcond]
          simp
        · rw [if_neg h1, if_neg h2, if_neg h3,
            if_pos ⟨rfl, Or.inr (by omega : 24 ≤ i.val)⟩]
          have h2 : (1 : ℂ) + 1 = 2 := by norm_num
          rw [h2]
          exact inv_mul_cancel₀ (by norm_num)
  · simp [hij, Matrix.one_apply_ne, gammaF_apply_ne]

/-- D_F is purely off-diagonal across γ's edge pair (T1 target):
    for every `buildDirac A B C E`, both diagonal blocks of D in the
    edge decomposition vanish, `E₊ D E₊ = 0` and `E₋ D E₋ = 0`.
    The projection from D_F, in the grading seat, carries no
    diagonal part — Jeff's "torsion twist in the projection" is
    zero here, proved from `buildDirac_gamma_odd` alone. -/
theorem buildDirac_edge_odd (A B C E : Block8) :
    edgePlus gammaF * buildDirac A B C E * edgePlus gammaF = 0
      ∧ edgeMinus gammaF * buildDirac A B C E * edgeMinus gammaF = 0 := by
  -- One engine for both edges: any γ-odd `M` is edge-off-diagonal.
  have key : ∀ M : Matrix I32 I32 ℂ, gammaF * M + M * gammaF = 0 →
      edgePlus gammaF * M * edgePlus gammaF = 0
        ∧ edgeMinus gammaF * M * edgeMinus gammaF = 0 := by
    intro M hM
    have hMγ : M * gammaF = -(gammaF * M) :=
      eq_neg_of_add_eq_zero_right hM
    have hγMγ : gammaF * M * gammaF = -M := by
      rw [Matrix.mul_assoc, hMγ, mul_neg, ← Matrix.mul_assoc,
        gammaF_involutive, Matrix.one_mul]
    have hexp : (1 + gammaF) * M * (1 + gammaF)
        = (M + gammaF * M * gammaF) + (gammaF * M + M * gammaF) := by
      simp only [add_mul, mul_add, one_mul, mul_one, Matrix.mul_assoc]
      abel
    have hexp' : (1 - gammaF) * M * (1 - gammaF)
        = (M + gammaF * M * gammaF) - (gammaF * M + M * gammaF) := by
      simp only [sub_mul, mul_sub, one_mul, mul_one, Matrix.mul_assoc]
      abel
    constructor
    · unfold edgePlus
      rw [Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_smul, smul_smul, ← Matrix.mul_assoc, hexp, hM,
        hγMγ, add_zero, add_neg_cancel, smul_zero]
    · unfold edgeMinus
      rw [Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_smul, smul_smul, ← Matrix.mul_assoc, hexp', hM,
        sub_zero, hγMγ, add_neg_cancel, smul_zero]
  exact key _ (buildDirac_gamma_odd A B C E)

/-- γ anticommutes with the real structure's matrix (T1 target):
    `gammaF * UJ + UJ * gammaF = 0`. Entrywise: `UJ` moves index `i`
    to its partner, and the partner always sits in the opposite
    γ-sector (`gammaF (partner i) (partner i) = - gammaF i i`). -/
theorem gammaF_UJ_anticomm :
    gammaF * UJ + UJ * gammaF = 0 := by
  ext i j
  rw [Matrix.add_apply, gammaF_mul_apply, mul_gammaF_apply,
    Matrix.zero_apply]
  by_cases h : j = partner i
  · subst h
    have hUJ : UJ i (partner i) = 1 := by simp [UJ, UJ_matrix]
    have hsign : gammaF (partner i) (partner i) = - gammaF i i := by
      have hdiag : ∀ k : I32, gammaF k k
          = if k.val < 8 then (1 : ℂ) else if k.val < 16 then -1
            else if k.val < 24 then -1 else 1 := by
        intro k
        unfold gammaF
        simp
      rw [hdiag, hdiag, partner_val_eq]
      have hi : i.val < 32 := i.isLt
      interval_cases h : i.val <;> simp
    rw [hUJ, hsign]
    ring
  · have hUJ : UJ i j = 0 := by simp [UJ, UJ_matrix, h]
    rw [hUJ]
    simp

/-- The opposite 1-form of a γ-odd matrix is γ-odd (T1 target):
    `A° = UJ * Aᵀ * UJ` inherits oddness from `A`, via
    `gammaF_UJ_anticomm` and `γᵀ = γ`. -/
theorem oppositeOneForm_gamma_odd (A : Matrix I32 I32 ℂ)
    (hA : gammaF * A + A * gammaF = 0) :
    gammaF * oppositeOneForm A + oppositeOneForm A * gammaF = 0 := by
  have hγT : gammaF.transpose = gammaF := by
    ext a b
    rw [Matrix.transpose_apply]
    by_cases h : a = b
    · subst h
      rfl
    · rw [gammaF_apply_ne (Ne.symm h), gammaF_apply_ne h]
  have hAT : gammaF * A.transpose + A.transpose * gammaF = 0 := by
    have h2 := congrArg Matrix.transpose hA
    simp only [Matrix.transpose_add, Matrix.transpose_mul, hγT,
      Matrix.transpose_zero] at h2
    rwa [add_comm] at h2
  have hγUJ : gammaF * UJ = -(UJ * gammaF) :=
    eq_neg_of_add_eq_zero_left gammaF_UJ_anticomm
  have hUJγ : UJ * gammaF = -(gammaF * UJ) :=
    eq_neg_of_add_eq_zero_right gammaF_UJ_anticomm
  have hgAo : gammaF * oppositeOneForm A
      = (gammaF * UJ) * A.transpose * UJ := by
    unfold oppositeOneForm
    simp only [← Matrix.mul_assoc]
  have hAog : oppositeOneForm A * gammaF
      = (UJ * A.transpose) * (UJ * gammaF) := by
    unfold oppositeOneForm
    exact Matrix.mul_assoc _ _ _
  have hfact : (UJ * gammaF * A.transpose) * UJ
      + (UJ * A.transpose * (gammaF * UJ))
      = UJ * (gammaF * A.transpose + A.transpose * gammaF) * UJ := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  have e1 : gammaF * oppositeOneForm A
      = -((UJ * gammaF) * A.transpose * UJ) := by
    rw [hgAo, hγUJ, neg_mul, neg_mul]
  have e2 : oppositeOneForm A * gammaF
      = -((UJ * A.transpose) * (gammaF * UJ)) := by
    rw [hAog, hUJγ, mul_neg]
  rw [e1, e2, ← neg_add, hfact, hAT, Matrix.mul_zero, Matrix.zero_mul,
    neg_zero]

/-- Inner fluctuations preserve γ-oddness (T1 target): if `D` and
    the 1-form `A` are γ-odd, so is the fluctuated Dirac operator
    `fluctuatedDirac D A = D + A + A°`. -/
theorem fluctuatedDirac_gamma_odd (D A : Matrix I32 I32 ℂ)
    (hD : gammaF * D + D * gammaF = 0)
    (hA : gammaF * A + A * gammaF = 0) :
    gammaF * fluctuatedDirac D A + fluctuatedDirac D A * gammaF = 0 := by
  have key : gammaF * fluctuatedDirac D A + fluctuatedDirac D A * gammaF
      = (gammaF * D + D * gammaF) + (gammaF * A + A * gammaF)
        + (gammaF * oppositeOneForm A
          + oppositeOneForm A * gammaF) := by
    simp only [fluctuatedDirac, mul_add, add_mul]
    abel
  rw [key, hD, hA, oppositeOneForm_gamma_odd A hA]
  simp

/-- **Seat 1 survival verdict (T1 target): the grading seat's
    torsion map is the zero map.** The defect of the uncorrected
    grading vanishes, and every inner fluctuation of a γ-odd Dirac
    operator by a γ-odd 1-form stays in the γ frame — the η read off
    the grading is unchanged by `D ↦ D_A`, so the induced
    correction is `T = 0` and `torsion_flat_iff` is satisfied
    trivially. The substance is the invariance
    (`fluctuatedDirac_gamma_odd`), not the arithmetic. -/
theorem grading_seat_survival :
    defect gammaF 0 = 0 ∧ ∀ (D A : Matrix I32 I32 ℂ),
      gammaF * D + D * gammaF = 0 → gammaF * A + A * gammaF = 0 →
      gammaF * fluctuatedDirac D A + fluctuatedDirac D A * gammaF = 0 :=
  ⟨by simp [defect],
   fun D A hD hA => fluctuatedDirac_gamma_odd D A hD hA⟩

-- ============================================================================
-- §2. Seat 2 — the sign seat on the flat sector, and the Majorana line
-- ============================================================================

/-- The block-swap index of the flat Dirac operator: the unique
    column a row of `smDirac ↑y ↑y ↑y ↑y 0` can reach. Within each
    16-block it swaps the two 8-blocks (the diagonal blocks of the
    ansatz pair row `i` with the row across the block boundary at
    the same local index). Tier T2 (definition). -/
def sigmaIdx (i : I32) : I32 :=
  ⟨if i.val < 8 then i.val + 8
   else if i.val < 16 then i.val - 8
   else if i.val < 24 then i.val + 8
   else i.val - 8, by
    have hi := i.isLt
    split_ifs <;> omega⟩

/-- The block swap is an involution (T1 target). -/
theorem sigmaIdx_involutive (i : I32) : sigmaIdx (sigmaIdx i) = i := by
  have hv : ∀ k : I32, (sigmaIdx k).val
      = if k.val < 8 then k.val + 8
        else if k.val < 16 then k.val - 8
        else if k.val < 24 then k.val + 8
        else k.val - 8 := fun k => rfl
  apply Fin.ext
  rw [hv (sigmaIdx i), hv i]
  by_cases h1 : i.val < 8 <;> by_cases h2 : i.val < 16 <;>
    by_cases h3 : i.val < 24 <;> split_ifs <;> omega

/-- Support of the flat Dirac operator (T1 target): every nonzero
    entry of `smDirac ↑y ↑y ↑y ↑y 0` sits in the block-swap column.
    All four blocks of the flat ansatz are diagonal (`yukawaBlock`
    of equal entries, `majoranaBlock 0 = 0`), so row `i` reaches
    only column `sigmaIdx i`. -/
theorem smDirac_flat_support (y : ℝ) (i k : I32)
    (h : smDirac ↑y ↑y ↑y ↑y 0 i k ≠ 0) : k = sigmaIdx i := by
  by_contra hk
  apply h
  have hkval : k.val ≠ (sigmaIdx i).val := fun hv => hk (Fin.ext hv)
  have hσval : (sigmaIdx i).val
      = if i.val < 8 then i.val + 8
        else if i.val < 16 then i.val - 8
        else if i.val < 24 then i.val + 8
        else i.val - 8 := rfl
  have hM0 : majoranaBlock 0 = 0 := by
    ext a b
    rw [Matrix.zero_apply]
    unfold majoranaBlock
    rw [Matrix.diagonal_apply]
    split_ifs <;> rfl
  by_cases H1 : i.val < 8 <;> by_cases H2 : i.val < 16 <;>
    by_cases H3 : i.val < 24 <;>
    (unfold smDirac buildDirac
     simp only []
     split_ifs <;>
       simp_all only [hσval, hM0, yukawaBlock, Matrix.diagonal_apply,
         Matrix.map_apply, starRingEnd_apply, Matrix.conjTranspose_apply,
         Matrix.conjTranspose_zero, Fin.ext_iff, Matrix.zero_apply,
         star_zero, ite_true, ite_false, dite_true, dite_false] <;>
       (try (split_ifs with hab)) <;>
       first | rfl | (simp only [Matrix.zero_apply, star_zero]) | (intro a; exfalso; omega) | (exfalso; omega) | (exfalso; have hv := congrArg Fin.val hab; dsimp only at hv; omega) | skip)

/-- Value of the flat Dirac operator on its support (T1 target):
    `smDirac ↑y ↑y ↑y ↑y 0` at `(i, sigmaIdx i)` is exactly `↑y` —
    in each of the four block regions the reached entry is a
    diagonal Yukawa entry (or its conjugate, and `↑y` is real). -/
theorem smDirac_flat_value (y : ℝ) (i : I32) :
    smDirac ↑y ↑y ↑y ↑y 0 i (sigmaIdx i) = (↑y : ℂ) := by
  have hσval : (sigmaIdx i).val
      = if i.val < 8 then i.val + 8
        else if i.val < 16 then i.val - 8
        else if i.val < 24 then i.val + 8
        else i.val - 8 := rfl
  have hvec : ∀ a : Fin 8,
      (![(↑y : ℂ), ↑y, ↑y, ↑y, ↑y, ↑y, ↑y, ↑y] : Fin 8 → ℂ) a = ↑y := by
    intro a
    fin_cases a <;> simp
  by_cases H1 : i.val < 8
  · -- Row in H_L, reached column in H_R: the A block, diagonal.
    have hj : (sigmaIdx i).val = i.val + 8 := by rw [hσval]; simp [H1]
    have hj8 : ¬ (sigmaIdx i).val < 8 := by omega
    have hj16 : (sigmaIdx i).val < 16 := by omega
    unfold smDirac buildDirac
    simp only []
    simp only [H1, hj8, hj16, dite_true, dite_false]
    rw [yukawaBlock, Matrix.diagonal_apply]
    split_ifs with hab
    · exact hvec _
    · exfalso
      apply hab
      apply Fin.ext
      show i.val = (sigmaIdx i).val - 8
      omega
  · by_cases H2 : i.val < 16
    · -- Row in H_R, reached column in H_L: the A† block, diagonal,
      -- entry `star (↑y) = ↑y`.
      have hj : (sigmaIdx i).val = i.val - 8 := by
        rw [hσval]; simp [H1, H2]
      have hj8 : (sigmaIdx i).val < 8 := by omega
      unfold smDirac buildDirac
      simp only []
      simp only [H1, H2, hj8, dite_true, dite_false]
      rw [Matrix.conjTranspose_apply, yukawaBlock, Matrix.diagonal_apply]
      split_ifs with hab
      · rw [hvec]
        exact RCLike.conj_ofReal y
      · exfalso
        apply hab
        apply Fin.ext
        show (sigmaIdx i).val = i.val - 8
        omega
    · by_cases H3 : i.val < 24
      · -- Row in H_L^c, reached column in H_R^c: the B block
        -- (`B = Ā`), diagonal, entry `star (↑y) = ↑y`.
        have hj : (sigmaIdx i).val = i.val + 8 := by
          rw [hσval]; simp [H1, H2, H3]
        have hj8 : ¬ (sigmaIdx i).val < 8 := by omega
        have hj16 : ¬ (sigmaIdx i).val < 16 := by omega
        have hj24 : ¬ (sigmaIdx i).val < 24 := by omega
        unfold smDirac buildDirac
        simp only []
        simp only [H1, H2, H3, hj8, hj16, hj24, dite_true, dite_false]
        rw [Matrix.map_apply, starRingEnd_apply, yukawaBlock,
          Matrix.diagonal_apply]
        split_ifs with hab
        · rw [hvec]
          exact RCLike.conj_ofReal y
        · exfalso
          apply hab
          apply Fin.ext
          show i.val - 16 = (sigmaIdx i).val - 24
          omega
      · -- Row in H_R^c, reached column in H_L^c: the B† block,
        -- entry `star (star (↑y)) = ↑y`.
        have hj : (sigmaIdx i).val = i.val - 8 := by
          rw [hσval]; simp [H1, H2, H3]
        have hj8 : ¬ (sigmaIdx i).val < 8 := by omega
        have hj16 : ¬ (sigmaIdx i).val < 16 := by omega
        have hj24 : (sigmaIdx i).val < 24 := by omega
        unfold smDirac buildDirac
        simp only []
        simp only [H1, H2, H3, hj8, hj16, hj24, dite_true, dite_false]
        rw [Matrix.conjTranspose_apply, Matrix.map_apply,
          starRingEnd_apply, yukawaBlock, Matrix.diagonal_apply]
        split_ifs with hab
        · rw [hvec, star_star]
        · exfalso
          apply hab
          apply Fin.ext
          show (sigmaIdx i).val - 16 = i.val - 24
          omega

/-- **The flat sector is flat** (T1 target): at equal real Yukawas
    and zero Majorana parameter, the ansatz Dirac operator squares
    to the scalar `(↑y * ↑y) • 1`. This is the fact that makes the
    sign seat elementary: no spectral calculus is needed to
    normalise `D₀`. -/
theorem smDirac_flat_sq (y : ℝ) :
    smDirac ↑y ↑y ↑y ↑y 0 * smDirac ↑y ↑y ↑y ↑y 0
      = (↑y * ↑y) • 1 := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hij : j = i
  · rw [hij]
    rw [Finset.sum_eq_single (sigmaIdx i)]
    · have hv1 := smDirac_flat_value y i
      have hv2 := smDirac_flat_value y (sigmaIdx i)
      rw [sigmaIdx_involutive] at hv2
      rw [hv1, hv2, Matrix.smul_apply, Matrix.one_apply_eq]
      exact ((Complex.ofReal_mul y y).symm.trans (mul_one _).symm).trans
        (smul_eq_mul _ _).symm
    · intro k _ hk
      have hz : smDirac ↑y ↑y ↑y ↑y 0 i k = 0 := by
        by_contra hc
        exact hk (smDirac_flat_support y i k hc)
      rw [hz, zero_mul]
    · intro hcon
      exact absurd (Finset.mem_univ _) hcon
  · have hsum : ∑ k : I32, smDirac ↑y ↑y ↑y ↑y 0 i k
        * smDirac ↑y ↑y ↑y ↑y 0 k j = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      by_cases hk : k = sigmaIdx i
      · subst hk
        have hz : smDirac ↑y ↑y ↑y ↑y 0 (sigmaIdx i) j = 0 := by
          by_contra hc
          have h3 := smDirac_flat_support y (sigmaIdx i) j hc
          rw [sigmaIdx_involutive] at h3
          exact hij h3
        rw [hz, mul_zero]
      · have hz : smDirac ↑y ↑y ↑y ↑y 0 i k = 0 := by
          by_contra hc
          exact hk (smDirac_flat_support y i k hc)
        rw [hz, zero_mul]
    rw [hsum, Matrix.smul_apply, Matrix.one_apply_ne (Ne.symm hij), smul_zero]

/-- The flat sector's operator is the corpus's named one-generation
    Dirac operator (T1 target): `smDirac ↑y ↑y ↑y ↑y 0`
    is `DF_oneGen y y y y` — same diagonal Yukawa block, conjugated
    copy (which agrees, the entries being real), zero Majorana
    block. The sign seat is therefore taken on the corpus's actual
    `D_F`, not on a lookalike. -/
theorem smDirac_zero_eq_oneGen (y : ℝ) :
    smDirac ↑y ↑y ↑y ↑y 0 = DF_oneGen y y y y := by
  have hM0 : majoranaBlock 0 = 0 := by
    ext a b
    rw [Matrix.zero_apply]
    unfold majoranaBlock
    rw [Matrix.diagonal_apply]
    split_ifs <;> rfl
  unfold smDirac DF_oneGen yukawaBlock
  rw [hM0]

/-- **The sign of the flat Dirac operator** (Tier T2 definition —
    the seat-2 identification): `etaSign y := (↑y)⁻¹ • D₀`, the
    phase of the flat sector's Dirac operator. An involution by
    `etaSign_sq`; the name "sign" is the modelling choice recorded
    in the header. -/
noncomputable def etaSign (y : ℝ) : Matrix I32 I32 ℂ :=
  (↑y)⁻¹ • smDirac ↑y ↑y ↑y ↑y 0

/-- The sign is an involution (T1 target): `(etaSign y)² = 1` for
    `y ≠ 0`, from `smDirac_flat_sq` by scalar arithmetic. -/
theorem etaSign_sq (y : ℝ) (hy : y ≠ 0) : etaSign y * etaSign y = 1 := by
  have hne : (↑y : ℂ) ≠ 0 := by exact_mod_cast hy
  have hcc : (↑y : ℂ)⁻¹ * (↑y : ℂ)⁻¹ * ((↑y : ℂ) * (↑y : ℂ)) = 1 := by
    calc (↑y : ℂ)⁻¹ * (↑y : ℂ)⁻¹ * ((↑y : ℂ) * (↑y : ℂ))
        = ((↑y : ℂ)⁻¹ * ↑y) * ((↑y : ℂ)⁻¹ * ↑y) := by ring
      _ = 1 * 1 := by rw [inv_mul_cancel₀ hne]
      _ = 1 := mul_one _
  unfold etaSign
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, smDirac_flat_sq,
    smul_smul]
  have key : ∀ r : ℝ, r = 1 → r • (1 : Matrix I32 I32 ℂ) = 1 :=
    fun r hr => by rw [hr, one_smul]
  apply key
  field_simp

/-- **The Majorana torsion correction** (Tier T2 definition):
    along the corpus's Majorana line `s ↦ smDirac ↑y ↑y ↑y ↑y s`,
    the correction to the sign seat, normalised by the flat scale:
    `torsionMajorana y s := (↑y)⁻¹ • (D(s) − D(0))`. Note
    `etaSign y + torsionMajorana y s = (↑y)⁻¹ • D(s)`: the pair
    `(η₀ + T)` of EdgeSignature's law is exactly the normalised
    deformed operator. -/
noncomputable def torsionMajorana (y : ℝ) (s : ℂ) : Matrix I32 I32 ℂ :=
  (↑y)⁻¹ • (smDirac ↑y ↑y ↑y ↑y s - smDirac ↑y ↑y ↑y ↑y 0)

/-- The sign's first row (T1 target): row `⟨0⟩` of `etaSign y` is
    the unit row at column `⟨8⟩` — the flat operator's support and
    value, read off at the first index. -/
theorem etaSign_row0 (y : ℝ) (hy : y ≠ 0) (k : I32) :
    etaSign y ⟨0, by norm_num⟩ k
      = if k = ⟨8, by norm_num⟩ then 1 else 0 := by
  have hσ : sigmaIdx ⟨0, by norm_num⟩ = ⟨8, by norm_num⟩ :=
    Fin.ext rfl
  by_cases hk : k = ⟨8, by norm_num⟩
  · rw [if_pos hk, hk]
    unfold etaSign
    rw [Matrix.smul_apply]
    have hv := smDirac_flat_value y ⟨0, by norm_num⟩
    rw [hσ] at hv
    rw [hv]
    show ((y⁻¹ : ℝ) : ℂ) * ↑y = 1
    rw [Complex.ofReal_inv]
    exact inv_mul_cancel₀ (by exact_mod_cast hy)
  · rw [if_neg hk]
    have hz : smDirac ↑y ↑y ↑y ↑y 0 ⟨0, by norm_num⟩ k = 0 := by
      by_contra hc
      have h3 := smDirac_flat_support y ⟨0, by norm_num⟩ k hc
      exact hk (h3.trans hσ)
    unfold etaSign
    rw [Matrix.smul_apply, hz, smul_zero]

/-- The Majorana deformation lives only in the E blocks (T1
    target): along the line, `D(s) − D(0)` is `buildDirac 0 0 0
    (majoranaBlock s)` — the Yukawa and conjugate blocks cancel
    entrywise, leaving exactly the Majorana block and its
    conjugate transpose. -/
theorem deltaDirac_eq (y : ℝ) (s : ℂ) :
    smDirac ↑y ↑y ↑y ↑y s - smDirac ↑y ↑y ↑y ↑y 0
      = buildDirac 0 0 0 (majoranaBlock s) := by
  have hM0 : majoranaBlock 0 = 0 := by
    ext a b
    rw [Matrix.zero_apply]
    unfold majoranaBlock
    rw [Matrix.diagonal_apply]
    split_ifs <;> rfl
  ext i j
  unfold smDirac
  rw [hM0, Matrix.sub_apply]
  unfold buildDirac
  simp only []
  split_ifs <;>
    simp [majoranaBlock, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
      Matrix.conjTranspose_zero]

/-- The defect's witness entry is readable (T1 target): the
    Majorana correction at `(⟨8⟩, ⟨24⟩)` — the (ν_R, ν̄_R) slot —
    is `(↑y)⁻¹ * star s`, via the corpus's own `buildDirac_Edag_entry`
    and `majoranaBlock_val`. -/
theorem torsionMajorana_apply_8_24 (y : ℝ) (s : ℂ) :
    torsionMajorana y s ⟨8, by norm_num⟩ ⟨24, by norm_num⟩
      = (↑y)⁻¹ * star s := by
  unfold torsionMajorana
  rw [Matrix.smul_apply, deltaDirac_eq,
    buildDirac_Edag_entry 0 0 0 (majoranaBlock s)
      ⟨8, by norm_num⟩ ⟨24, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)]
  have h1 : (⟨8 - 8, by norm_num⟩ : Fin 8) = 0 := Fin.ext rfl
  have h2 : (⟨24 - 24, by norm_num⟩ : Fin 8) = 0 := Fin.ext rfl
  rw [h1, h2, Matrix.conjTranspose_apply, majoranaBlock_val]
  show ((y⁻¹ : ℝ) : ℂ) * star s = (↑y)⁻¹ * star s
  rw [Complex.ofReal_inv]

/-- **The defect, computed at one entry** (T1 target):
    `defect (etaSign y) (torsionMajorana y s) ⟨0⟩ ⟨24⟩
      = (↑y)⁻¹ * star s`.
    The `T * η₀` and `T * T` parts contribute nothing at this
    entry — every entry of T's row `⟨0⟩` vanishes (`hT0`), since
    the Majorana correction is supported on rows `⟨8⟩..⟨24⟩` —
    so the whole defect at the (ν_L, ν̄_R) corner is the
    anticommutator term `η₀ * T` at its witness entry. -/
theorem defect_entry (y : ℝ) (hy : y ≠ 0) (s : ℂ) :
    defect (etaSign y) (torsionMajorana y s) ⟨0, by norm_num⟩
        ⟨24, by norm_num⟩
      = (↑y)⁻¹ * star s := by
  have hT0 : ∀ k : I32, torsionMajorana y s ⟨0, by norm_num⟩ k = 0 := by
    intro k
    unfold torsionMajorana
    rw [Matrix.smul_apply, deltaDirac_eq]
    have hz : buildDirac 0 0 0 (majoranaBlock s) ⟨0, by norm_num⟩ k
        = 0 := by
      unfold buildDirac
      simp only []
      split_ifs <;> simp_all [majoranaBlock, Matrix.diagonal_apply] <;>
        try (intro a; exfalso; omega) <;> try (exfalso; omega)
    rw [hz, smul_zero]
  have hTX : ∀ X : Matrix I32 I32 ℂ,
      (torsionMajorana y s * X) ⟨0, by norm_num⟩ ⟨24, by norm_num⟩
        = 0 := by
    intro X
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    rw [hT0 k, zero_mul]
  unfold defect
  rw [Matrix.add_apply, Matrix.add_apply, hTX, hTX, add_zero, add_zero,
    Matrix.mul_apply]
  rw [Finset.sum_eq_single ⟨8, by norm_num⟩]
  · have hr := etaSign_row0 y hy ⟨8, by norm_num⟩
    rw [if_pos rfl] at hr
    rw [hr, torsionMajorana_apply_8_24, one_mul]
  · intro k _ hk
    have hr := etaSign_row0 y hy k
    rw [if_neg hk] at hr
    rw [hr, zero_mul]
  · intro hcon
    exact absurd (Finset.mem_univ _) hcon

/-- **Seat 2 survival verdict (T1 target): the Majorana line is
    flat exactly at its origin.** For `y ≠ 0`,
    `(etaSign y + torsionMajorana y s)² = 1 ↔ s = 0`. The forward
    direction reads the defect at the single entry `(⟨0⟩, ⟨24⟩)`,
    where it equals `(↑y)⁻¹ * star s` — nonzero for every `s ≠ 0`.
    Equivalently: the normalised deformed operator
    `(↑y)⁻¹ • D(s)` is an involution iff the Majorana block
    vanishes. In the sign seat, D_F's torsion is the Majorana
    block, and it does not survive. -/
theorem majorana_survival_iff (y : ℝ) (hy : y ≠ 0) (s : ℂ) :
    (etaSign y + torsionMajorana y s) * (etaSign y + torsionMajorana y s)
        = 1
      ↔ s = 0 := by
  constructor
  · intro h
    have hdef : defect (etaSign y) (torsionMajorana y s) = 0 :=
      (dirac_torsion_flat_iff _ _ (etaSign_sq y hy)).mp h
    have h0 : defect (etaSign y) (torsionMajorana y s)
        ⟨0, by norm_num⟩ ⟨24, by norm_num⟩ = 0 := by
      rw [hdef, Matrix.zero_apply]
    rw [defect_entry y hy s] at h0
    rcases mul_eq_zero.mp h0 with h1 | h2
    · exfalso
      have hne : (↑y : ℂ) ≠ 0 := by exact_mod_cast hy
      exact (inv_ne_zero hne) h1
    · exact star_eq_zero.mp h2
  · intro hs
    have hT : torsionMajorana y 0 = 0 := by
      unfold torsionMajorana
      simp
    rw [hs, hT, add_zero]
    exact etaSign_sq y hy

end ThetLogos
