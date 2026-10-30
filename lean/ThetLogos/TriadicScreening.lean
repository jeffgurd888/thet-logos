import ThetLogos.TriadicPin

/-!
# ThetLogos.TriadicScreening — P2: the XYZ screening wave (T1 screens over a T5 target)

Screening wave for the sector target `TriadicSectorExistence`
(`ThetLogos.TriadicPin`; dossier `whitepaper/xyz-triadic-pin-2026-10-17.md`,
§4). The target ranges over the named grid of 24 triples
`(genC, genH k, genM a)`, `k : Fin 3`, `a : Fin 8` — one member drawn from
each sector family `sectorC = {genC}`, `sectorH = Set.range genH`,
`sectorM = Set.range genM`.

What is proved here (Tier T1 throughout — machine-checked screening facts):

- §A: entry-level facts about the Gell-Mann squares (every `(gellMann a)²`
  is diagonal; for `a ≠ 7` its diagonal is 1 wherever `gellMann a` is
  nonzero).
- §B: the pin's first P2 sub-task — **every `genM a` with `a ≠ 7` is a
  tripotent** (`tripotent_genM_of_ne_seven`, with the six named
  corollaries `tripotent_genM1` … `tripotent_genM6`). Together with
  `tripotent_genM0` and `not_tripotent_genM7` (`XYZTripotents.lean`), the
  tripotence of `genM 1`–`genM 6` is thereby determined: all six hold.
- §C: the ℤ[i]-entry facts the R5 screen needs for the grid members.
- §D: the grid screen itself. The 21 triples with `a ≠ 7` are DEAD by R5
  (`sector_triple_misses_11`: all three members are ℤ[i]-valued, so the
  generated TRO misses `smGen 11`); the 3 triples with `a = 7` are DEAD
  because `genM 7` is not a tripotent. The uniform verdict is
  `sector_triple_dead` (all 24 triples), and since the sector families
  are exactly `{genC}`, `range genH`, `range genM`, the 24 verdicts
  assemble into `not_triadicSectorExistence` — a proved corollary of the
  screens, recorded as this wave's KILL outcome for the *sector*
  sharpening R3♯(sectors) only.

Fences, stated precisely:

- Open Problem 2 (`xyz_tripotents_exist`, `XYZTripotents.lean:489`)
  quantifies over **all** matrices and remains OPEN and untouched:
  nothing here depends on it, and no screen here constrains triples
  outside the named sector families (e.g. tripotents with non-ℤ[i]
  entries, which R5 cannot see). `TriadicSectorExistence` was the
  *restriction* of that statement to the named families; it is the
  restriction, not the problem, that the screens close.
- "DEAD" below always names its killing rule/theorem. No triple is
  ALIVE: a triple passing every screen would still not be existence,
  and in the event no grid triple passes.
-/

namespace ThetLogos

/-! ## §A. The Gell-Mann squares, entry by entry -/

/-- Every Gell-Mann square is diagonal: off-diagonal entries of
    `(gellMann a)²` vanish for all `a` (including `a = 7`, whose square
    is `(1/3)·diag(1, 1, 4)`). Tier T1. -/
theorem gellMann_sq_offdiag (a : Fin 8) (p q : Fin 3) (h : p ≠ q) :
    (gellMann a * gellMann a) p q = 0 := by
  fin_cases a <;> fin_cases p <;> fin_cases q <;>
    simp [gellMann, Matrix.mul_apply, Fin.sum_univ_three] at h ⊢

/-- Nonzero entries of `gellMann a` (`a ≠ 7`) sit where the square is
    1 on the diagonal: for `a ≠ 7`, `(gellMann a)²` is the 0/1 support
    projector of `gellMann a`. Tier T1. -/
theorem gellMann_sq_of_ne (a : Fin 8) (ha : a ≠ 7) (p q : Fin 3)
    (h : gellMann a p q ≠ 0) : (gellMann a * gellMann a) p p = 1 := by
  fin_cases a <;> fin_cases p <;> fin_cases q <;>
    simp_all [gellMann, Matrix.mul_apply, Fin.sum_univ_three]

/-! ## §B. Tripotence of `genM a` for `a ≠ 7` (the pin's first P2 sub-task) -/

/-- Support projector for `(genM a)²`: on each colour triplet it is the
    diagonal of the Gell-Mann square. Tier T2. -/
noncomputable def genMsupp (a : Fin 8) : I32 → ℂ := fun i =>
  match tripletOf i.val with
  | some (_, p) => (gellMann a * gellMann a) p p
  | none => 0

theorem genMsupp_eq (a : Fin 8) (i : I32) (t : Fin 4) (p : Fin 3)
    (h : tripletOf i.val = some (t, p)) :
    genMsupp a i = (gellMann a * gellMann a) p p := by
  unfold genMsupp
  rw [h]

theorem genMsupp_none (a : Fin 8) (i : I32) (h : tripletOf i.val = none) :
    genMsupp a i = 0 := by
  unfold genMsupp
  rw [h]

/-- `(genM a)²` is the diagonal triplet-support projector, for every
    `a`. (For `a = 7` the projector values are `1/3` and `4/3`, which is
    exactly what blocks tripotence in §B's support step.) Tier T1. -/
theorem genM_sq_diag (a : Fin 8) :
    genM a * genM a = Matrix.diagonal (genMsupp a) := by
  ext i j
  by_cases h : ∃ t : Fin 4, ∃ p q : Fin 3,
      tripletOf i.val = some (t, p) ∧ tripletOf j.val = some (t, q)
  · obtain ⟨t, p, q, hi, hj⟩ := h
    rw [genM_sq_onblock a i j t p q hi hj]
    by_cases hij : i = j
    · subst hij
      have hpq : p = q := congrArg Prod.snd (Option.some_inj.mp (hi.symm.trans hj))
      subst hpq
      rw [Matrix.diagonal_apply_eq, genMsupp_eq a i t p hi]
    · have h0 : (gellMann a * gellMann a) p q = 0 := by
        by_cases hpq : p = q
        · subst hpq
          have hii : i = tripletIdx t p := tripletOf_inv i t p hi
          have hjj : j = tripletIdx t p := tripletOf_inv j t p hj
          exact absurd (hii.trans hjj.symm) hij
        · exact gellMann_sq_offdiag a p q hpq
      rw [h0, Matrix.diagonal_apply_ne _ hij]
  · have hLHS : (genM a * genM a) i j = 0 := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro l _
      by_cases g1 : genM a i l = 0
      · rw [g1, zero_mul]
      · by_cases g2 : genM a l j = 0
        · rw [g2, mul_zero]
        · exfalso
          obtain ⟨t1, p1, q1, h1i, h1l⟩ := genM_supp_triplet a i l g1
          obtain ⟨t2, p2, q2, h2l, h2j⟩ := genM_supp_triplet a l j g2
          have htt : t1 = t2 :=
            congrArg Prod.fst (Option.some_inj.mp (h1l.symm.trans h2l))
          subst htt
          exact h ⟨t1, p1, q2, h1i, h2j⟩
    rw [hLHS]
    by_cases hij : i = j
    · subst hij
      have hnone : tripletOf i.val = none := by
        cases hto : tripletOf i.val with
        | none => rfl
        | some tp =>
          obtain ⟨t, p⟩ := tp
          exact absurd ⟨t, p, p, hto, hto⟩ h
      rw [Matrix.diagonal_apply_eq, genMsupp_none a i hnone]
    · rw [Matrix.diagonal_apply_ne _ hij]

/-- Every M-sector generator except `genM 7` is a tripotent: the
    Hermitian-square-projector route of `tripotent_genM0`, uniform in
    `a ≠ 7`. Tier T1. -/
theorem tripotent_genM_of_ne_seven (a : Fin 8) (ha : a ≠ 7) :
    Tripotent (genM a) := by
  refine tripotent_of_hermitian_sq_proj (genM_herm a) (genM_sq_diag a) ?_
  intro i j hne
  obtain ⟨t, p, q, hi, hj⟩ := genM_supp_triplet a i j hne
  rw [genMsupp_eq a i t p hi]
  have h2 : genM a i j = gellMann a p q := genM_apply_eq a i j t p q hi hj
  rw [h2] at hne
  exact gellMann_sq_of_ne a ha p q hne

/-- `genM 1` is a tripotent. Tier T1. -/
theorem tripotent_genM1 : Tripotent (genM 1) :=
  tripotent_genM_of_ne_seven 1 (by decide)

/-- `genM 2` is a tripotent. Tier T1. -/
theorem tripotent_genM2 : Tripotent (genM 2) :=
  tripotent_genM_of_ne_seven 2 (by decide)

/-- `genM 3` is a tripotent. Tier T1. -/
theorem tripotent_genM3 : Tripotent (genM 3) :=
  tripotent_genM_of_ne_seven 3 (by decide)

/-- `genM 4` is a tripotent. Tier T1. -/
theorem tripotent_genM4 : Tripotent (genM 4) :=
  tripotent_genM_of_ne_seven 4 (by decide)

/-- `genM 5` is a tripotent. Tier T1. -/
theorem tripotent_genM5 : Tripotent (genM 5) :=
  tripotent_genM_of_ne_seven 5 (by decide)

/-- `genM 6` is a tripotent. Tier T1. -/
theorem tripotent_genM6 : Tripotent (genM 6) :=
  tripotent_genM_of_ne_seven 6 (by decide)

/-! ## §C. ℤ[i]-entry facts for the grid members -/

/-- The C-sector generator is ℤ[i]-valued: its entries are `I` or `0`.
    Tier T1. -/
theorem genC_gaussInt (i j : I32) : IsGaussInt (genC i j) := by
  by_cases h : i = j
  · subst h
    rw [genC_diag_val]
    split_ifs <;> first | exact gaussInt_I | exact gaussInt_zero
  · rw [genC_apply_ne h]
    exact gaussInt_zero

/-- The Gell-Mann matrices `gellMann a` with `a ≠ 7` are ℤ[i]-valued:
    their entries lie in `{0, ±1, ±I}`. (Only `gellMann 7` leaves
    ℤ[i], via `1/√3`.) Tier T1. -/
theorem gellMann_gaussInt_of_ne_seven (a : Fin 8) (ha : a ≠ 7) (p q : Fin 3) :
    IsGaussInt (gellMann a p q) := by
  fin_cases a <;> fin_cases p <;> fin_cases q <;>
    simp_all [gellMann, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.smul_apply] <;>
    first
      | exact gaussInt_zero
      | exact gaussInt_one
      | exact gaussInt_neg_one
      | exact gaussInt_I
      | exact gaussInt_neg_I

/-- The M-sector generators `genM a` with `a ≠ 7` are ℤ[i]-valued.
    Tier T1. -/
theorem genM_gaussInt_of_ne_seven (a : Fin 8) (ha : a ≠ 7) (i j : I32) :
    IsGaussInt (genM a i j) := by
  unfold genM
  cases h1 : tripletOf i.val with
  | none =>
    cases h2 : tripletOf j.val with
    | none => simp only [gaussInt_zero]
    | some tp2 => simp only [gaussInt_zero]
  | some tp1 =>
    obtain ⟨t1, p1⟩ := tp1
    cases h2 : tripletOf j.val with
    | none => simp only [gaussInt_zero]
    | some tp2 =>
      obtain ⟨t2, p2⟩ := tp2
      simp only []
      by_cases heq : t1 = t2
      · rw [if_pos heq]; exact gellMann_gaussInt_of_ne_seven a ha p1 p2
      · rw [if_neg heq]; exact gaussInt_zero

/-! ## §D. The grid screen: all 24 triples are DEAD -/

/-- R5 screen, uniform in the grid: a sector triple with `a ≠ 7`
    provably misses `smGen 11 = genM 7`, because all three members are
    ℤ[i]-valued (`genC_gaussInt`, `genH_gaussInt`,
    `genM_gaussInt_of_ne_seven`). Tier T1. -/
theorem sector_triple_misses_11 (k : Fin 3) (a : Fin 8) (ha : a ≠ 7) :
    ¬ MemGenTRO ({genC, genH k, genM a} : Set (Matrix I32 I32 ℂ)) (smGen 11) :=
  no_gaussInt_triple_reaches_genM7 genC (genH k) (genM a)
    (fun i j => genC_gaussInt i j)
    (fun i j => genH_gaussInt k i j)
    (fun i j => genM_gaussInt_of_ne_seven a ha i j)

/-- Scoreboard side of the same screen: every grid triple reaches its
    own three members by membership. (What it provably cannot do is
    reach all twelve — see `sector_triple_dead`.) Tier T1. -/
theorem sector_triple_reaches_members (k : Fin 3) (a : Fin 8) :
    MemGenTRO ({genC, genH k, genM a} : Set (Matrix I32 I32 ℂ)) genC ∧
    MemGenTRO ({genC, genH k, genM a} : Set (Matrix I32 I32 ℂ)) (genH k) ∧
    MemGenTRO ({genC, genH k, genM a} : Set (Matrix I32 I32 ℂ)) (genM a) :=
  ⟨MemGenTRO.of_mem _ (by simp), MemGenTRO.of_mem _ (by simp),
   MemGenTRO.of_mem _ (by simp)⟩

/-- The uniform grid verdict: **no** named sector triple is a
    tripotent triple generating all twelve `smGen`. For `a = 7` the
    third member is not a tripotent (`not_tripotent_genM7`); for
    `a ≠ 7` the triple is ℤ[i]-valued and misses `smGen 11`
    (`sector_triple_misses_11`, rule R5). Tier T1. -/
theorem sector_triple_dead (k : Fin 3) (a : Fin 8) :
    ¬ (Tripotent genC ∧ Tripotent (genH k) ∧ Tripotent (genM a) ∧
        ∀ g : Fin 12, MemGenTRO ({genC, genH k, genM a} :
          Set (Matrix I32 I32 ℂ)) (smGen g)) := by
  rintro ⟨-, -, hZ, hgen⟩
  by_cases ha : a = 7
  · subst ha
    exact not_tripotent_genM7 hZ
  · exact sector_triple_misses_11 k a ha (hgen 11)

/-- Assembly of the 24 verdicts: the sector sharpening
    `TriadicSectorExistence` (R3♯(sectors)) is **refuted**. A witness
    would have to be one of the 24 grid triples — `sectorC` is the
    singleton `{genC}`, `sectorH`/`sectorM` are the ranges of `genH`/
    `genM` — and `sector_triple_dead` kills each one. This closes the
    *sector restriction* of Open Problem 2 only; the unrestricted
    statement `xyz_tripotents_exist` remains open (see the module
    header). Tier T1. -/
theorem not_triadicSectorExistence : ¬ TriadicSectorExistence := by
  intro h
  unfold TriadicSectorExistence at h
  obtain ⟨X, hX, Y, hY, Z, hZ, hTX, hTY, hTZ, hgen⟩ := h
  simp only [sectorC, Set.mem_singleton_iff] at hX
  simp only [sectorH, Set.mem_range] at hY
  simp only [sectorM, Set.mem_range] at hZ
  obtain ⟨k, hk⟩ := hY
  obtain ⟨a, ha⟩ := hZ
  subst hX
  subst hk
  subst ha
  exact sector_triple_dead k a ⟨hTX, hTY, hTZ, hgen⟩

end ThetLogos
