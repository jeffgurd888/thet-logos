import Mathlib.Tactic
import ThetLogos.Scaffold32
import ThetLogos.FiniteSpectralTriple
import ThetLogos.ThreeGen

/-!
# ThetLogos.SMFermions — three-generation SM fermion quantum numbers (SM-Match Track 2)

After: Gurd, *The Ontological Thet–LOGOS Framework* (Revised Draft, Nexus
Research, Sept 2026); SM-Match program dossier `whitepaper/sm-match-2026-10-11.md`.

**Honesty boundary (read first).**
* "Match" means the formalized table coincides with the Standard Model's known
  fermion assignments — same hypercharges, isospins, color reps, charges.
* **Hypercharge assignments are INPUTS (Tier T2), not derived.** Nothing here
  derives Y from thet primitives; the values are the SM's known ones, recorded
  so the machine can check internal consistency (Q = T³ + Y/2, chirality
  sectors, the embedSM index scheme).
* Generation replication is IMPOSED (Tier T2), not derived — matching
  `ThreeGen.lean`'s convention π₃ = π ⊗ I₃.
* Yukawa values: untouched (`satisfiesDestruction`); no masses, couplings, or
  mixing angles appear.
* No physical predictions beyond the structural table.

Tier map in this file:
* T2 (inputs): `SMFermion`, `hypercharge`, `weakIsospin`, `ColorRep`,
  `colorRep`, `electricCharge`, `fermionIndex`, `fermionIndex3`,
  the `*3` generation-blind wrappers.
* T1 (proved): `charge_consistency`, `charge_table_explicit`,
  `fermionIndex_sector`, `fermionIndex_partner`, `fermionIndex_lt16`,
  `quark_index_scheme`, `lepton_index_slots`, `lepton_color_blind_*`,
  `quark_color_injective_*`, `embedSM_lepton_doublet`, `lepton_index_embedSM`,
  `embedSM_quark_diag`, `replication_imposed`, `fermionIndex3_proj`,
  `fermionIndex3_particle_block`, and the priced color-action corollary
  `color_triplet_priced` (from the proved `pi_pure_color_zero`).
-/

namespace ThetLogos

/-- The 8 one-generation fermion types of the Standard Model. Tier T2 (input). -/
inductive SMFermion : Type
  | nuL | eL | uL | dL | nuR | eR | uR | dR
  deriving DecidableEq, Repr

/-- Weak hypercharge Y, in the convention Q = T³ + Y/2.
    **INPUT (Tier T2): hypercharge assignments are NOT derived here.** -/
def hypercharge : SMFermion → ℚ
  | .nuL => -1 | .eL => -1 | .uL => 1/3 | .dL => 1/3
  | .nuR => 0  | .eR => -2 | .uR => 4/3 | .dR => -2/3

/-- Third component of weak isospin. **INPUT (Tier T2).** -/
def weakIsospin : SMFermion → ℚ
  | .nuL => 1/2  | .eL => -1/2 | .uL => 1/2  | .dL => -1/2
  | .nuR => 0    | .eR => 0    | .uR => 0    | .dR => 0

/-- Color representation of a fermion type. Tier T2 (input). -/
inductive ColorRep : Type
  | triplet
  | singlet
  deriving DecidableEq, Repr

/-- Quarks are color triplets, leptons color singlets. **INPUT (Tier T2).**
    Priced caveat: the Option-A representation kills the M₃(ℂ) summand
    (`pi_pure_color_zero`), so the full SU(3) color action is NOT represented —
    only the color-diagonal factor inside the quark block survives. The
    "triplet" label is the SM structural input; see `color_triplet_priced`. -/
def colorRep : SMFermion → ColorRep
  | .nuL => .singlet | .eL => .singlet | .uL => .triplet | .dL => .triplet
  | .nuR => .singlet | .eR => .singlet | .uR => .triplet | .dR => .triplet

/-- Electric charge Q. **INPUT (Tier T2)** — the SM's known charges;
    `charge_consistency` checks Q = T³ + Y/2 for all 8 types. -/
def electricCharge : SMFermion → ℚ
  | .nuL => 0 | .eL => -1 | .uL => 2/3 | .dL => -1/3
  | .nuR => 0 | .eR => -1 | .uR => 2/3 | .dR => -1/3

/-- **T1 (proved):** Q = T³ + Y/2 reproduces the input charge table for all 8
    one-generation fermion types. A consistency check of the recorded SM
    table — not a derivation of hypercharge. -/
theorem charge_consistency (f : SMFermion) :
    electricCharge f = weakIsospin f + hypercharge f / 2 := by
  cases f <;> norm_num [hypercharge, weakIsospin, electricCharge]

/-- Explicit charge table, by rfl from the input definitions. Tier T1. -/
theorem charge_table_explicit :
    electricCharge .nuL = 0 ∧ electricCharge .eL = -1 ∧
    electricCharge .uL = 2/3 ∧ electricCharge .dL = -1/3 ∧
    electricCharge .nuR = 0 ∧ electricCharge .eR = -1 ∧
    electricCharge .uR = 2/3 ∧ electricCharge .dR = -1/3 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Index mapping onto the `embedSM` Option-A convention -/

/-- One-generation particle-block index for each fermion type and color label,
    following the `embedSM` Option-A convention (see the `embedSM` docstring in
    `FiniteSpectralTriple.lean` and the sector enumeration in `Scaffold32.lean`):
    H_L: ν_L→0, e_L→1, u_L(c)→2+2c, d_L(c)→3+2c;
    H_R: ν_R→8, e_R→9, u_R(c)→10+2c, d_R(c)→11+2c.
    Tier T2 (convention, matching the documented enumeration). -/
def fermionIndex : SMFermion → Fin 3 → I32
  | .nuL, _ => ⟨0, by omega⟩
  | .eL, _ => ⟨1, by omega⟩
  | .uL, c => ⟨2 + 2 * c.val, by have h := c.isLt; omega⟩
  | .dL, c => ⟨3 + 2 * c.val, by have h := c.isLt; omega⟩
  | .nuR, _ => ⟨8, by omega⟩
  | .eR, _ => ⟨9, by omega⟩
  | .uR, c => ⟨10 + 2 * c.val, by have h := c.isLt; omega⟩
  | .dR, c => ⟨11 + 2 * c.val, by have h := c.isLt; omega⟩

/-- Plain-ℕ unfolding of `fermionIndex`, for arithmetic proofs. Tier T2. -/
def fermionIndexVal : SMFermion → Fin 3 → ℕ
  | .nuL, _ => 0
  | .eL, _ => 1
  | .uL, c => 2 + 2 * c.val
  | .dL, c => 3 + 2 * c.val
  | .nuR, _ => 8
  | .eR, _ => 9
  | .uR, c => 10 + 2 * c.val
  | .dR, c => 11 + 2 * c.val

/-- The index value is the documented ℕ expression. Tier T1. -/
theorem fermionIndex_val (f : SMFermion) (c : Fin 3) :
    (fermionIndex f c).val = fermionIndexVal f c := by
  cases f <;> rfl

/-- Chirality label of the fermion type. Tier T2. -/
def isLeft : SMFermion → Bool
  | .nuL => true | .eL => true | .uL => true | .dL => true
  | .nuR => false | .eR => false | .uR => false | .dR => false

/-- **T1:** the table's chirality assignment matches the index sectors:
    left-handed types land in H_L (indices < 8), right-handed in H_R. -/
theorem fermionIndex_sector (f : SMFermion) (c : Fin 3) :
    (fermionIndex f c).val < 8 ↔ isLeft f = true := by
  have hc := c.isLt
  rw [fermionIndex_val]
  cases f <;> simp [fermionIndexVal, isLeft] <;> omega

/-- **T1:** every particle index lies below 16, so `partner` sends it to the
    antiparticle block (indices 16–31), per the `Scaffold32` sector map. -/
theorem fermionIndex_lt16 (f : SMFermion) (c : Fin 3) :
    (fermionIndex f c).val < 16 := by
  have hc := c.isLt
  rw [fermionIndex_val]
  cases f <;> simp [fermionIndexVal] <;> omega

/-- **T1:** the antiparticle partner of a particle index is index + 16. -/
theorem fermionIndex_partner (f : SMFermion) (c : Fin 3) :
    (partner (fermionIndex f c)).val = (fermionIndex f c).val + 16 := by
  rw [partner_val_eq]
  simp only [fermionIndex_lt16 f c, ↓reduceIte]

/-- **T1:** the quark indices follow the documented (s, c) scheme —
    index 2+2c+s with s ∈ {0,1} isospin, c ∈ {0,1,2} color (H_L), and
    10+2c+s on H_R — matching the `Scaffold32` partner docstring. -/
theorem quark_index_scheme (c : Fin 3) :
    (fermionIndex .uL c).val = 2 + 2 * c.val ∧
    (fermionIndex .dL c).val = 3 + 2 * c.val ∧
    (fermionIndex .uR c).val = 10 + 2 * c.val ∧
    (fermionIndex .dR c).val = 11 + 2 * c.val :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **T1:** the lepton slots of the Option-A enumeration. -/
theorem lepton_index_slots (c : Fin 3) :
    (fermionIndex .nuL c).val = 0 ∧ (fermionIndex .eL c).val = 1 ∧
    (fermionIndex .nuR c).val = 8 ∧ (fermionIndex .eR c).val = 9 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **T1:** the color label is inert for leptons (they are singlets). -/
theorem lepton_color_blind_nuL (c1 c2 : Fin 3) :
    fermionIndex .nuL c1 = fermionIndex .nuL c2 := rfl

/-- **T1:** the color label is inert for leptons (they are singlets). -/
theorem lepton_color_blind_eL (c1 c2 : Fin 3) :
    fermionIndex .eL c1 = fermionIndex .eL c2 := rfl

/-- **T1:** the color label is inert for leptons (they are singlets). -/
theorem lepton_color_blind_nuR (c1 c2 : Fin 3) :
    fermionIndex .nuR c1 = fermionIndex .nuR c2 := rfl

/-- **T1:** the color label is inert for leptons (they are singlets). -/
theorem lepton_color_blind_eR (c1 c2 : Fin 3) :
    fermionIndex .eR c1 = fermionIndex .eR c2 := rfl

/-- **T1:** the three color labels give three distinct indices for u_L —
    the triplet genuinely has dimension 3 in the index scheme. -/
theorem quark_color_injective_uL : Function.Injective (fermionIndex .uL) := by
  intro c1 c2 h
  have h1 := c1.isLt; have h2 := c2.isLt
  have hv := congrArg Fin.val h
  rw [fermionIndex_val, fermionIndex_val] at hv
  simp only [fermionIndexVal] at hv
  rw [Fin.ext_iff]
  omega

/-- **T1:** the three color labels give three distinct indices for d_L. -/
theorem quark_color_injective_dL : Function.Injective (fermionIndex .dL) := by
  intro c1 c2 h
  have h1 := c1.isLt; have h2 := c2.isLt
  have hv := congrArg Fin.val h
  rw [fermionIndex_val, fermionIndex_val] at hv
  simp only [fermionIndexVal] at hv
  rw [Fin.ext_iff]
  omega

/-- **T1:** the three color labels give three distinct indices for u_R. -/
theorem quark_color_injective_uR : Function.Injective (fermionIndex .uR) := by
  intro c1 c2 h
  have h1 := c1.isLt; have h2 := c2.isLt
  have hv := congrArg Fin.val h
  rw [fermionIndex_val, fermionIndex_val] at hv
  simp only [fermionIndexVal] at hv
  rw [Fin.ext_iff]
  omega

/-- **T1:** the three color labels give three distinct indices for d_R. -/
theorem quark_color_injective_dR : Function.Injective (fermionIndex .dR) := by
  intro c1 c2 h
  have h1 := c1.isLt; have h2 := c2.isLt
  have hv := congrArg Fin.val h
  rw [fermionIndex_val, fermionIndex_val] at hv
  simp only [fermionIndexVal] at hv
  rw [Fin.ext_iff]
  omega

/-! ## Consistency with the represented algebra action -/

/-- **T1:** on the lepton doublet slots, `embedSM` reads exactly the
    quaternionic factor `a.q` — indices 0,1 of the particle block are the
    (ν_L, e_L) doublet acted on by ℍ. -/
theorem embedSM_lepton_doublet (a : AF) (i j : Fin 2) :
    embedSM a ⟨i.val, by have h := i.isLt; omega⟩
               ⟨j.val, by have h := j.isLt; omega⟩ = a.q i j := by
  have hi := i.isLt; have hj := j.isLt
  unfold embedSM
  dsimp only
  split_ifs with hL hl hR h1 h2 hq
  · rfl
  all_goals omega

/-- **T1:** the table's lepton indices sit on the quaternionic doublet:
    slot (ν_L, e_L) = matrix entry a.q₀₁. -/
theorem lepton_index_embedSM (a : AF) :
    embedSM a ⟨(fermionIndex .nuL 0).val, by decide⟩
               ⟨(fermionIndex .eL 0).val, by decide⟩ = a.q 0 1 :=
  embedSM_lepton_doublet a 0 1

/-- **T1:** on the quark-block diagonal, `embedSM` reads the color-diagonal
    factor `a.q s s * a.color c c` for isospin slot s and color c.
    This is the represented (color-diagonal) remnant of the triplet action —
    the full SU(3) is priced out by `color_triplet_priced` below. -/
theorem embedSM_quark_diag (a : AF) (s : Fin 2) (c : Fin 3) :
    embedSM a ⟨2 + 2 * c.val + s.val, by have h1 := c.isLt; have h2 := s.isLt; omega⟩
               ⟨2 + 2 * c.val + s.val, by have h1 := c.isLt; have h2 := s.isLt; omega⟩
      = a.q s s * a.color c c := by
  have hc := c.isLt; have hs := s.isLt
  have e1 : (2 + 2 * c.val + s.val - 2) % 2 = s.val := by omega
  have e2 : (2 + 2 * c.val + s.val - 2) / 2 = c.val := by omega
  have hLL : (2 + 2 * c.val + s.val) < 8 ∧ (2 + 2 * c.val + s.val) < 8 :=
    ⟨by omega, by omega⟩
  have hnotl : ¬ ((2 + 2 * c.val + s.val) < 2 ∧ (2 + 2 * c.val + s.val) < 2) := by
    omega
  have hQ : 2 ≤ (2 + 2 * c.val + s.val) ∧ 2 ≤ (2 + 2 * c.val + s.val) :=
    ⟨by omega, by omega⟩
  have fi : (⟨(2 + 2 * c.val + s.val - 2) % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2)
      = s := by
    rw [Fin.ext_iff]; exact e1
  have fc : (⟨(2 + 2 * c.val + s.val - 2) / 2, by omega⟩ : Fin 3) = c := by
    rw [Fin.ext_iff]; exact e2
  -- The facts hLL/hnotl/hQ let `split_ifs` discharge every contradictory
  -- branch by assumption, leaving only the H_L quark-block case.
  unfold embedSM
  dsimp only
  split_ifs
  · rw [fi, fc]

/-- **T1 (priced obstruction):** a pure-color algebra element acts trivially in
    the Option-A representation (corollary of the proved `pi_pure_color_zero`).
    Consequence: the color-triplet structure of quarks is NOT represented by
    the finite algebra's π — full SU(3) color lives in the algebra ℂ⊕ℍ⊕M₃(ℂ)
    (SM-Match Track 1), not in its Option-A representation. The "triplet" label
    in this file is the SM structural input; the represented remnant is the
    color-diagonal factor of `embedSM_quark_diag`. -/
theorem color_triplet_priced (m : Matrix I3 I3 ℂ) (i j : I32) :
    pi ⟨0, 0, m⟩ i j = 0 := by
  rw [pi_pure_color_zero]
  rfl

/-! ## Three-generation triplication (imposed, Tier T2) -/

/-- Three-generation hypercharge: generation-blind by imposition. Tier T2. -/
def hypercharge3 (f : SMFermion) (_ : Fin 3) : ℚ := hypercharge f

/-- Three-generation weak isospin: generation-blind by imposition. Tier T2. -/
def weakIsospin3 (f : SMFermion) (_ : Fin 3) : ℚ := weakIsospin f

/-- Three-generation electric charge: generation-blind by imposition. Tier T2. -/
def electricCharge3 (f : SMFermion) (_ : Fin 3) : ℚ := electricCharge f

/-- Three-generation color rep: generation-blind by imposition. Tier T2. -/
def colorRep3 (f : SMFermion) (_ : Fin 3) : ColorRep := colorRep f

/-- Three-generation index on `I96 = I32 × Fin 3`, per the `ThreeGen.lean`
    convention: the pair `(i, g)` is the 32-index `i` in generation `g`.
    Generation replication is **IMPOSED (T2), not derived** — matching
    `smGen3` / `smDirac3diag` = (·) ⊗ I₃. -/
def fermionIndex3 (f : SMFermion) (c g : Fin 3) : I96 := (fermionIndex f c, g)

/-- Antiparticle partner index in generation `g` (T2 convention, via `partner`). -/
def fermionIndex3bar (f : SMFermion) (c g : Fin 3) : I96 :=
  (partner (fermionIndex f c), g)

/-- **T1:** generation replication is imposed — the whole table is
    generation-blind. This is the formal "not derived" stamp. -/
theorem replication_imposed (f : SMFermion) (g : Fin 3) :
    hypercharge3 f g = hypercharge f ∧ weakIsospin3 f g = weakIsospin f ∧
      electricCharge3 f g = electricCharge f ∧ colorRep3 f g = colorRep f :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **T1:** the 3-gen index projects to the 1-gen index and the generation. -/
theorem fermionIndex3_proj (f : SMFermion) (c g : Fin 3) :
    (fermionIndex3 f c g).1 = fermionIndex f c ∧ (fermionIndex3 f c g).2 = g :=
  ⟨rfl, rfl⟩

/-- **T1:** three-generation particle indices stay in the particle block
    (< 16), matching the support of `pi` (`pi_zero_of_ge_16`) and the
    `smGen3` = π ⊗ I₃ convention. -/
theorem fermionIndex3_particle_block (f : SMFermion) (c g : Fin 3) :
    (fermionIndex3 f c g).1.val < 16 :=
  fermionIndex_lt16 f c

end ThetLogos
