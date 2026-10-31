import ThetLogos.Census96FortySixBound
import ThetLogos.Census96PairBound

/-!
# ThetLogos.Census96Assembly - C96-4: the 402 assembly

Final brick of the Census-96 line (packs `pack-c96-4.md`; gates C96-1,
C96-2b, C96-3b2 all FULL). Two discharges and nothing else:

1. **The 402.** `finrank_census96Sol_eq` / `census96_proved`:
   the landed decoupling equiv `census96SolEquiv` reduces the census
   to the finrank of `(Fin 3 -> Sol32) x (GenPair -> Census96PairSol)`;
   finrank additivity over products and pi types, with
   `Fintype.card (Fin 3) = 3`, `card_genPair = 3`,
   `finrank_sol32_eq = 46` (C96-2b) and `finrank_pairSpace_eq = 88`
   (C96-3b2, of `PairSpace`, which is `Census96PairSol` by its landed
   definition), gives 3*46 + 3*88 = 138 + 264 = 402. This is the
   equiv + additivity route only (K-C96-2 guard): no unfolding of
   the 2352-side admissible bookkeeping. On the face: **402, NOT
   414** (the mixing pair contributes 88, not 92).

2. **The diagonal pin.** `census96Diag_proved`: `Diag96Sol` is the
   `smDirac3diagLM` image of `Sol32`; `smDirac3diagLM` is injective
   (its (g, g) generation block is the source matrix itself), so the
   image has the source's finrank, 46. FENCE: this is the
   flavour-diagonal corollary, NOT the census, NOT evidence for the
   402 beyond the shared 46.

## What this discharge promotes

The T4 note in `ThreeGen.lean`'s header (per-diagonal nullity 46,
per-mixing-pair nullity 88, total 402, from the Python census
`attack4_3gen.py`) is promoted by this discharge: the note becomes
a proved theorem. Exactly that, no more. The Python counterpart is
registered as BRIDGE-1 entry BR1-015 (numerical rank computation,
T4 probe; this module is the Lean counterpart).

## Fences

Generations IMPOSED; CKM/PMNS input-only; no flavour quantity is
derived; posted question Q3 (generations) OPEN regardless of
outcome; NO CLAIM; dials 0/4. The old 46 -> 10 gloss is UNSOUND AS
STATED and is never cited.
-/

open Matrix

namespace ThetLogos

/-! ## 1. The 402 assembly -/

/-- The pair factor's finrank is 88: `finrank_pairSpace_eq` is stated
    for `PairSpace`, and `PairSpace` is `Census96PairSol` by its
    landed definition in `Census96PairSpace.lean`. -/
theorem finrank_pairSol_eq : Module.finrank ℝ Census96PairSol = 88 :=
  finrank_pairSpace_eq

/-- Diagonal sector: three copies of the one-generation 46. -/
theorem finrank_pi_sol32_eq :
    Module.finrank ℝ (Fin 3 → Sol32) = 3 * 46 := by
  rw [Module.finrank_pi_fintype]
  simp [finrank_sol32_eq]

/-- Pair sector: three generation pairs at 88 each. -/
theorem finrank_pi_pairSol_eq :
    Module.finrank ℝ (GenPair → Census96PairSol) = 3 * 88 := by
  rw [Module.finrank_pi_fintype]
  simp [finrank_pairSol_eq, card_genPair]

/-- **The census number.** The real dimension of the order-one
    solution space `Census96Sol` is 402 = 3*46 + 3*88, by the
    decoupling equiv and finrank additivity over the two proved
    sector numbers. NOT 414. -/
theorem finrank_census96Sol_eq : Module.finrank ℝ Census96Sol = 402 := by
  have h1 := census96SolEquiv.finrank_eq
  rw [Module.finrank_prod, finrank_pi_sol32_eq, finrank_pi_pairSol_eq] at h1
  rw [h1]

/-- **CENSUS-96, discharged.** The pinned statement `Census96`
    (`finrank ℝ Census96Sol = 402`) is proved. The T4 note becomes
    a proved theorem; generations remain IMPOSED, Q3 OPEN,
    NO CLAIM, dials 0/4. -/
theorem census96_proved : Census96 :=
  finrank_census96Sol_eq

/-! ## 2. The flavour-diagonal pin -/

/-- **Block extraction:** the `(g, g)` generation block of the
    flavour-diagonal triplication is the source matrix itself. -/
theorem genBlock_smDirac3diag_diag (D : Matrix I32 I32 ℂ) (g : Fin 3) :
    genBlock (smDirac3diag D) g g = D := by
  ext i j
  simp [genBlock, smDirac3diag]

/-- `smDirac3diagLM` is injective: if the triplications agree, their
    `(0, 0)` generation blocks agree, and those blocks are the
    sources. -/
theorem smDirac3diagLM_injective : Function.Injective smDirac3diagLM := by
  intro D1 D2 h
  have h2 : smDirac3diag D1 = smDirac3diag D2 := h
  have h3 := congrArg (fun M => genBlock M 0 0) h2
  rwa [genBlock_smDirac3diag_diag, genBlock_smDirac3diag_diag] at h3

/-- The transported map out of `Sol32` is injective. -/
theorem diagMap_injective :
    Function.Injective (smDirac3diagLM.comp Sol32.subtype) := by
  intro a b h
  have h2 : smDirac3diagLM a.1 = smDirac3diagLM b.1 := h
  exact Subtype.ext (smDirac3diagLM_injective h2)

/-- The diagonal solution space has finrank 46: it is the image of
    `Sol32` under an injective linear map. -/
theorem finrank_diag96Sol_eq : Module.finrank ℝ Diag96Sol = 46 := by
  have hmap : LinearMap.range (smDirac3diagLM.comp Sol32.subtype)
      = Diag96Sol := by
    ext x
    simp only [LinearMap.mem_range, LinearMap.comp_apply, Diag96Sol,
      Submodule.mem_map]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y.1, y.2, hy⟩
    · rintro ⟨y, hy, hfy⟩
      exact ⟨⟨y, hy⟩, hfy⟩
  have e := (LinearEquiv.ofInjective _ diagMap_injective).finrank_eq
  rw [hmap, finrank_sol32_eq] at e
  exact e.symm

/-- **CENSUS-96-DIAG, discharged (fenced).** The pinned statement
    `Census96Diag` (`finrank ℝ Diag96Sol = 46`) is proved. This is
    the flavour-diagonal corollary of the one-generation 46 - NOT
    the census, NOT evidence for the 402 beyond the shared 46. -/
theorem census96Diag_proved : Census96Diag :=
  finrank_diag96Sol_eq

end ThetLogos
