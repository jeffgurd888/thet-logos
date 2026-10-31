import ThetLogos.Census96Decoupling
import ThetLogos.CFKernel22

/-!
# ThetLogos.Census96PairSpace - C96-3a: the mixing-pair space P and its directions

First half of C96-3 (THE 88 THEOREM), lane 2 of the Census-96 line
(scoping memo `scoping-census96-2026-10-30.md` section C96-3; pack
`pack-c96-3a.md`). The interface C96-0 / C96-1 / C96-1b is FROZEN and
untouched; every name defined here is new.

## What this module does

1. **The pair space.** C96-1's landed pair vocabulary already
   determines the mixing-pair space: `Census96PairSol`
   (`Census96Decoupling.lean` section 10) is the space of single
   off-diagonal blocks `M` whose self-adjoint pair `(M, M-dagger)` has
   both members block-admissible (`IsAdmBlock`) and both satisfying
   the one-generation order-one condition. Per the pack's instruction
   ("if the landed names already determine the space, define P as that
   space with its characterization proved"), `PairSpace` below IS
   `Census96PairSol`, with the membership characterization stated and
   proved as `mem_pairSpace_iff`. No parallel space is invented.
   C96-3b takes `finrank` of exactly this object.

2. **Pair-coupling lemmas (SA + J) for a pair in isolation.** The
   self-adjoint coupling (the partner block is `M-dagger`, an
   involution, entrywise `star (M j i)`) and the J coupling (the
   partner block at the J-mirrored entry `(partner j, partner i)`
   equals `M i j`), plus grading-odd vanishing for both members, and
   the isolation theorem `pairSpace_isolation`: a single pair, with
   zero diagonal data and zero other pairs, assembles via the landed
   `census96Backward` to a global element of `Census96Sol` whose two
   blocks at that generation pair are exactly `M` and `M-dagger`.

3. **Directions (PARTIAL - stall named).** The hermitian sector of P
   is reached by `pairSpace_of_isAdm32`: every one-generation
   admissible order-one block `D` (i.e. every element of `Sol32`)
   embeds in P, because under self-adjointness the entrywise-conj
   J-form of `IsAdmBlock` is the owned transpose form. This lands the
   22 hermitian directions owned by `CFKernel22` (`dirs22`: 10 SM +
   12 exotic) as explicit elements of P: `pairDir22`, with the SM
   subfamily `pairDirSM` (Fin 10) and the exotic subfamily
   `pairDirExotic` (Fin 12). The concatenation combinator `dir88Of`
   assembles any future 18 + 16 + 54 families into the `Fin 88 -> P`
   family C96-3b consumes.

   STALL (not a kill): the remaining directions of the T4 split
   (18 SM-like / 16 flipped / 54 exotic) are the non-hermitian
   directions `I * H-` (J-ANTI-compatible hermitian order-one blocks,
   the 240-dimensional side of the Python's `272 + 240` off-diagonal
   pattern split) and the flipped / E-slot hermitian directions
   beyond the 22. The corpus owns NO J-anticompatible order-one
   direction and no order-one engine for the flipped or general
   E-slot buildDirac patterns (the owned exotic order-one proofs are
   per-matrix entry bashes for the 12 W22 survivors only). Those
   memberships are therefore NOT proved here; no direction is padded
   with zero and no slot is merely counted (K-C96-2 guard). The gap
   is exactly: order-one proofs for (a) the 8 flipped A-slot patterns,
   (b) the J-anticompatible partners of the hermitian families,
   (c) the remaining exotic Majorana E-slot patterns.

## Kills and fences (on the face)

- K-C96-1 (armed): a PROVED 89th independent direction, or any proved
  finrank of P different from 88, kills the T4 note at full rank.
  Nothing here proves any finrank of P; the finrank headline is
  C96-3b's, gated on the full direction set plus independence and the
  upper bound. Failure to find directions is a STALL (above), never
  a kill.
- K-C96-2 (vacuity): every direction named here is an element of P
  with its coupling conditions proved; parameter-slot counting is
  not membership, and no count is asserted by definitional unfolding.
- Generations IMPOSED; CKM/PMNS input-only; this module counts
  slots/directions and derives no flavour quantity; Q3 OPEN;
  NO CLAIM. The old 46 -> 10 gloss is UNSOUND AS STATED and is not
  cited as support.
-/

open Matrix

namespace ThetLogos

/-! ## 1. The mixing-pair space P -/

/-- **The mixing-pair space `P`** (the pack's calligraphic P): the
    space of mixing-pair blocks for one unordered generation pair.
    By C96-1's landed determination this is exactly
    `Census96PairSol`: single off-diagonal blocks `M` such that the
    self-adjoint pair `(M, M-dagger)` has both members
    block-admissible and both order-one. Tier T2 (definition by
    identification with the landed T1-built space). -/
def PairSpace : Submodule ℝ (Matrix I32 I32 ℂ) := Census96PairSol

/-- `PairSpace` is the landed `Census96PairSol`, by definition. -/
theorem pairSpace_eq : PairSpace = Census96PairSol := rfl

/-- **Characterization of P.** Membership in the pair space is
    exactly the four pair conditions: block-admissibility of `M`,
    block-admissibility of the self-adjoint partner `M-dagger`, and
    the one-generation order-one condition on both members. -/
theorem mem_pairSpace_iff (M : Matrix I32 I32 ℂ) :
    M ∈ PairSpace ↔ IsAdmBlock M ∧ IsAdmBlock M.conjTranspose ∧
      OrderOneHolds M ∧ OrderOneHolds M.conjTranspose :=
  Iff.rfl

/-- The zero pair is in P. -/
theorem pairSpace_zero_mem : (0 : Matrix I32 I32 ℂ) ∈ PairSpace :=
  Submodule.zero_mem PairSpace

/-! ## 2. Pair-coupling lemmas (SA + J) for a pair in isolation -/

/-- Projection: the first member of a pair is block-admissible. -/
theorem pairSpace_admBlock {M : Matrix I32 I32 ℂ} (hM : M ∈ PairSpace) :
    IsAdmBlock M := hM.1

/-- Projection (SA coupling): the partner member `M-dagger` of a pair
    is block-admissible. -/
theorem pairSpace_admBlock_partner {M : Matrix I32 I32 ℂ} (hM : M ∈ PairSpace) :
    IsAdmBlock M.conjTranspose := hM.2.1

/-- Projection: the first member of a pair is order-one. -/
theorem pairSpace_orderOne {M : Matrix I32 I32 ℂ} (hM : M ∈ PairSpace) :
    OrderOneHolds M := hM.2.2.1

/-- Projection (SA coupling): the partner member `M-dagger` of a pair
    is order-one. -/
theorem pairSpace_orderOne_partner {M : Matrix I32 I32 ℂ} (hM : M ∈ PairSpace) :
    OrderOneHolds M.conjTranspose := hM.2.2.2

/-- **SA coupling, involution:** the partner of the partner is the
    original block: `(M-dagger)-dagger = M`. The pair `(M, M-dagger)`
    is symmetric in its two members. -/
theorem pairSpace_partner_partner (M : Matrix I32 I32 ℂ) :
    M.conjTranspose.conjTranspose = M :=
  Matrix.conjTranspose_conjTranspose M

/-- **SA coupling, entrywise:** the partner block's entries are the
    conjugate-transposed entries of `M`. -/
theorem pairSpace_partner_entry (M : Matrix I32 I32 ℂ) (i j : I32) :
    M.conjTranspose i j = star (M j i) := rfl

/-- **J coupling for the pair in isolation:** for `M` in P, the
    partner block at the J-mirrored entry `(partner j, partner i)`
    equals `M i j`. This is the entrywise content of the pair's
    J-compatibility read across the two members: self-adjointness
    supplies the dagger, J supplies the mirror. -/
theorem pairSpace_J_cross {M : Matrix I32 I32 ℂ} (hM : M ∈ PairSpace)
    (i j : I32) : M.conjTranspose (partner j) (partner i) = M i j := by
  rw [pairSpace_partner_entry]
  exact admBlock_entry_star M hM.1 i j

/-- **J coupling, first member:** `star (M (partner i) (partner j))
    = M i j` (the landed `admBlock_entry_star`, restated for P). -/
theorem pairSpace_J_entry {M : Matrix I32 I32 ℂ} (hM : M ∈ PairSpace)
    (i j : I32) : star (M (partner i) (partner j)) = M i j :=
  admBlock_entry_star M hM.1 i j

/-- **J coupling, partner member:** the partner block satisfies the
    same J-mirror identity. -/
theorem pairSpace_J_entry_partner {M : Matrix I32 I32 ℂ} (hM : M ∈ PairSpace)
    (i j : I32) :
    star (M.conjTranspose (partner i) (partner j)) = M.conjTranspose i j :=
  admBlock_entry_star M.conjTranspose hM.2.1 i j

/-- **Grading coupling:** both members of a pair vanish at entries
    whose grading signs agree (the pair is grading-odd in both
    members). -/
theorem pairSpace_gammaOdd_entry_eq_zero {M : Matrix I32 I32 ℂ}
    (hM : M ∈ PairSpace) {i j : I32} (hij : gSign i = gSign j) :
    M i j = 0 ∧ M.conjTranspose i j = 0 :=
  ⟨gammaOdd_entry_eq_zero_of_gSign_eq M hM.1.1 hij,
   gammaOdd_entry_eq_zero_of_gSign_eq M.conjTranspose hM.2.1.1 hij⟩

/-! ## 3. The hermitian embedding: `Sol32` directions lie in P -/

/-- Under self-adjointness, entrywise conjugation is transposition:
    `entrywiseConj D = D.transpose` when `D-dagger = D`. This is the
    bridge between the Python's conj form of block J-compatibility
    and the corpus's owned transpose form. -/
theorem entrywiseConj_eq_transpose_of_selfAdjoint {D : Matrix I32 I32 ℂ}
    (h : D.conjTranspose = D) : entrywiseConj D = D.transpose := by
  ext i j
  rw [Matrix.transpose_apply]
  change star (D i j) = D j i
  rw [selfAdjoint_entry D h i j, star_star]

/-- A one-generation admissible block is block-admissible: under
    self-adjointness the owned transpose-form J-compatibility
    `UJ * D-transpose * UJ = D` rewrites to the conj form
    `UJ * conj(D) = D * UJ` using `UJ * UJ = 1`. -/
theorem isAdmBlock_of_isAdm32 {D : Matrix I32 I32 ℂ} (h : IsAdm32 D) :
    IsAdmBlock D := by
  refine ⟨h.2.1, ?_⟩
  rw [entrywiseConj_eq_transpose_of_selfAdjoint h.1]
  have h2 := congrArg (· * UJ) h.2.2
  rwa [mul_assoc, UJ_mul_self, mul_one] at h2

/-- **Hermitian embedding.** Every one-generation admissible
    order-one block lies in P: for a self-adjoint `D` the pair
    `(D, D-dagger)` is `(D, D)`, so the four pair conditions collapse
    to `IsAdm32 D` (via the conj/transpose bridge) and
    `OrderOneHolds D`. In particular every element of `Sol32`,
    read as a block, is a mixing-pair direction with equal members. -/
theorem pairSpace_of_isAdm32 {D : Matrix I32 I32 ℂ} (hA : IsAdm32 D)
    (hO : OrderOneHolds D) : D ∈ PairSpace := by
  refine ⟨isAdmBlock_of_isAdm32 hA, ?_, hO, ?_⟩
  · rw [hA.1]; exact isAdmBlock_of_isAdm32 hA
  · rw [hA.1]; exact hO

/-- Every `W22` direction (the cut-down space of `CFKernel22`:
    order-one, self-adjoint, J-compatible, grading-odd) lies in P. -/
theorem pairSpace_of_isW22 {D : Matrix I32 I32 ℂ} (h : IsW22 D) :
    D ∈ PairSpace :=
  pairSpace_of_isAdm32 ⟨h.2.2.1, h.2.2.2.2, h.2.2.2.1⟩ h.1

/-! ## 4. The landed hermitian directions in P -/

/-- The 22 owned hermitian directions of `CFKernel22` (10 SM + 12
    exotic), as elements of P via the hermitian embedding. These are
    explicit elements of P with all four coupling conditions proved
    (through `dirs22_mem` and `pairSpace_of_isW22`) - not slot
    counts. -/
def pairDir22 (k : Fin 22) : PairSpace :=
  ⟨dirs22 k, pairSpace_of_isW22 (dirs22_mem k)⟩

/-- The underlying block of `pairDir22 k` is `dirs22 k`. -/
theorem pairDir22_apply (k : Fin 22) :
    (pairDir22 k : Matrix I32 I32 ℂ) = dirs22 k := rfl

/-- The SM subfamily of the landed directions: indices 0-9 of
    `dirs22` (the real/imaginary parts of the five SM parameters
    `yNu, yE, yU, yD, yR`), as elements of P. -/
def pairDirSM (k : Fin 10) : PairSpace :=
  pairDir22 ⟨k.val, lt_trans k.isLt (by norm_num)⟩

/-- The exotic subfamily of the landed directions: indices 10-21 of
    `dirs22` (the 12 exotic W22 survivors), as elements of P. -/
def pairDirExotic (k : Fin 12) : PairSpace :=
  pairDir22 ⟨k.val + 10, by have h := k.isLt; omega⟩

/-! ## 5. The pair in isolation at 96, and the `Fin 88` assembly form -/

/-- **Isolation.** A pair in P, placed alone at one unordered
    generation pair `p` (zero diagonal data, zero other pairs),
    assembles through the landed `census96Backward` to a global
    order-one solution at 96 whose `(p.1, p.2)` block is `M` and
    whose `(p.2, p.1)` block is the SA partner `M-dagger`. The pair
    coupling is exactly the global self-adjointness of the assembly. -/
theorem pairSpace_isolation {M : PairSpace} (p : GenPair) :
    ∃ D : Census96Sol, genBlock D.1 p.1.1 p.1.2 = M.1 ∧
      genBlock D.1 p.1.2 p.1.1 = M.1.conjTranspose := by
  have hpp : (⟨(p.1.1, p.1.2), p.2⟩ : GenPair) = p := Subtype.ext rfl
  refine ⟨census96Backward (fun _ => 0,
    fun q => if q = p then (⟨M.1, M.2⟩ : Census96PairSol) else 0), ?_, ?_⟩
  · show genBlock (assemble96 (fun g => ((fun _ => (0 : Sol32)) g).1)
        (fun q => ((fun q => if q = p then (⟨M.1, M.2⟩ : Census96PairSol)
          else (0 : Census96PairSol)) q).1))
        p.1.1 p.1.2 = M.1
    rw [genBlock_assemble96, pairBlockOf_of_lt _ _ p.2]
    simp [hpp]
  · show genBlock (assemble96 (fun g => ((fun _ => (0 : Sol32)) g).1)
        (fun q => ((fun q => if q = p then (⟨M.1, M.2⟩ : Census96PairSol)
          else (0 : Census96PairSol)) q).1))
        p.1.2 p.1.1 = M.1.conjTranspose
    rw [genBlock_assemble96, pairBlockOf_of_gt _ _ p.2]
    simp [hpp]

/-- **The `Fin 88 -> P` assembly form for C96-3b.** Any three
    direction families of the T4 split sizes - 18 SM-like, 16
    flipped, 54 exotic, each an explicit element of P - concatenate
    into the single indexed family `Fin 88 -> P` that the finrank
    assembly consumes. This combinator is bookkeeping only: it
    asserts no membership beyond what the three input families
    carry (K-C96-2 guard). -/
def dir88Of (dSM : Fin 18 → PairSpace) (dFlip : Fin 16 → PairSpace)
    (dEx : Fin 54 → PairSpace) : Fin 88 → PairSpace :=
  Fin.append (Fin.append dSM dFlip) dEx

/-- The SM-like segment of the assembled family: the first 18
    indices are the `dSM` directions. -/
theorem dir88Of_SM (dSM : Fin 18 → PairSpace) (dFlip : Fin 16 → PairSpace)
    (dEx : Fin 54 → PairSpace) (k : Fin 18) :
    dir88Of dSM dFlip dEx ⟨k.val, by have h := k.isLt; omega⟩ = dSM k := by
  have e1 : (⟨k.val, by have h := k.isLt; omega⟩ : Fin 88)
      = Fin.castAdd 54 (Fin.castAdd 16 k) := Fin.ext rfl
  rw [dir88Of, e1, Fin.append_left, Fin.append_left]

/-- The flipped segment of the assembled family: indices 18-33 are
    the `dFlip` directions. -/
theorem dir88Of_flip (dSM : Fin 18 → PairSpace) (dFlip : Fin 16 → PairSpace)
    (dEx : Fin 54 → PairSpace) (k : Fin 16) :
    dir88Of dSM dFlip dEx ⟨k.val + 18, by have h := k.isLt; omega⟩ = dFlip k := by
  have e1 : (⟨k.val + 18, by have h := k.isLt; omega⟩ : Fin 88)
      = Fin.castAdd 54 (Fin.natAdd 18 k) := by
    apply Fin.ext
    show k.val + 18 = 18 + k.val
    omega
  rw [dir88Of, e1, Fin.append_left, Fin.append_right]

/-- The exotic segment of the assembled family: indices 34-87 are
    the `dEx` directions. -/
theorem dir88Of_exotic (dSM : Fin 18 → PairSpace) (dFlip : Fin 16 → PairSpace)
    (dEx : Fin 54 → PairSpace) (k : Fin 54) :
    dir88Of dSM dFlip dEx ⟨k.val + 34, by have h := k.isLt; omega⟩ = dEx k := by
  have e1 : (⟨k.val + 34, by have h := k.isLt; omega⟩ : Fin 88)
      = Fin.natAdd 34 k := by
    apply Fin.ext
    show k.val + 34 = 34 + k.val
    omega
  rw [dir88Of, e1, Fin.append_right]

end ThetLogos
