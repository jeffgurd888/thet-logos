import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Metric
import ThetLogos.PoissonTotalMassBlindness

/-!
# ThetLogos.RLP1PhiLayer — RL-P1, Brick 1: the Φ layer (TW-P1..TW-P7)

## STATUS — READ FIRST (the closure is on the face)

This module formalizes, as corpus mathematics, the **Φ layer** of the
mechanics registered as **RL-P1** (Gate 1 pre-registration v1, frozen
2026-11-05, `rl-p1-gate1-preregistration-2026-11-05.md`; v2,
`rl-p1-gate1-preregistration-v2-2026-11-05.md`). The theorems here are
the Φ-layer theorems-in-waiting **TW-P1..TW-P7** of the Gate 4
derivation report (`rl-p1-gate4-derivation-2026-11-05.md`, §2 and §8),
in §8's dependency order.

**The gravity candidacy of RL-P1 is CLOSED.** At Gate 4 the frozen
shadow test (v2 §2) was run exactly as frozen, in exact rational
arithmetic, and shape agreement failed on both registered cases:
**K-RLP1-SHADOW FIRED.** The recorded verdict (v1 §6, pre-written) is:

> **RL-P1 is a mechanics, not a gravity candidate.**

Per the registration (P-D2), that kill is final for RL-P1 as
registered; Gates 5–8 do not run on it. This module is built — on
Jeff's explicit decision of 2026-11-05 — **as corpus mechanics only**,
decoupled from any Dial-2 candidacy. There is **no Dial-2 language
anywhere in this module**: no statement here is evidence for, or a
step toward, any gravity claim. **NO CLAIM; dials 0/4; Dial 2 = 0.**

Register discipline (v1 §1, §2): everything below is **Register A
vocabulary only** — the seat, the kernel `K(x, y) = q ^ d(x, y)`, and
the raw coupling sum `Φ`. No Register B sentence occurs in any
definition or theorem. Per rider **R-G2F2** (v2 §3): the minus sign in
`Φ`'s definition is a **declared convention** of the primitive, fixing
which way the coupling term leans; nothing in this module presents
that lean as derived, forced, or an attraction.

## What is here

The seat is the finite weighted-graph seat of `BridgeLaplacian.lean` /
`GreenOperator.lean` (v1 §2.1): a finite type `V`, weights
`w : V → V → ℝ` symmetric, nonnegative, zero diagonal, the seat graph
`G_w` (adjacency `w x y ≠ 0`) connected, distance
`d(x, y) := G_w.dist x y`. The seat is packaged as a structure
(`RLP1Seat`) so the later RL-P1 bricks consume one stable handle.
(The Φ layer itself consumes less: connectedness is used only by the
registered-seat exhibits of TW-P7, through the graph-distance
characterizations; TW-P1..TW-P6 hold seat-by-seat with the distance
as given.)

- §1: seat, kernel, row sum, Φ, eccentricity; kernel basics.
- §2 (in §8's dependency order): **TW-P1** linearity →
  **TW-P2** row sums `R(x) ≥ 1`, equality iff `|V| = 1` →
  **TW-P3** constant-shift identity (with the non-invariance
  corollary: the operational form of K-RLP1-BLIND does not fire for
  the registered Φ) → **TW-P4** no `meanSub` factorization →
  **TW-P5** total visibility.
- §3: **TW-P6** bounds for nonnegative backgrounds.
- §4: **TW-P7** registered-seat exact values (v2 §2 seats at
  `q = 1/2`): row sums on the path seat `P₈` and the product seat
  `C₄ × C₄`, and Φ of the P₈ delta background — finite computation
  exhibits, proved against the graph distances of those seats.

NOT here (later bricks, fired separately): the stationarity layer
(TW-S1..TW-S5), the universality statement (TW-U1), the successor
exhibit (TW-S6). The exclusion list of v1 §2.5 binds this module:
Φ is a raw kernel sum — no Poisson solve, no Green operator, no
`meanSub` factorization occurs in its definition (TW-P4 proves the
last of these is not merely unchosen but impossible for this Φ).

Axiom audit: headline theorems are checked at the end of the file
against the standard three (`propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace ThetLogos

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-! ## §1. The seat, the kernel, the coupling sum -/

/-- The seat graph of raw weight data: adjacency is `w x y ≠ 0`
(v1 §2.1). The symmetry and diagonal hypotheses are exactly what a
simple graph needs; they are part of the seat data wherever the
graph is used. -/
def rlp1GraphOf (w : V → V → ℝ) (hsymm : ∀ x y, w x y = w y x)
    (hdiag : ∀ x, w x x = 0) : SimpleGraph V where
  Adj x y := w x y ≠ 0
  symm := ⟨fun x y h => by rwa [hsymm y x]⟩
  loopless := ⟨fun x h => h (hdiag x)⟩

/-- An **RL-P1 seat** (v1 §2.1): the finite weighted-graph seat,
packaged. `w` is the weight function; `connected` is the declared
seat condition on the seat graph `G_w`. The decay factor `q` is
*not* part of the seat: it is a declared input of the candidate
(v1 §5), passed to the kernel and Φ separately. -/
structure RLP1Seat (V : Type*) [Fintype V] [DecidableEq V] where
  /-- The weight function of the seat. -/
  w : V → V → ℝ
  /-- Weights are symmetric. -/
  symm : ∀ x y, w x y = w y x
  /-- Weights are nonnegative. -/
  nonneg : ∀ x y, 0 ≤ w x y
  /-- The diagonal vanishes. -/
  diag : ∀ x, w x x = 0
  /-- The seat graph is connected (declared seat condition). -/
  connected : (rlp1GraphOf w symm diag).Connected

/-- The seat graph `G_w` of a packaged seat. -/
def RLP1Seat.graph (s : RLP1Seat V) : SimpleGraph V :=
  rlp1GraphOf s.w s.symm s.diag

/-- Seat distance `d(x, y) := G_w.dist x y` (v1 §2.1). -/
noncomputable def RLP1Seat.dist (s : RLP1Seat V) (x y : V) : ℕ :=
  s.graph.dist x y

/-- The kernel (v1 §2.4, frozen form): `K(x, y) = q ^ d(x, y)`,
defined directly from the seat distance — no inversion, no solve,
no limit. -/
noncomputable def rlp1Kernel (s : RLP1Seat V) (q : ℝ) (x y : V) : ℝ :=
  q ^ s.dist x y

/-- The row sum `R(x) := Σ_y K(x, y)` (Gate 4 §2). -/
noncomputable def rlp1RowSum (s : RLP1Seat V) (q : ℝ) (x : V) : ℝ :=
  ∑ y, rlp1Kernel s q x y

/-- The coupling sum (v1 §2.4): `Φ(ρ, x) := −Σ_y K(x, y) · ρ(y)`.
A raw sum over sites: no mean is subtracted, no operator is
inverted. The minus sign is a declared convention of the primitive
(R-G2F2); it is part of the definition, not a derived direction. -/
noncomputable def rlp1Phi (s : RLP1Seat V) (q : ℝ) (ρ : V → ℝ) (x : V) : ℝ :=
  -∑ y, rlp1Kernel s q x y * ρ y

/-- The eccentricity `e(x) := max_y d(x, y)` of a site (Gate 4,
TW-P6), as the maximum over the finite seat (the value `d(x, x)`
itself witnesses the image is inhabited). -/
noncomputable def rlp1Ecc (s : RLP1Seat V) (x : V) : ℕ :=
  (Finset.univ.image (s.dist x)).max'
    ⟨s.dist x x, Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩⟩

/-- The kernel on the diagonal is `1`: `K(x, x) = q ^ 0 = 1`. -/
theorem rlp1Kernel_self (s : RLP1Seat V) (q : ℝ) (x : V) :
    rlp1Kernel s q x x = 1 := by
  simp [rlp1Kernel, RLP1Seat.dist, SimpleGraph.dist_self]

/-- The kernel is positive wherever `q` is. -/
theorem rlp1Kernel_pos (s : RLP1Seat V) (hq : 0 < q) (x y : V) :
    0 < rlp1Kernel s q x y :=
  pow_pos hq _

/-- Every seat distance is bounded by the eccentricity. -/
theorem rlp1Dist_le_ecc (s : RLP1Seat V) (x y : V) :
    s.dist x y ≤ rlp1Ecc s x :=
  Finset.le_max' _ _ (Finset.mem_image.mpr ⟨y, Finset.mem_univ y, rfl⟩)

/-! ## §2. TW-P1..TW-P5 — the Φ chain, in §8's dependency order -/

/-- **TW-P1 (linearity).** `Φ(a·ρ₁ + b·ρ₂, x) = a·Φ(ρ₁, x) +
b·Φ(ρ₂, x)` for all scalars `a, b` and fields `ρ₁, ρ₂`.
*Proof (Gate 4):* linearity of the finite sum. -/
theorem rlp1Phi_linear (s : RLP1Seat V) (q a b : ℝ) (ρ₁ ρ₂ : V → ℝ)
    (x : V) :
    rlp1Phi s q (a • ρ₁ + b • ρ₂) x
      = a * rlp1Phi s q ρ₁ x + b * rlp1Phi s q ρ₂ x := by
  have hsum : (∑ y, rlp1Kernel s q x y * (a * ρ₁ y + b * ρ₂ y))
      = a * (∑ y, rlp1Kernel s q x y * ρ₁ y)
        + b * (∑ y, rlp1Kernel s q x y * ρ₂ y) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  simp only [rlp1Phi, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hsum]; ring

/-- **TW-P2 (row sums, lower bound).** `R(x) ≥ 1` for every `x`.
*Proof (Gate 4):* every term `q^{d(x,y)} > 0` and the diagonal
term is `K(x, x) = q⁰ = 1`. -/
theorem rlp1RowSum_ge_one (s : RLP1Seat V) (hq : 0 < q) (x : V) :
    1 ≤ rlp1RowSum s q x := by
  calc (1:ℝ) = rlp1Kernel s q x x := (rlp1Kernel_self s q x).symm
    _ ≤ ∑ y, rlp1Kernel s q x y :=
        Finset.single_le_sum (fun y _ => (rlp1Kernel_pos s hq x y).le)
          (Finset.mem_univ x)
    _ = rlp1RowSum s q x := rfl

/-- **TW-P2 (row sums, equality case).** `R(x) = 1` iff the seat
has exactly one site. -/
theorem rlp1RowSum_eq_one_iff (s : RLP1Seat V) (hq : 0 < q)
    (x : V) :
    rlp1RowSum s q x = 1 ↔ Fintype.card V = 1 := by
  constructor
  · intro h
    by_contra hcard
    have h1le : 1 ≤ Fintype.card V := Fintype.card_pos
    have hcard2 : 1 < Fintype.card V :=
      lt_of_le_of_ne h1le (Ne.symm hcard)
    obtain ⟨y, hy⟩ := Fintype.exists_ne_of_one_lt_card hcard2 x
    have hsplit : rlp1RowSum s q x
        = rlp1Kernel s q x x
          + Finset.sum (Finset.univ.erase x)
              (fun z => rlp1Kernel s q x z) := by
      rw [rlp1RowSum, ← Finset.add_sum_erase _ _ (Finset.mem_univ x)]
    have hterm : rlp1Kernel s q x y
        ≤ Finset.sum (Finset.univ.erase x)
            (fun z => rlp1Kernel s q x z) :=
      Finset.single_le_sum (fun z _ => (rlp1Kernel_pos s hq x z).le)
        (Finset.mem_erase.mpr ⟨hy, Finset.mem_univ y⟩)
    have hpos : (0:ℝ) < rlp1Kernel s q x y := rlp1Kernel_pos s hq x y
    rw [rlp1Kernel_self] at hsplit
    linarith
  · intro hcard
    obtain ⟨a, ha⟩ := Fintype.card_eq_one_iff.mp hcard
    have huniq : ∀ z : V, z = x := fun z => (ha z).trans (ha x).symm
    rw [rlp1RowSum, Finset.sum_eq_single x]
    · exact rlp1Kernel_self s q x
    · intro z _ hz
      exact absurd (huniq z) hz
    · intro hcon
      exact absurd (Finset.mem_univ x) hcon

/-- Φ of a constant field: `Φ(c·1, x) = −c · R(x)`. This is the
computation inside both TW-P3 and TW-P5. -/
theorem rlp1Phi_const (s : RLP1Seat V) (q c : ℝ) (x : V) :
    rlp1Phi s q (fun _ => c) x = -c * rlp1RowSum s q x := by
  simp only [rlp1Phi, rlp1RowSum, ← Finset.sum_mul]
  ring

/-- **TW-P3 (constant-shift identity).**
`Φ(ρ + c, x) = Φ(ρ, x) − c · R(x)` for every constant `c`.
*Proof (Gate 4):* TW-P1 and `Φ(c·1, x) = −c·R(x)`. -/
theorem rlp1Phi_add_const (s : RLP1Seat V) (q : ℝ) (ρ : V → ℝ)
    (c : ℝ) (x : V) :
    rlp1Phi s q (fun i => ρ i + c) x
      = rlp1Phi s q ρ x - c * rlp1RowSum s q x := by
  have hsum : (∑ y, rlp1Kernel s q x y * (ρ y + c))
      = (∑ y, rlp1Kernel s q x y * ρ y)
        + c * ∑ y, rlp1Kernel s q x y := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  simp only [rlp1Phi, rlp1RowSum]
  rw [hsum]; ring

/-- **TW-P3, the registered consequence.** The statement
"`Φ(ρ + c, x) = Φ(ρ, x)` for all `c, x`" is **false** of the
registered Φ (at `c = 1` the difference is `R(x) ≥ 1 > 0`) — the
operational form of K-RLP1-BLIND does not fire (Gate 4 §2). -/
theorem rlp1Phi_add_const_ne (s : RLP1Seat V) (hq : 0 < q)
    (ρ : V → ℝ) (x : V) :
    rlp1Phi s q (fun i => ρ i + 1) x ≠ rlp1Phi s q ρ x := by
  have hR : (0:ℝ) < rlp1RowSum s q x :=
    lt_of_lt_of_le one_pos (rlp1RowSum_ge_one s hq x)
  rw [rlp1Phi_add_const]
  intro hcon
  have hB : (1:ℝ) * rlp1RowSum s q x = 0 := by linarith [hcon]
  rw [one_mul] at hB
  exact hR.ne' hB

/-- **TW-P4 (no mean-subtraction factorization).** There is no
functional `F` with `Φ(ρ, x) = F(meanSub ρ) (x)` for all `ρ, x`:
`meanSub (ρ + c) = meanSub ρ` (landed, `meanSub_add_const`), while
TW-P3 shows `Φ` changes under the same shift. Together with the
absence of any Green/Poisson factor in Φ's definition, this
discharges the Φ side of K-RLP1-BLIND: the kill does not fire
(Gate 4 §2). -/
theorem rlp1Phi_not_factor_meanSub (s : RLP1Seat V) (hq : 0 < q) :
    ¬ ∃ F : (V → ℝ) → (V → ℝ),
      ∀ ρ x, rlp1Phi s q ρ x = F (meanSub ρ) x := by
  rintro ⟨F, hF⟩
  obtain ⟨x⟩ := (inferInstance : Nonempty V)
  have h1 := hF (fun i : V => (0:ℝ) + 1) x
  have h2 := hF (fun _ : V => (0:ℝ)) x
  have hm : meanSub (fun i : V => (0:ℝ) + 1)
      = meanSub (fun _ : V => (0:ℝ)) :=
    meanSub_add_const (fun _ : V => (0:ℝ)) 1
  rw [hm] at h1
  exact rlp1Phi_add_const_ne s hq (fun _ : V => (0:ℝ)) x
    (h1.trans h2.symm)

/-- **TW-P5 (total visibility).** With `Φ(c·1, x) = −c·R(x)`
(`rlp1Phi_const`) and `R(x) ≥ 1`, the constant level — hence the
total `c·|V|` — is recoverable from Φ at any single site:
`c = −Φ(c·1, x) / R(x)`. The coupling sees the total source by
construction, as registered (v1 §2.4 (ii)). -/
theorem rlp1_const_eq (s : RLP1Seat V) (hq : 0 < q) (c : ℝ)
    (x : V) :
    c = -rlp1Phi s q (fun _ => c) x / rlp1RowSum s q x := by
  have hR : rlp1RowSum s q x ≠ 0 :=
    (lt_of_lt_of_le one_pos (rlp1RowSum_ge_one s hq x)).ne'
  rw [rlp1Phi_const, eq_div_iff hR]
  ring

/-! ## §3. TW-P6 — bounds for nonnegative backgrounds -/

/-- The kernel is antitone in the distance when `0 < q ≤ 1`:
a larger distance gives a smaller kernel value. -/
theorem rlp1Kernel_antitone (hq0 : 0 < q) (hq1 : q ≤ 1)
    {a b : ℕ} (h : a ≤ b) : q ^ b ≤ q ^ a := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add]
  have h1 : q ^ k ≤ 1 := pow_le_one₀ hq0.le hq1
  calc q ^ a * q ^ k ≤ q ^ a * 1 :=
        mul_le_mul_of_nonneg_left h1 (pow_pos hq0 a).le
    _ = q ^ a := mul_one _

/-- The kernel is at most `1` when `0 < q ≤ 1`. -/
theorem rlp1Kernel_le_one (s : RLP1Seat V) (hq0 : 0 < q)
    (hq1 : q ≤ 1) (x y : V) : rlp1Kernel s q x y ≤ 1 := by
  show q ^ s.dist x y ≤ 1
  exact pow_le_one₀ hq0.le hq1

/-- **TW-P6 (bounds for nonnegative backgrounds).** If `ρ ≥ 0` and
`e(x)` is the eccentricity of `x`, then
`−Σ_y ρ(y) ≤ Φ(ρ, x) ≤ −(q^{e(x)} · Σ_y ρ(y))`.
*Proof (Gate 4):* `q^{e(x)} ≤ K(x, y) ≤ 1` term-by-term. -/
theorem rlp1Phi_bounds (s : RLP1Seat V) (hq0 : 0 < q) (hq1 : q < 1)
    (ρ : V → ℝ) (hρ : ∀ y, 0 ≤ ρ y) (x : V) :
    -(∑ y, ρ y) ≤ rlp1Phi s q ρ x
      ∧ rlp1Phi s q ρ x ≤ -((q ^ rlp1Ecc s x) * ∑ y, ρ y) := by
  have hterm : ∀ y, q ^ rlp1Ecc s x * ρ y ≤ rlp1Kernel s q x y * ρ y
      ∧ rlp1Kernel s q x y * ρ y ≤ ρ y := by
    intro y
    constructor
    · have hker : q ^ rlp1Ecc s x ≤ rlp1Kernel s q x y := by
        unfold rlp1Kernel
        exact pow_le_pow_of_le_one hq0.le hq1.le
          (rlp1Dist_le_ecc s x y)
      exact mul_le_mul_of_nonneg_right hker (hρ y)
    · have hK : rlp1Kernel s q x y ≤ 1 :=
        rlp1Kernel_le_one s hq0 hq1.le x y
      calc rlp1Kernel s q x y * ρ y ≤ 1 * ρ y :=
            mul_le_mul_of_nonneg_right hK (hρ y)
        _ = ρ y := one_mul _
  have hsum1 : (∑ y, q ^ rlp1Ecc s x * ρ y)
      ≤ ∑ y, rlp1Kernel s q x y * ρ y :=
    Finset.sum_le_sum fun y _ => (hterm y).1
  have hsum2 : (∑ y, rlp1Kernel s q x y * ρ y) ≤ ∑ y, ρ y :=
    Finset.sum_le_sum fun y _ => (hterm y).2
  rw [← Finset.mul_sum] at hsum1
  simp only [rlp1Phi]
  constructor <;> linarith

/-! ## §4. TW-P7 — registered-seat exact values

The two v2 §2 seats at `q = 1/2`, as finite computation exhibits.
Each seat's graph distance is characterized first; the tables are
then evaluations of `rlp1RowSum` / `rlp1Phi` against that
characterization. (The dictionary side of the v2 §2 test is the
audit's comparison standard, not a Φ-layer object — v1 §2.5 — and
does not occur here.) -/

/-- The natural-number distance `|a − b|`, written with truncated
subtraction. All of its basic facts are `omega`. -/
def rlp1NatDist (a b : ℕ) : ℕ := a - b + (b - a)

theorem rlp1NatDist_symm (a b : ℕ) :
    rlp1NatDist a b = rlp1NatDist b a := by
  unfold rlp1NatDist; omega

theorem rlp1NatDist_self (a : ℕ) : rlp1NatDist a a = 0 := by
  simp [rlp1NatDist]

theorem rlp1NatDist_triangle (a b c : ℕ) :
    rlp1NatDist a c ≤ rlp1NatDist a b + rlp1NatDist b c := by
  unfold rlp1NatDist; omega

theorem rlp1NatDist_eq_zero {a b : ℕ} :
    rlp1NatDist a b = 0 ↔ a = b := by
  unfold rlp1NatDist; omega

/-! ### The path seat P₈ -/

/-- The distance on the path seat: `|x − y|` on site values. -/
def pathDist8 (x y : Fin 8) : ℕ := rlp1NatDist x.val y.val

theorem pathDist8_symm (x y : Fin 8) :
    pathDist8 x y = pathDist8 y x :=
  rlp1NatDist_symm _ _

theorem pathDist8_self (x : Fin 8) : pathDist8 x x = 0 :=
  rlp1NatDist_self _

theorem pathDist8_triangle (x y z : Fin 8) :
    pathDist8 x z ≤ pathDist8 x y + pathDist8 y z :=
  rlp1NatDist_triangle _ _ _

/-- The unit weights of the path seat: `1` on adjacent sites,
`0` elsewhere. -/
def pathWeights8 (x y : Fin 8) : ℝ :=
  if pathDist8 x y = 1 then 1 else 0

theorem pathWeights8_symm :
    ∀ x y, pathWeights8 x y = pathWeights8 y x := by
  intro x y
  by_cases h : pathDist8 x y = 1
  · have h' : pathDist8 y x = 1 := by rw [pathDist8_symm]; exact h
    simp [pathWeights8, h, h']
  · have h' : pathDist8 y x ≠ 1 := by rw [pathDist8_symm]; exact h
    simp [pathWeights8, h, h']

theorem pathWeights8_diag : ∀ x, pathWeights8 x x = 0 := by
  intro x; simp [pathWeights8, pathDist8_self]

theorem pathWeights8_nonneg : ∀ x y, 0 ≤ pathWeights8 x y := by
  intro x y; unfold pathWeights8; split_ifs <;> norm_num

theorem pathWeights8_ne_zero_iff (x y : Fin 8) :
    pathWeights8 x y ≠ 0 ↔ pathDist8 x y = 1 := by
  by_cases h : pathDist8 x y = 1 <;> simp [pathWeights8, h]

/-- Adjacency in the path seat graph is unit distance. -/
theorem pathAdj_iff (hs : ∀ x y, pathWeights8 x y = pathWeights8 y x)
    (hd : ∀ x, pathWeights8 x x = 0) (x y : Fin 8) :
    (rlp1GraphOf pathWeights8 hs hd).Adj x y ↔ pathDist8 x y = 1 :=
  pathWeights8_ne_zero_iff x y

/-- Every walk in the path seat graph has length at least the
distance of its endpoints (walk induction on the triangle
inequality). -/
theorem pathDist8_le_of_walk
    (hs : ∀ x y, pathWeights8 x y = pathWeights8 y x)
    (hd : ∀ x, pathWeights8 x x = 0) {x y : Fin 8}
    (p : (rlp1GraphOf pathWeights8 hs hd).Walk x y) :
    pathDist8 x y ≤ p.length := by
  induction p with
  | nil => simp [pathDist8_self]
  | @cons u v w h p ih =>
    have h1 : pathDist8 u v = 1 := (pathAdj_iff hs hd u v).mp h
    have htri : pathDist8 u w ≤ pathDist8 u v + pathDist8 v w :=
      pathDist8_triangle u v w
    rw [SimpleGraph.Walk.length_cons]
    omega

/-- Every pair of sites of the path seat is joined by a walk of
length exactly the distance (strong induction on the distance:
step one site toward the target). -/
theorem pathWalk8 (hs : ∀ x y, pathWeights8 x y = pathWeights8 y x)
    (hd : ∀ x, pathWeights8 x x = 0) (x y : Fin 8) :
    ∃ p : (rlp1GraphOf pathWeights8 hs hd).Walk x y,
      p.length = pathDist8 x y := by
  suffices h : ∀ n (x y : Fin 8), pathDist8 x y = n →
      ∃ p : (rlp1GraphOf pathWeights8 hs hd).Walk x y,
        p.length = n by
    exact h _ x y rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x y hn
    by_cases hxy : x = y
    · have hn0 : n = 0 := by
        rw [← hn, hxy, pathDist8_self]
      subst hn0
      subst hxy
      exact ⟨SimpleGraph.Walk.nil, SimpleGraph.Walk.length_nil⟩
    · have hne : x.val ≠ y.val := fun hv => hxy (Fin.ext hv)
      have hn1 : 1 ≤ n := by
        have h0 : pathDist8 x y ≠ 0 := by
          show rlp1NatDist x.val y.val ≠ 0
          exact rlp1NatDist_eq_zero.not.mpr hne
        omega
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · obtain ⟨x', hx'v⟩ : ∃ z : Fin 8, z.val = x.val + 1 :=
          ⟨⟨x.val + 1, by omega⟩, rfl⟩
        have hstep : pathDist8 x x' = 1
            ∧ pathDist8 x' y + 1 = pathDist8 x y := by
          constructor
          · show rlp1NatDist x.val x'.val = 1
            rw [hx'v]; unfold rlp1NatDist; omega
          · show rlp1NatDist x'.val y.val + 1 = rlp1NatDist x.val y.val
            rw [hx'v]; unfold rlp1NatDist; omega
        have hadj : (rlp1GraphOf pathWeights8 hs hd).Adj x x' :=
          (pathAdj_iff hs hd x x').mpr hstep.1
        obtain ⟨p', hp'⟩ := ih (n - 1) (by omega) x' y (by omega)
        exact ⟨SimpleGraph.Walk.cons hadj p', by
          rw [SimpleGraph.Walk.length_cons, hp']; omega⟩
      · obtain ⟨x', hx'v⟩ : ∃ z : Fin 8, z.val = x.val - 1 :=
          ⟨⟨x.val - 1, by omega⟩, rfl⟩
        have hstep : pathDist8 x x' = 1
            ∧ pathDist8 x' y + 1 = pathDist8 x y := by
          constructor
          · show rlp1NatDist x.val x'.val = 1
            rw [hx'v]; unfold rlp1NatDist; omega
          · show rlp1NatDist x'.val y.val + 1 = rlp1NatDist x.val y.val
            rw [hx'v]; unfold rlp1NatDist; omega
        have hadj : (rlp1GraphOf pathWeights8 hs hd).Adj x x' :=
          (pathAdj_iff hs hd x x').mpr hstep.1
        obtain ⟨p', hp'⟩ := ih (n - 1) (by omega) x' y (by omega)
        exact ⟨SimpleGraph.Walk.cons hadj p', by
          rw [SimpleGraph.Walk.length_cons, hp']; omega⟩

/-- The path seat graph is connected. -/
theorem pathConnected
    (hs : ∀ x y, pathWeights8 x y = pathWeights8 y x)
    (hd : ∀ x, pathWeights8 x x = 0) :
    (rlp1GraphOf pathWeights8 hs hd).Connected := by
  constructor
  · intro x y
    obtain ⟨p, -⟩ := pathWalk8 hs hd x y
    exact ⟨p⟩

/-- The graph distance of the path seat is `|x − y|`. -/
theorem pathGraph_dist
    (hs : ∀ x y, pathWeights8 x y = pathWeights8 y x)
    (hd : ∀ x, pathWeights8 x x = 0) (x y : Fin 8) :
    (rlp1GraphOf pathWeights8 hs hd).dist x y = pathDist8 x y := by
  apply le_antisymm
  · obtain ⟨p, hp⟩ := pathWalk8 hs hd x y
    rw [← hp]
    exact SimpleGraph.dist_le p
  · obtain ⟨p, hp⟩ := (pathConnected hs hd).exists_walk_length_eq_dist
      (u := x) (v := y)
    rw [← hp]
    exact pathDist8_le_of_walk hs hd p

/-- The path seat P₈ as a packaged seat. -/
def pathSeat8 : RLP1Seat (Fin 8) where
  w := pathWeights8
  symm := pathWeights8_symm
  nonneg := pathWeights8_nonneg
  diag := pathWeights8_diag
  connected := pathConnected pathWeights8_symm pathWeights8_diag

/-- The seat distance of P₈ is `|x − y|`. -/
theorem pathSeat8_dist (x y : Fin 8) :
    pathSeat8.dist x y = pathDist8 x y :=
  pathGraph_dist _ _ x y

/-- The single-site (delta) background at `y₀`: value `1` at
`y₀`, `0` elsewhere. (Gate 4 §2's `δ` backgrounds, TW-P7;
encoded directly rather than via `Pi.single`.) -/
def rlp1Delta (y₀ : V) : V → ℝ := fun y => if y = y₀ then 1 else 0

/-- Φ of a single-site background is minus the kernel entry:
`Φ(δ_{y₀}, x) = −K(x, y₀)` (the sum collapses to one term). -/
theorem rlp1Phi_delta (s : RLP1Seat V) (q : ℝ) (y₀ : V) (x : V) :
    rlp1Phi s q (rlp1Delta y₀) x = -rlp1Kernel s q x y₀ := by
  simp only [rlp1Phi]
  rw [Finset.sum_eq_single y₀]
  · simp [rlp1Delta]
  · intro z _ hz
    have h0 : rlp1Delta y₀ z = 0 := if_neg hz
    rw [h0, mul_zero]
  · intro hcon
    exact absurd (Finset.mem_univ y₀) hcon

/-- Φ of the P₈ delta background (site `3`), closed form:
`Φ(δ₃, x) = −(1/2)^{|x − 3|}`. -/
theorem pathSeat8_phi_single (x : Fin 8) :
    rlp1Phi pathSeat8 (1/2 : ℝ) (rlp1Delta 3) x
      = -((1/2 : ℝ) ^ pathDist8 x 3) := by
  rw [rlp1Phi_delta]
  show -((1/2 : ℝ) ^ pathSeat8.dist x 3) = -((1/2 : ℝ) ^ pathDist8 x 3)
  rw [pathSeat8_dist]

/-- The P₈ row-sum table as data (Gate 4, TW-P7): the values
`R = (255/128, 159/64, 87/32, 45/16, 45/16, 87/32, 159/64,
255/128)` at sites `0…7` — nonconstant, as v2 §2.6 registers. -/
noncomputable def pathRowTable8 (x : Fin 8) : ℝ :=
  if x.val = 0 then 255/128
  else if x.val = 1 then 159/64
  else if x.val = 2 then 87/32
  else if x.val = 3 then 45/16
  else if x.val = 4 then 45/16
  else if x.val = 5 then 87/32
  else if x.val = 6 then 159/64
  else 255/128

/-- **TW-P7 (P₈ row sums, exact).** At `q = 1/2`, the row sums of
the path seat are the registered table. -/
theorem pathSeat8_rowSum_table (x : Fin 8) :
    rlp1RowSum pathSeat8 (1/2 : ℝ) x = pathRowTable8 x := by
  fin_cases x <;>
    simp only [rlp1RowSum, rlp1Kernel, pathSeat8_dist,
      Fin.sum_univ_eight] <;>
    norm_num [pathDist8, rlp1NatDist, pathRowTable8]

/-- The P₈ delta-Φ table as data (Gate 4, TW-P7): the values
`Φ(δ₃, ·) = (−1/8, −1/4, −1/2, −1, −1/2, −1/4, −1/8, −1/16)`
at sites `0…7`. -/
noncomputable def pathPhiTable8 (x : Fin 8) : ℝ :=
  if x.val = 0 then -1/8
  else if x.val = 1 then -1/4
  else if x.val = 2 then -1/2
  else if x.val = 3 then -1
  else if x.val = 4 then -1/2
  else if x.val = 5 then -1/4
  else if x.val = 6 then -1/8
  else -1/16

/-- **TW-P7 (P₈ delta background, exact).** At `q = 1/2`,
`Φ(δ₃, x) = −2^{−|x−3|}`, site by site the registered table. -/
theorem pathSeat8_phi_single_table (x : Fin 8) :
    rlp1Phi pathSeat8 (1/2 : ℝ) (rlp1Delta 3) x
      = pathPhiTable8 x := by
  rw [pathSeat8_phi_single]
  fin_cases x <;> norm_num [pathDist8, rlp1NatDist, pathPhiTable8]

/-! ### The cycle C₄ and the torus seat C₄ × C₄ -/

/-- The distance on the 4-cycle: the shorter of the two arcs,
`min (|a − b|, 4 − |a − b|)`. All of its basic facts are
`omega` after unfolding. -/
def rlp1CycDist4 (a b : Fin 4) : ℕ :=
  min (rlp1NatDist a.val b.val) (4 - rlp1NatDist a.val b.val)

theorem rlp1CycDist4_symm (a b : Fin 4) :
    rlp1CycDist4 a b = rlp1CycDist4 b a := by
  unfold rlp1CycDist4 rlp1NatDist; omega

theorem rlp1CycDist4_self (a : Fin 4) : rlp1CycDist4 a a = 0 := by
  unfold rlp1CycDist4 rlp1NatDist; omega

theorem rlp1CycDist4_triangle (a b c : Fin 4) :
    rlp1CycDist4 a c ≤ rlp1CycDist4 a b + rlp1CycDist4 b c := by
  have ha := a.isLt; have hb := b.isLt; have hc := c.isLt
  unfold rlp1CycDist4 rlp1NatDist; omega

theorem rlp1CycDist4_eq_zero {a b : Fin 4} :
    rlp1CycDist4 a b = 0 ↔ a = b := by
  have ha := a.isLt; have hb := b.isLt
  unfold rlp1CycDist4 rlp1NatDist; omega

/-- The clockwise successor on the 4-cycle. -/
def succ4 (a : Fin 4) : Fin 4 := ⟨(a.val + 1) % 4, by omega⟩

/-- The counterclockwise successor on the 4-cycle. -/
def pred4 (a : Fin 4) : Fin 4 := ⟨(a.val + 3) % 4, by omega⟩

theorem rlp1CycDist4_succ (a : Fin 4) : rlp1CycDist4 a (succ4 a) = 1 := by
  have ha := a.isLt
  have hv : (succ4 a).val = (a.val + 1) % 4 := rfl
  unfold rlp1CycDist4 rlp1NatDist
  rw [hv]; omega

theorem rlp1CycDist4_pred (a : Fin 4) : rlp1CycDist4 a (pred4 a) = 1 := by
  have ha := a.isLt
  have hv : (pred4 a).val = (a.val + 3) % 4 := rfl
  unfold rlp1CycDist4 rlp1NatDist
  rw [hv]; omega

/-- The unit weights of the 4-cycle. -/
def cycWeights4 (a b : Fin 4) : ℝ :=
  if rlp1CycDist4 a b = 1 then 1 else 0

theorem cycWeights4_symm :
    ∀ a b, cycWeights4 a b = cycWeights4 b a := by
  intro a b
  by_cases h : rlp1CycDist4 a b = 1
  · have h' : rlp1CycDist4 b a = 1 := by rw [rlp1CycDist4_symm]; exact h
    simp [cycWeights4, h, h']
  · have h' : rlp1CycDist4 b a ≠ 1 := by rw [rlp1CycDist4_symm]; exact h
    simp [cycWeights4, h, h']

theorem cycWeights4_diag : ∀ a, cycWeights4 a a = 0 := by
  intro a; simp [cycWeights4, rlp1CycDist4_self]

theorem cycWeights4_nonneg : ∀ a b, 0 ≤ cycWeights4 a b := by
  intro a b; unfold cycWeights4; split_ifs <;> norm_num

theorem cycWeights4_ne_zero_iff (a b : Fin 4) :
    cycWeights4 a b ≠ 0 ↔ rlp1CycDist4 a b = 1 := by
  by_cases h : rlp1CycDist4 a b = 1 <;> simp [cycWeights4, h]

/-- Adjacency in the cycle graph is unit cycle distance. -/
theorem cycAdj_iff (hs : ∀ a b, cycWeights4 a b = cycWeights4 b a)
    (hd : ∀ a, cycWeights4 a a = 0) (a b : Fin 4) :
    (rlp1GraphOf cycWeights4 hs hd).Adj a b ↔ rlp1CycDist4 a b = 1 :=
  cycWeights4_ne_zero_iff a b

/-- Every walk in the cycle graph has length at least the cycle
distance of its endpoints. -/
theorem rlp1CycDist4_le_of_walk
    (hs : ∀ a b, cycWeights4 a b = cycWeights4 b a)
    (hd : ∀ a, cycWeights4 a a = 0) {a b : Fin 4}
    (p : (rlp1GraphOf cycWeights4 hs hd).Walk a b) :
    rlp1CycDist4 a b ≤ p.length := by
  induction p with
  | nil => simp [rlp1CycDist4_self]
  | @cons u v w h p ih =>
    have h1 : rlp1CycDist4 u v = 1 := (cycAdj_iff hs hd u v).mp h
    have htri : rlp1CycDist4 u w ≤ rlp1CycDist4 u v + rlp1CycDist4 v w :=
      rlp1CycDist4_triangle u v w
    rw [SimpleGraph.Walk.length_cons]
    omega

/-- Every pair of sites of the 4-cycle is joined by a walk of
length exactly the cycle distance (strong induction on the
distance: step along a shortest arc). -/
theorem cycWalk4 (hs : ∀ a b, cycWeights4 a b = cycWeights4 b a)
    (hd : ∀ a, cycWeights4 a a = 0) (a b : Fin 4) :
    ∃ p : (rlp1GraphOf cycWeights4 hs hd).Walk a b,
      p.length = rlp1CycDist4 a b := by
  suffices h : ∀ n (a b : Fin 4), rlp1CycDist4 a b = n →
      ∃ p : (rlp1GraphOf cycWeights4 hs hd).Walk a b,
        p.length = n by
    exact h _ a b rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b hn
    by_cases hab : a = b
    · have hn0 : n = 0 := by
        rw [← hn, hab, rlp1CycDist4_self]
      subst hn0
      subst hab
      exact ⟨SimpleGraph.Walk.nil, SimpleGraph.Walk.length_nil⟩
    · have hne : a.val ≠ b.val := fun hv => hab (Fin.ext hv)
      have hn1 : 1 ≤ n := by
        have h0 : rlp1CycDist4 a b ≠ 0 := rlp1CycDist4_eq_zero.not.mpr hab
        omega
      by_cases hdir : (b.val + 4 - a.val) % 4 ≤ (a.val + 4 - b.val) % 4
      · have hstep : rlp1CycDist4 (succ4 a) b + 1 = rlp1CycDist4 a b := by
          have ha := a.isLt; have hb := b.isLt
          have hv : (succ4 a).val = (a.val + 1) % 4 := rfl
          unfold rlp1CycDist4 rlp1NatDist
          rw [hv]; omega
        have hadj : (rlp1GraphOf cycWeights4 hs hd).Adj a (succ4 a) :=
          (cycAdj_iff hs hd a (succ4 a)).mpr (rlp1CycDist4_succ a)
        obtain ⟨p', hp'⟩ := ih (n - 1) (by omega) (succ4 a) b (by omega)
        exact ⟨SimpleGraph.Walk.cons hadj p', by
          rw [SimpleGraph.Walk.length_cons, hp']; omega⟩
      · have hstep : rlp1CycDist4 (pred4 a) b + 1 = rlp1CycDist4 a b := by
          have ha := a.isLt; have hb := b.isLt
          have hv : (pred4 a).val = (a.val + 3) % 4 := rfl
          unfold rlp1CycDist4 rlp1NatDist
          rw [hv]; omega
        have hadj : (rlp1GraphOf cycWeights4 hs hd).Adj a (pred4 a) :=
          (cycAdj_iff hs hd a (pred4 a)).mpr (rlp1CycDist4_pred a)
        obtain ⟨p', hp'⟩ := ih (n - 1) (by omega) (pred4 a) b (by omega)
        exact ⟨SimpleGraph.Walk.cons hadj p', by
          rw [SimpleGraph.Walk.length_cons, hp']; omega⟩

/-- The cycle graph is connected. -/
theorem cycConnected
    (hs : ∀ a b, cycWeights4 a b = cycWeights4 b a)
    (hd : ∀ a, cycWeights4 a a = 0) :
    (rlp1GraphOf cycWeights4 hs hd).Connected := by
  constructor
  · intro a b
    obtain ⟨p, -⟩ := cycWalk4 hs hd a b
    exact ⟨p⟩

/-- The graph distance of the cycle graph is the cycle distance. -/
theorem cycGraph_dist
    (hs : ∀ a b, cycWeights4 a b = cycWeights4 b a)
    (hd : ∀ a, cycWeights4 a a = 0) (a b : Fin 4) :
    (rlp1GraphOf cycWeights4 hs hd).dist a b = rlp1CycDist4 a b := by
  apply le_antisymm
  · obtain ⟨p, hp⟩ := cycWalk4 hs hd a b
    rw [← hp]
    exact SimpleGraph.dist_le p
  · obtain ⟨p, hp⟩ := (cycConnected hs hd).exists_walk_length_eq_dist
      (u := a) (v := b)
    rw [← hp]
    exact rlp1CycDist4_le_of_walk hs hd p

/-- The target distance on the torus seat: the sum of the two
coordinate cycle distances (the graph distance of the Cartesian
product `C₄ □ C₄`). -/
def torusTargetDist (x y : Fin 4 × Fin 4) : ℕ :=
  rlp1CycDist4 x.1 y.1 + rlp1CycDist4 x.2 y.2

theorem torusTargetDist_symm (x y : Fin 4 × Fin 4) :
    torusTargetDist x y = torusTargetDist y x := by
  unfold torusTargetDist
  rw [rlp1CycDist4_symm x.1 y.1, rlp1CycDist4_symm x.2 y.2]

theorem torusTargetDist_self (x : Fin 4 × Fin 4) :
    torusTargetDist x x = 0 := by
  simp [torusTargetDist, rlp1CycDist4_self]

theorem torusTargetDist_triangle (x y z : Fin 4 × Fin 4) :
    torusTargetDist x z
      ≤ torusTargetDist x y + torusTargetDist y z := by
  unfold torusTargetDist
  have h1 := rlp1CycDist4_triangle x.1 y.1 z.1
  have h2 := rlp1CycDist4_triangle x.2 y.2 z.2
  omega

/-- The unit weights of the torus seat: `1` exactly at target
distance `1` (one coordinate steps, the other rests). -/
def torusWeights44 (x y : Fin 4 × Fin 4) : ℝ :=
  if torusTargetDist x y = 1 then 1 else 0

theorem torusWeights44_symm :
    ∀ x y, torusWeights44 x y = torusWeights44 y x := by
  intro x y
  by_cases h : torusTargetDist x y = 1
  · have h' : torusTargetDist y x = 1 := by
      rw [torusTargetDist_symm]; exact h
    simp [torusWeights44, h, h']
  · have h' : torusTargetDist y x ≠ 1 := by
      rw [torusTargetDist_symm]; exact h
    simp [torusWeights44, h, h']

theorem torusWeights44_diag : ∀ x, torusWeights44 x x = 0 := by
  intro x; simp [torusWeights44, torusTargetDist_self]

theorem torusWeights44_nonneg :
    ∀ x y, 0 ≤ torusWeights44 x y := by
  intro x y; unfold torusWeights44; split_ifs <;> norm_num

theorem torusWeights44_ne_zero_iff (x y : Fin 4 × Fin 4) :
    torusWeights44 x y ≠ 0 ↔ torusTargetDist x y = 1 := by
  by_cases h : torusTargetDist x y = 1 <;> simp [torusWeights44, h]

/-- Adjacency in the torus seat graph is unit target distance. -/
theorem torusAdj_iff
    (hs : ∀ x y, torusWeights44 x y = torusWeights44 y x)
    (hd : ∀ x, torusWeights44 x x = 0) (x y : Fin 4 × Fin 4) :
    (rlp1GraphOf torusWeights44 hs hd).Adj x y
      ↔ torusTargetDist x y = 1 :=
  torusWeights44_ne_zero_iff x y

/-- Every walk in the torus seat graph has length at least the
target distance of its endpoints. -/
theorem torusTargetDist_le_of_walk
    (hs : ∀ x y, torusWeights44 x y = torusWeights44 y x)
    (hd : ∀ x, torusWeights44 x x = 0) {x y : Fin 4 × Fin 4}
    (p : (rlp1GraphOf torusWeights44 hs hd).Walk x y) :
    torusTargetDist x y ≤ p.length := by
  induction p with
  | nil => simp [torusTargetDist_self]
  | @cons u v w h p ih =>
    have h1 : torusTargetDist u v = 1 := (torusAdj_iff hs hd u v).mp h
    have htri : torusTargetDist u w
        ≤ torusTargetDist u v + torusTargetDist v w :=
      torusTargetDist_triangle u v w
    rw [SimpleGraph.Walk.length_cons]
    omega

/-- A cycle walk lifts to a torus walk in the first coordinate,
the second coordinate resting. -/
theorem torusWalk_lift_fst
    (hsc : ∀ a b, cycWeights4 a b = cycWeights4 b a)
    (hdc : ∀ a, cycWeights4 a a = 0)
    (hst : ∀ x y, torusWeights44 x y = torusWeights44 y x)
    (hdt : ∀ x, torusWeights44 x x = 0) (b : Fin 4)
    {a a' : Fin 4} (p : (rlp1GraphOf cycWeights4 hsc hdc).Walk a a') :
    ∃ q : (rlp1GraphOf torusWeights44 hst hdt).Walk (a, b) (a', b),
      q.length = p.length := by
  induction p with
  | nil => exact ⟨SimpleGraph.Walk.nil, SimpleGraph.Walk.length_nil⟩
  | @cons u v w h p ih =>
    obtain ⟨q, hq⟩ := ih
    have h1 : rlp1CycDist4 u v = 1 := (cycAdj_iff hsc hdc u v).mp h
    have hadj : (rlp1GraphOf torusWeights44 hst hdt).Adj (u, b) (v, b) :=
      (torusAdj_iff hst hdt (u, b) (v, b)).mpr (by
        simp only [torusTargetDist, h1, rlp1CycDist4_self, add_zero])
    exact ⟨SimpleGraph.Walk.cons hadj q, by
      rw [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_cons,
        hq]⟩

/-- A cycle walk lifts to a torus walk in the second coordinate,
the first coordinate resting. -/
theorem torusWalk_lift_snd
    (hsc : ∀ a b, cycWeights4 a b = cycWeights4 b a)
    (hdc : ∀ a, cycWeights4 a a = 0)
    (hst : ∀ x y, torusWeights44 x y = torusWeights44 y x)
    (hdt : ∀ x, torusWeights44 x x = 0) (a : Fin 4)
    {b b' : Fin 4} (p : (rlp1GraphOf cycWeights4 hsc hdc).Walk b b') :
    ∃ q : (rlp1GraphOf torusWeights44 hst hdt).Walk (a, b) (a, b'),
      q.length = p.length := by
  induction p with
  | nil => exact ⟨SimpleGraph.Walk.nil, SimpleGraph.Walk.length_nil⟩
  | @cons u v w h p ih =>
    obtain ⟨q, hq⟩ := ih
    have h1 : rlp1CycDist4 u v = 1 := (cycAdj_iff hsc hdc u v).mp h
    have hadj : (rlp1GraphOf torusWeights44 hst hdt).Adj (a, u) (a, v) :=
      (torusAdj_iff hst hdt (a, u) (a, v)).mpr (by
        simp only [torusTargetDist, h1, rlp1CycDist4_self, zero_add])
    exact ⟨SimpleGraph.Walk.cons hadj q, by
      rw [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_cons,
        hq]⟩

/-- The torus seat graph is connected: move in the first
coordinate, then in the second. -/
theorem torusConnected
    (hsc : ∀ a b, cycWeights4 a b = cycWeights4 b a)
    (hdc : ∀ a, cycWeights4 a a = 0)
    (hst : ∀ x y, torusWeights44 x y = torusWeights44 y x)
    (hdt : ∀ x, torusWeights44 x x = 0) :
    (rlp1GraphOf torusWeights44 hst hdt).Connected := by
  constructor
  · intro x y
    obtain ⟨p₁, -⟩ := cycWalk4 hsc hdc x.1 y.1
    obtain ⟨p₂, -⟩ := cycWalk4 hsc hdc x.2 y.2
    obtain ⟨q₁, -⟩ := torusWalk_lift_fst hsc hdc hst hdt x.2 p₁
    obtain ⟨q₂, -⟩ := torusWalk_lift_snd hsc hdc hst hdt y.1 p₂
    exact ⟨q₁.append q₂⟩

/-- The graph distance of the torus seat is the target distance:
the upper bound goes through the intermediate site `(y₁, x₂)`
by appending shortest walks of the two factors. -/
theorem torusGraph_dist
    (hsc : ∀ a b, cycWeights4 a b = cycWeights4 b a)
    (hdc : ∀ a, cycWeights4 a a = 0)
    (hst : ∀ x y, torusWeights44 x y = torusWeights44 y x)
    (hdt : ∀ x, torusWeights44 x x = 0) (x y : Fin 4 × Fin 4) :
    (rlp1GraphOf torusWeights44 hst hdt).dist x y
      = torusTargetDist x y := by
  apply le_antisymm
  · obtain ⟨p₁, hp₁⟩ := cycWalk4 hsc hdc x.1 y.1
    obtain ⟨q₁, hq₁⟩ := torusWalk_lift_fst hsc hdc hst hdt x.2 p₁
    obtain ⟨p₂, hp₂⟩ := cycWalk4 hsc hdc x.2 y.2
    obtain ⟨q₂, hq₂⟩ := torusWalk_lift_snd hsc hdc hst hdt y.1 p₂
    obtain ⟨r₁, hr₁⟩ :=
      (torusConnected hsc hdc hst hdt).exists_walk_length_eq_dist
        (u := x) (v := (y.1, x.2))
    obtain ⟨r₂, hr₂⟩ :=
      (torusConnected hsc hdc hst hdt).exists_walk_length_eq_dist
        (u := (y.1, x.2)) (v := y)
    calc (rlp1GraphOf torusWeights44 hst hdt).dist x y
        ≤ (r₁.append r₂).length := SimpleGraph.dist_le _
      _ = r₁.length + r₂.length :=
          SimpleGraph.Walk.length_append r₁ r₂
      _ = (rlp1GraphOf torusWeights44 hst hdt).dist x (y.1, x.2)
          + (rlp1GraphOf torusWeights44 hst hdt).dist (y.1, x.2) y := by
          rw [hr₁, hr₂]
      _ ≤ rlp1CycDist4 x.1 y.1 + rlp1CycDist4 x.2 y.2 :=
          add_le_add
            (by calc (rlp1GraphOf torusWeights44 hst hdt).dist x (y.1, x.2)
                ≤ q₁.length := SimpleGraph.dist_le q₁
              _ = rlp1CycDist4 x.1 y.1 := hq₁.trans hp₁)
            (by calc (rlp1GraphOf torusWeights44 hst hdt).dist (y.1, x.2) y
                ≤ q₂.length := SimpleGraph.dist_le q₂
              _ = rlp1CycDist4 x.2 y.2 := hq₂.trans hp₂)
      _ = torusTargetDist x y := rfl
  · obtain ⟨p, hp⟩ :=
      (torusConnected hsc hdc hst hdt).exists_walk_length_eq_dist
        (u := x) (v := y)
    rw [← hp]
    exact torusTargetDist_le_of_walk hst hdt p

/-- The torus seat C₄ × C₄ as a packaged seat. -/
def torusSeat44 : RLP1Seat (Fin 4 × Fin 4) where
  w := torusWeights44
  symm := torusWeights44_symm
  nonneg := torusWeights44_nonneg
  diag := torusWeights44_diag
  connected := torusConnected cycWeights4_symm cycWeights4_diag
    torusWeights44_symm torusWeights44_diag

/-- The seat distance of C₄ × C₄ is the target distance. -/
theorem torusSeat44_dist (x y : Fin 4 × Fin 4) :
    torusSeat44.dist x y = torusTargetDist x y :=
  torusGraph_dist cycWeights4_symm cycWeights4_diag
    torusWeights44_symm torusWeights44_diag x y

/-- The one-coordinate row sum at `q = 1/2` on C₄: the distances
from any site are `0, 1, 1, 2`, giving `1 + 1/2 + 1/2 + 1/4 =
9/4`. -/
theorem cycRowSum_half (a : Fin 4) :
    ∑ c : Fin 4, (1/2 : ℝ) ^ rlp1CycDist4 a c = 9/4 := by
  fin_cases a <;> simp only [Fin.sum_univ_four] <;>
    norm_num [rlp1CycDist4, rlp1NatDist]

/-- **TW-P7 (C₄ × C₄ row sums, exact).** At `q = 1/2`, every row
sum of the torus seat is `81/16` — constant, as v2 §2.6
registers (the torus is vertex-transitive, unlike P₈). The sum
factorizes over the two coordinates. -/
theorem torusSeat44_rowSum (x : Fin 4 × Fin 4) :
    rlp1RowSum torusSeat44 (1/2 : ℝ) x = 81/16 := by
  simp only [rlp1RowSum, rlp1Kernel, torusSeat44_dist,
    torusTargetDist, pow_add, Fintype.sum_prod_type]
  rw [← Finset.sum_mul_sum]
  rw [cycRowSum_half, cycRowSum_half]
  norm_num

/-! ## Axiom audit (headline theorems)

Expected: exactly the standard three (`propext`,
`Classical.choice`, `Quot.sound`) for every headline below. -/

#print axioms rlp1Phi_linear
#print axioms rlp1RowSum_ge_one
#print axioms rlp1RowSum_eq_one_iff
#print axioms rlp1Phi_add_const
#print axioms rlp1Phi_add_const_ne
#print axioms rlp1Phi_not_factor_meanSub
#print axioms rlp1_const_eq
#print axioms rlp1Phi_bounds
#print axioms pathSeat8_rowSum_table
#print axioms pathSeat8_phi_single_table
#print axioms torusSeat44_rowSum

end ThetLogos
