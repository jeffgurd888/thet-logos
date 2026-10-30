import Mathlib.Tactic

/-!
# GD-PROBE-R-b: Lean certification, Seat 1 (F21 = C₇ ⋊ C₃, ρ₃)

**NO CLAIM.** Parts of any official statement closed by this
module: **0**. Dials: **0/4**. Registry: **BR1-007** (the
GD-PROBE-R-a Python verdict this module certifies). Governing:
`pack-gd-probe-r-b.md`; re-scope memo
`scoping-gd-discriminator-rescope-2026-10-30.md` §2/§5; seats
script `gdprobeR_seat.py` and its run log `gdprobeR-run.txt`.

**What is certified here (Seat 1 only, N = 4).** At
(F21, ρ₃), FULL class space (5 classes):
(1) the κ₄^dep kernel theorem — the kernel of the seat's
κ₄ form is the span of the three vectors
`(1,1,1,0,0)`, `e₃`, `e₄` (the script's extraction
nullspace basis, run log lines 42–44);
(2) **GD-iii non-firing, certified** — every channel's
restriction to that kernel is exactly zero: the five
class-space channels and Θ(2,2,2) under the (Θ-2) readings
(the Route-A-critical content: no K-Kn event at this seat);
(3) class-space proportionality multiples
λ = 10, 31, 50, 25, 7203/320 as theorems;
(4) the **Θ escape (Θ-1), proved**: the Θ orbit kernel is
nonzero, factors through NONE of the six single class
variables, and is a κ₄-pullback multiple under NONE of
them — the GD-ii content at this seat.

**GD context, on the face.** GD-strong is probe-killed by
the R-a verdict (GD-ii, via the Θ escape) pending this
certification; GD-global / GD-kernel are untouched;
GD-iii's non-firing is this brick's critical content;
Route A stands. The joint R verdict (with Seat 2) is
R-c's, not this module's.

**BRIDGE-1 notes (discrepancies flagged at full rank,
script governs).** (a) The pack's inline λ list misorders
the channels against the run log; the script's mapping is
used: (2,1,1,1) λ=10, (3,1,1,1) λ=31, (2,2,1,1)-adjacent
λ=50, (2,2,1,1)-opposite λ=25, C6 form-level λ=7203/320
(kernel-level 1/36). (b) The pack's class list
"1A, 7A, 7B, 7C, 3A" does not match the script: the five
classes are `e`, the C₇-orbits {1,2,4} and {3,5,6}
(size 3 each), and the s=1 / s=2 cosets (size 7 each,
elements of order 3). The kernel is NOT a span of class
columns: it is spanned by the profile `(1,1,1,0,0)` on
the first three classes together with the two coset unit
vectors `e₃, e₄` — exactly the script's nullspace basis
of the fiber-weighted form `F4 = D K_tot D`. The
certified statements below are the script's.

**Seat architecture.** Character/class-level, in the
corpus's probe pattern: κ₄^dep is DEFINED as the
doubled-column Gram of the character data,
`K a b = (1/648)(R_a R_b + (7/4) I_a I_b)` with
`R = Re χ_ρ₃` and `I` the imaginary part in units of
`√7/2` (so `(7/4) I_a I_b = Imχ_a Imχ_b` in ℚ); the
script's kernel `(1/648)(RRᵀ + IIᵀ)` is then a THEOREM
(`K4F21_eq`), never a definition into place. Channel
kernels are the script's extracted per-quad kernels
entered as explicit class matrices (the B6-PROBE S₃-Θ
precedent); every λ is proved against the independently
defined κ₄, never defined into place. The Θ orbit kernel
is the script's extracted 41×41 orbit matrix as explicit
data; its class variables are DERIVED in-module from the
F21 group table and the orbit representatives.
-/

namespace ThetLogos

open Finset

section GDF21Seat

/-! ## Seat data: classes, character, fibers -/

/-- Conjugacy class sizes of F21 in the script's class
order: `e`, C₇-orbit {1,2,4}, C₇-orbit {3,5,6}, s=1
coset, s=2 coset. -/
def classSizeF21 : Fin 5 → ℚ := ![1, 3, 3, 7, 7]

/-- `Re χ` of ρ₃ by class: `(3, -1/2, -1/2, 0, 0)`. -/
def chiRF21 : Fin 5 → ℚ := ![3, -1 / 2, -1 / 2, 0, 0]

/-- `Im χ` of ρ₃ by class, in units of `√7 / 2`:
`(0, 1, -1, 0, 0)`. -/
def chiIcF21 : Fin 5 → ℚ := ![0, 1, -1, 0, 0]

/-- Step-0R (iii) at the character level: `e₁ = 0`,
the size-weighted mean of `Re χ` vanishes. -/
theorem e1_F21 :
    (∑ a, classSizeF21 a * chiRF21 a) / 21 = 0 := by
  rw [Fin.sum_univ_five]
  simp [classSizeF21, chiRF21] <;> norm_num

/-- Irreducibility of ρ₃ from the character data:
`(1/21) ∑ size_a (R_a² + (7/4) I_a²) = 1`. -/
theorem chi_irred_F21 :
    (∑ a, classSizeF21 a * (chiRF21 a ^ 2 + (7 / 4) * chiIcF21 a ^ 2)) / 21
      = 1 := by
  rw [Fin.sum_univ_five]
  simp [classSizeF21, chiRF21, chiIcF21]
  norm_num

/-- Quad fibers at this seat (plaquette = wrap, script):
`[9261, 27783, 27783, 64827, 64827]`. -/
def fibQF21 : Fin 5 → ℚ := ![9261, 27783, 27783, 64827, 64827]

/-- C6 fibers at this seat (script):
`[4084101, 12252303, 12252303, 28588707, 28588707]`. -/
def fibC6F21 : Fin 5 → ℚ :=
  ![4084101, 12252303, 12252303, 28588707, 28588707]

/-- The C6 fibers are `441` times the quad fibers,
entrywise (441 = 21²). -/
theorem fibC6F21_eq (a : Fin 5) :
    fibC6F21 a = 441 * fibQF21 a := by
  fin_cases a <;> simp [fibC6F21, fibQF21] <;> norm_num

/-! ## κ₄^dep at the seat: Gram definition, script kernel -/

/-- **The seat's κ₄^dep per-quad kernel, DEFINED as the
doubled-column Gram of the character data** in the
script's normalization:
`K a b = (1/648) (R_a R_b + (7/4) I_a I_b)`, where the
`(7/4) I_a I_b` term is `Imχ_a · Imχ_b` in rational
coordinates (`Imχ = I · √7/2`). -/
def K4F21 (a b : Fin 5) : ℚ :=
  (1 / 648) * (chiRF21 a * chiRF21 b + (7 / 4) * (chiIcF21 a * chiIcF21 b))

/-- **BRIDGE-1 certificate**: the Gram definition above
reproduces the script's extracted per-quad kernel
entrywise — `[1/72, -1/432, -1/432, 0, 0; …]` (run log
line 31). -/
theorem K4F21_eq (a b : Fin 5) :
    K4F21 a b =
      ![![1 / 72, -1 / 432, -1 / 432, 0, 0],
        ![-1 / 432, 1 / 324, -1 / 432, 0, 0],
        ![-1 / 432, -1 / 432, 1 / 324, 0, 0],
        ![0, 0, 0, 0, 0],
        ![0, 0, 0, 0, 0]] a b := by
  fin_cases a <;> fin_cases b <;>
    simp [K4F21, chiRF21, chiIcF21] <;> norm_num

/-- The κ₄ kernel's **fiber-weighted** margins vanish
exactly — the script's margins-zero (the plain row sums
do NOT vanish: row 0 sums to `4/432`; the fibers are
part of the statement). -/
theorem K4F21_fibMargins (a : Fin 5) :
    ∑ b, K4F21 a b * fibQF21 b = 0 := by
  rw [Fin.sum_univ_five]
  fin_cases a <;> simp [K4F21, chiRF21, chiIcF21, fibQF21] <;> norm_num


/-- The census total kernel: `192` plaquette quads plus
`48` wrap quads; the script found the two per-quad
kernels equal, so the total is `240 • K`. -/
def K4totF21 (a b : Fin 5) : ℚ := 240 * K4F21 a b

/-- **The κ₄^dep form matrix** `F4 = D K_tot D`,
`D = diag(quad fibers)` — the script's `F4` (run log
line 36), the matrix whose kernel is deliverable (1). -/
def F4F21 (a b : Fin 5) : ℚ := fibQF21 a * K4totF21 a b * fibQF21 b

/-- The first Gram vector of the form: `u_a = fib_a · R_a`
`= (27783, -27783/2, -27783/2, 0, 0)`. -/
def uF21 (a : Fin 5) : ℚ := fibQF21 a * chiRF21 a

/-- The second Gram vector: `v_a = fib_a · I_a`
`= (0, 27783, -27783, 0, 0)`. -/
def vF21 (a : Fin 5) : ℚ := fibQF21 a * chiIcF21 a

theorem uF21_zero : uF21 0 = 27783 := by
  simp [uF21, fibQF21, chiRF21] <;> norm_num
theorem uF21_one : uF21 1 = -27783 / 2 := by
  simp [uF21, fibQF21, chiRF21] <;> norm_num
theorem uF21_two : uF21 2 = -27783 / 2 := by
  simp [uF21, fibQF21, chiRF21] <;> norm_num
theorem uF21_three : uF21 3 = 0 := by
  simp [uF21, fibQF21, chiRF21] <;> norm_num
theorem uF21_four : uF21 4 = 0 := by
  simp [uF21, fibQF21, chiRF21] <;> norm_num
theorem vF21_zero : vF21 0 = 0 := by simp [vF21, fibQF21, chiIcF21]
theorem vF21_two : vF21 2 = -27783 := by
  simp [vF21, fibQF21, chiIcF21] <;> norm_num
theorem vF21_three : vF21 3 = 0 := by
  simp [vF21, fibQF21, chiIcF21] <;> norm_num
theorem vF21_four : vF21 4 = 0 := by
  simp [vF21, fibQF21, chiIcF21] <;> norm_num
theorem vF21_one : vF21 1 = 27783 := by simp [vF21, fibQF21, chiIcF21]

/-- **Gram factorization of the κ₄ form**:
`F4 a b = (10/27) (u_a u_b + (7/4) v_a v_b)`
(`240/648 = 10/27`). -/
theorem F4F21_gram (a b : Fin 5) :
    F4F21 a b = (10 / 27) * (uF21 a * uF21 b
      + (7 / 4) * (vF21 a * vF21 b)) := by
  simp [F4F21, K4totF21, K4F21, uF21, vF21]
  ring

/-- The κ₄ form's margins vanish exactly. -/
theorem F4F21_margins (a : Fin 5) : ∑ b, F4F21 a b = 0 := by
  rw [Fin.sum_univ_five]
  fin_cases a <;>
    simp [F4F21, K4totF21, K4F21, chiRF21, chiIcF21, fibQF21] <;> norm_num

/-! ## Bilinear forms, the two kernel functionals -/

/-- The bilinear form of a class matrix. -/
def bilinOf (M : Fin 5 → Fin 5 → ℚ) (φ ψ : Fin 5 → ℚ) : ℚ :=
  ∑ a, ∑ b, φ a * M a b * ψ b

/-- The diagonal form of a class matrix. -/
def formOf (M : Fin 5 → Fin 5 → ℚ) (φ : Fin 5 → ℚ) : ℚ :=
  bilinOf M φ φ

/-- First kernel functional: `L₁ φ = ∑ a, φ_a u_a`. -/
def L1F21 (φ : Fin 5 → ℚ) : ℚ := ∑ a, φ a * uF21 a

/-- Second kernel functional: `L₂ φ = ∑ a, φ_a v_a`. -/
def L2F21 (φ : Fin 5 → ℚ) : ℚ := ∑ a, φ a * vF21 a

theorem L1F21_eq (φ : Fin 5 → ℚ) :
    L1F21 φ = 27783 * φ 0 - (27783 / 2) * φ 1 - (27783 / 2) * φ 2 := by
  rw [L1F21, Fin.sum_univ_five, uF21_zero, uF21_one, uF21_two,
    uF21_three, uF21_four]
  ring

theorem L2F21_eq (φ : Fin 5 → ℚ) :
    L2F21 φ = 27783 * φ 1 - 27783 * φ 2 := by
  rw [L2F21, Fin.sum_univ_five, vF21_zero, vF21_one, vF21_two,
    vF21_three, vF21_four]
  ring

/-- `L₁ φ = 0 ∧ L₂ φ = 0` iff `φ` is constant on the
first three classes. -/
theorem L12_eq_zero_iff (φ : Fin 5 → ℚ) :
    (L1F21 φ = 0 ∧ L2F21 φ = 0) ↔ (φ 0 = φ 1 ∧ φ 1 = φ 2) := by
  rw [L1F21_eq, L2F21_eq]
  constructor
  · rintro ⟨h1, h2⟩
    have h12 : φ 1 = φ 2 := by linarith
    refine ⟨?_, h12⟩
    rw [← h12] at h1
    linarith
  · rintro ⟨h1, h2⟩
    constructor <;> linarith

/-- **The κ₄ bilinear form, Gram-expanded**:
`φᵀ F4 ψ = (10/27) (L₁φ·L₁ψ + (7/4) L₂φ·L₂ψ)`. -/
theorem bilinOf_F4F21 (φ ψ : Fin 5 → ℚ) :
    bilinOf F4F21 φ ψ = (10 / 27) * (L1F21 φ * L1F21 ψ
      + (7 / 4) * (L2F21 φ * L2F21 ψ)) := by
  have e : ∀ a b : Fin 5, φ a * F4F21 a b * ψ b
      = ((10 / 27) * (φ a * uF21 a)) * (ψ b * uF21 b)
        + ((10 / 27) * (7 / 4) * (φ a * vF21 a)) * (ψ b * vF21 b) := by
    intro a b
    rw [F4F21_gram]
    ring
  unfold bilinOf L1F21 L2F21
  rw [Finset.sum_congr rfl (fun a _ =>
    Finset.sum_congr rfl (fun b _ => e a b))]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_add_distrib),
    Finset.sum_add_distrib, ← Finset.sum_mul_sum, ← Finset.sum_mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- The row action of the κ₄ form matrix:
`∑ a, φ_a F4 a b = (10/27)(L₁φ · u_b + (7/4) L₂φ · v_b)`. -/
theorem rowAction_F4F21 (φ : Fin 5 → ℚ) (b : Fin 5) :
    (∑ a, φ a * F4F21 a b)
      = (10 / 27) * (L1F21 φ * uF21 b + (7 / 4) * (L2F21 φ * vF21 b)) := by
  have e : ∀ a : Fin 5, φ a * F4F21 a b
      = ((10 / 27) * (φ a * uF21 a)) * uF21 b
        + ((10 / 27) * (7 / 4) * (φ a * vF21 a)) * vF21 b := by
    intro a
    rw [F4F21_gram]
    ring
  rw [Finset.sum_congr rfl (fun a _ => e a), Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum]
  unfold L1F21 L2F21
  ring

/-! ## Deliverable (1): the kernel theorem -/

/-- The three kernel basis profiles — the script's
extraction nullspace basis of `F4` (run log lines
42–44): the constant-on-`{1A, 7A, 7B}` profile and the
two coset unit vectors. -/
def kv0F21 : Fin 5 → ℚ := ![1, 1, 1, 0, 0]
def kv1F21 : Fin 5 → ℚ := ![0, 0, 0, 1, 0]
def kv2F21 : Fin 5 → ℚ := ![0, 0, 0, 0, 1]

/-- Membership in the kernel span, concretely:
`φ = c₀·kv0 + c₁·kv1 + c₂·kv2`. -/
def inKerSpanF21 (φ : Fin 5 → ℚ) : Prop :=
  ∃ c0 c1 c2 : ℚ, φ = fun a => c0 * kv0F21 a + c1 * kv1F21 a + c2 * kv2F21 a

theorem inKerSpanF21_iff (φ : Fin 5 → ℚ) :
    inKerSpanF21 φ ↔ (φ 0 = φ 1 ∧ φ 1 = φ 2) := by
  constructor
  · rintro ⟨c0, c1, c2, rfl⟩
    simp [kv0F21, kv1F21, kv2F21]
  · rintro ⟨h1, h2⟩
    refine ⟨φ 0, φ 3, φ 4, ?_⟩
    funext a
    fin_cases a <;>
      simp [kv0F21, kv1F21, kv2F21] <;> linarith

/-- **Kernel theorem, form version (deliverable 1).**
The κ₄^dep diagonal form at (F21, ρ₃) vanishes exactly
on the span of `{(1,1,1,0,0), e₃, e₄}` — a
3-dimensional kernel. -/
theorem K4F21_form_eq_zero_iff (φ : Fin 5 → ℚ) :
    formOf F4F21 φ = 0 ↔ inKerSpanF21 φ := by
  rw [formOf, bilinOf_F4F21]
  constructor
  · intro h
    have hS : L1F21 φ * L1F21 φ + (7 / 4) * (L2F21 φ * L2F21 φ) = 0 := by
      have := h
      nlinarith [this]
    have h1 : L1F21 φ * L1F21 φ = 0 := by
      have g1 : 0 ≤ L1F21 φ * L1F21 φ := mul_self_nonneg _
      have g2 : 0 ≤ (7 / 4 : ℚ) * (L2F21 φ * L2F21 φ) := by
        apply mul_nonneg (by norm_num) (mul_self_nonneg _)
      linarith
    have h2 : L2F21 φ * L2F21 φ = 0 := by
      have g1 : 0 ≤ L1F21 φ * L1F21 φ := mul_self_nonneg _
      have g2 : 0 ≤ (7 / 4 : ℚ) * (L2F21 φ * L2F21 φ) := by
        apply mul_nonneg (by norm_num) (mul_self_nonneg _)
      nlinarith
    have hL : L1F21 φ = 0 ∧ L2F21 φ = 0 :=
      ⟨mul_self_eq_zero.mp h1, mul_self_eq_zero.mp h2⟩
    rw [inKerSpanF21_iff]
    exact (L12_eq_zero_iff φ).mp hL
  · intro h
    have hL : L1F21 φ = 0 ∧ L2F21 φ = 0 :=
      (L12_eq_zero_iff φ).mpr ((inKerSpanF21_iff φ).mp h)
    rw [hL.1, hL.2]
    norm_num

/-- **Kernel theorem, matrix version (deliverable 1).**
`φ` is annihilated by the κ₄^dep form matrix
(`∑ a, φ_a F4 a b = 0` for every `b`) iff it lies in
the same span. For this Gram form the two kernels
coincide. -/
theorem K4F21_matrixKer_iff (φ : Fin 5 → ℚ) :
    (∀ b, (∑ a, φ a * F4F21 a b) = 0) ↔ inKerSpanF21 φ := by
  constructor
  · intro h
    have h0 := h 0
    rw [rowAction_F4F21, uF21_zero, vF21_zero] at h0
    have hL1 : L1F21 φ = 0 := by nlinarith [h0]
    have h1 := h 1
    rw [rowAction_F4F21, uF21_one, vF21_one, hL1] at h1
    have hL2 : L2F21 φ = 0 := by nlinarith [h1]
    rw [inKerSpanF21_iff]
    exact (L12_eq_zero_iff φ).mp ⟨hL1, hL2⟩
  · intro h b
    have hL : L1F21 φ = 0 ∧ L2F21 φ = 0 :=
      (L12_eq_zero_iff φ).mpr ((inKerSpanF21_iff φ).mp h)
    rw [rowAction_F4F21, hL.1, hL.2]
    norm_num

/-- The kernel is exactly 3-dimensional: the three
basis profiles are linearly independent (evaluation at
classes 0, 3, 4 separates the coefficients) and span
the kernel by `K4F21_form_eq_zero_iff`. -/
theorem kv_independentF21 (c0 c1 c2 : ℚ)
    (h : (fun a => c0 * kv0F21 a + c1 * kv1F21 a + c2 * kv2F21 a)
      = fun _ => 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 := by
  have h0 := congrFun h 0
  have h3 := congrFun h 3
  have h4 := congrFun h 4
  simp [kv0F21, kv1F21, kv2F21] at h0 h3 h4
  exact ⟨h0, h3, h4⟩

end GDF21Seat

section GDF21Channels

/-! ## The five class-space channels: extracted kernels -/

/-- The order-5 channel (2,1,1,1) per-quad kernel at
this seat — the script's extracted matrix (run log
line 57). -/
def K2111F21 : Fin 5 → Fin 5 → ℚ :=
  ![![5 / 36, -5 / 216, -5 / 216, 0, 0],
    ![-5 / 216, 5 / 162, -5 / 216, 0, 0],
    ![-5 / 216, -5 / 216, 5 / 162, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0]]

/-- The order-6 channel (3,1,1,1) per-quad kernel
(run log line 64). -/
def K3111F21 : Fin 5 → Fin 5 → ℚ :=
  ![![31 / 72, -31 / 432, -31 / 432, 0, 0],
    ![-31 / 432, 31 / 324, -31 / 432, 0, 0],
    ![-31 / 432, -31 / 432, 31 / 324, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0]]

/-- The order-6 channel (2,2,1,1)-adjacent per-quad
kernel (run log line 71). -/
def K2211adjF21 : Fin 5 → Fin 5 → ℚ :=
  ![![25 / 36, -25 / 216, -25 / 216, 0, 0],
    ![-25 / 216, 25 / 162, -25 / 216, 0, 0],
    ![-25 / 216, -25 / 216, 25 / 162, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0]]

/-- The order-6 channel (2,2,1,1)-opposite per-quad
kernel (run log line 78). -/
def K2211oppF21 : Fin 5 → Fin 5 → ℚ :=
  ![![25 / 72, -25 / 432, -25 / 432, 0, 0],
    ![-25 / 432, 25 / 324, -25 / 432, 0, 0],
    ![-25 / 432, -25 / 432, 25 / 324, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0]]

/-- The order-6 channel C6 per-support kernel
(run log line 88). -/
def KC6F21 : Fin 5 → Fin 5 → ℚ :=
  ![![1 / 2592, -1 / 15552, -1 / 15552, 0, 0],
    ![-1 / 15552, 1 / 11664, -1 / 15552, 0, 0],
    ![-1 / 15552, -1 / 15552, 1 / 11664, 0, 0],
    ![0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0]]

/-- A quad channel's form matrix: quad fibers and the
census factor `240`, as for κ₄. -/
def quadFormOf (K : Fin 5 → Fin 5 → ℚ) (a b : Fin 5) : ℚ :=
  fibQF21 a * (240 * K a b) * fibQF21 b

/-- The C6 channel's form matrix: C6 fibers times the
per-support kernel (the script's `form_matrix`). -/
def FC6F21 (a b : Fin 5) : ℚ := fibC6F21 a * KC6F21 a b * fibC6F21 b

/-! ## Deliverable (3): proportionality, kernel level -/

/-- (2,1,1,1) kernel `= 10 · κ₄` kernel. -/
theorem K2111F21_prop (a b : Fin 5) :
    K2111F21 a b = 10 * K4F21 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [K2111F21, K4F21, chiRF21, chiIcF21] <;> norm_num

/-- (3,1,1,1) kernel `= 31 · κ₄` kernel. -/
theorem K3111F21_prop (a b : Fin 5) :
    K3111F21 a b = 31 * K4F21 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [K3111F21, K4F21, chiRF21, chiIcF21] <;> norm_num

/-- (2,2,1,1)-adjacent kernel `= 50 · κ₄` kernel. -/
theorem K2211adjF21_prop (a b : Fin 5) :
    K2211adjF21 a b = 50 * K4F21 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [K2211adjF21, K4F21, chiRF21, chiIcF21] <;> norm_num

/-- (2,2,1,1)-opposite kernel `= 25 · κ₄` kernel. -/
theorem K2211oppF21_prop (a b : Fin 5) :
    K2211oppF21 a b = 25 * K4F21 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [K2211oppF21, K4F21, chiRF21, chiIcF21] <;> norm_num

/-- C6 per-support kernel `= (1/36) · κ₄` kernel. -/
theorem KC6F21_prop (a b : Fin 5) :
    KC6F21 a b = (1 / 36) * K4F21 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [KC6F21, K4F21, chiRF21, chiIcF21] <;> norm_num

/-! ## Deliverable (3): proportionality, form level -/

/-- Bilinear forms respect entrywise proportionality. -/
theorem bilinOf_of_entrywise {M M' : Fin 5 → Fin 5 → ℚ} {lam : ℚ}
    (h : ∀ a b, M a b = lam * M' a b) (φ ψ : Fin 5 → ℚ) :
    bilinOf M φ ψ = lam * bilinOf M' φ ψ := by
  have e : ∀ a b, φ a * M a b * ψ b
      = lam * (φ a * M' a b * ψ b) := by
    intro a b
    rw [h a b]
    ring
  unfold bilinOf
  rw [Finset.sum_congr rfl (fun a _ =>
    Finset.sum_congr rfl (fun b _ => e a b)), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]

/-- (2,1,1,1) form `= 10 · κ₄` form, λ = 10 > 0. -/
theorem F2111F21_prop (φ ψ : Fin 5 → ℚ) :
    bilinOf (quadFormOf K2111F21) φ ψ = 10 * bilinOf F4F21 φ ψ := by
  apply bilinOf_of_entrywise
  intro a b
  rw [quadFormOf, F4F21, K4totF21, K2111F21_prop]
  ring

/-- (3,1,1,1) form `= 31 · κ₄` form, λ = 31 > 0. -/
theorem F3111F21_prop (φ ψ : Fin 5 → ℚ) :
    bilinOf (quadFormOf K3111F21) φ ψ = 31 * bilinOf F4F21 φ ψ := by
  apply bilinOf_of_entrywise
  intro a b
  rw [quadFormOf, F4F21, K4totF21, K3111F21_prop]
  ring

/-- (2,2,1,1)-adjacent form `= 50 · κ₄` form,
λ = 50 > 0. -/
theorem F2211adjF21_prop (φ ψ : Fin 5 → ℚ) :
    bilinOf (quadFormOf K2211adjF21) φ ψ
      = 50 * bilinOf F4F21 φ ψ := by
  apply bilinOf_of_entrywise
  intro a b
  rw [quadFormOf, F4F21, K4totF21, K2211adjF21_prop]
  ring

/-- (2,2,1,1)-opposite form `= 25 · κ₄` form,
λ = 25 > 0. -/
theorem F2211oppF21_prop (φ ψ : Fin 5 → ℚ) :
    bilinOf (quadFormOf K2211oppF21) φ ψ
      = 25 * bilinOf F4F21 φ ψ := by
  apply bilinOf_of_entrywise
  intro a b
  rw [quadFormOf, F4F21, K4totF21, K2211oppF21_prop]
  ring

/-- **C6 form `= (7203/320) · κ₄` form** — the
form-level multiple: kernel multiple `1/36`, fiber
ratio `441²`, census factor `240`:
`441² / (36 · 240) = 7203/320 > 0`. -/
theorem FC6F21_prop_entry (a b : Fin 5) :
    FC6F21 a b = (7203 / 320) * F4F21 a b := by
  rw [FC6F21, F4F21, K4totF21, KC6F21_prop, fibC6F21_eq, fibC6F21_eq]
  ring

theorem FC6F21_prop (φ ψ : Fin 5 → ℚ) :
    bilinOf FC6F21 φ ψ = (7203 / 320) * bilinOf F4F21 φ ψ :=
  bilinOf_of_entrywise FC6F21_prop_entry φ ψ

/-- The five form-level multiples are all positive. -/
theorem lambdas_pos_F21 :
    (0:ℚ) < 10 ∧ (0:ℚ) < 31 ∧ (0:ℚ) < 50 ∧ (0:ℚ) < 25
      ∧ (0:ℚ) < 7203 / 320 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num⟩

/-! ## Deliverable (2), class channels: GD-iii non-firing -/

/-- The κ₄ bilinear form vanishes on kernel pairs —
immediate from the Gram expansion. -/
theorem bilinOf_F4F21_of_ker {φ ψ : Fin 5 → ℚ}
    (hφ : L1F21 φ = 0 ∧ L2F21 φ = 0)
    (hψ : L1F21 ψ = 0 ∧ L2F21 ψ = 0) :
    bilinOf F4F21 φ ψ = 0 := by
  rw [bilinOf_F4F21, hφ.1, hφ.2, hψ.1, hψ.2]
  norm_num

/-- Kernel-span membership gives the `L₁ = L₂ = 0`
functionals. -/
theorem L12_of_inKerSpan {φ : Fin 5 → ℚ} (h : inKerSpanF21 φ) :
    L1F21 φ = 0 ∧ L2F21 φ = 0 :=
  (L12_eq_zero_iff φ).mpr ((inKerSpanF21_iff φ).mp h)

/-- **GD-iii non-firing, (2,1,1,1)**: restriction to
`ker κ₄^dep` is exactly zero (bilinear, hence also
diagonal). -/
theorem restrict_K2111F21_zero {φ ψ : Fin 5 → ℚ}
    (hφ : inKerSpanF21 φ) (hψ : inKerSpanF21 ψ) :
    bilinOf (quadFormOf K2111F21) φ ψ = 0 := by
  rw [F2111F21_prop, bilinOf_F4F21_of_ker
    (L12_of_inKerSpan hφ) (L12_of_inKerSpan hψ)]
  norm_num

/-- **GD-iii non-firing, (3,1,1,1)**. -/
theorem restrict_K3111F21_zero {φ ψ : Fin 5 → ℚ}
    (hφ : inKerSpanF21 φ) (hψ : inKerSpanF21 ψ) :
    bilinOf (quadFormOf K3111F21) φ ψ = 0 := by
  rw [F3111F21_prop, bilinOf_F4F21_of_ker
    (L12_of_inKerSpan hφ) (L12_of_inKerSpan hψ)]
  norm_num

/-- **GD-iii non-firing, (2,2,1,1)-adjacent**. -/
theorem restrict_K2211adjF21_zero {φ ψ : Fin 5 → ℚ}
    (hφ : inKerSpanF21 φ) (hψ : inKerSpanF21 ψ) :
    bilinOf (quadFormOf K2211adjF21) φ ψ = 0 := by
  rw [F2211adjF21_prop, bilinOf_F4F21_of_ker
    (L12_of_inKerSpan hφ) (L12_of_inKerSpan hψ)]
  norm_num

/-- **GD-iii non-firing, (2,2,1,1)-opposite**. -/
theorem restrict_K2211oppF21_zero {φ ψ : Fin 5 → ℚ}
    (hφ : inKerSpanF21 φ) (hψ : inKerSpanF21 ψ) :
    bilinOf (quadFormOf K2211oppF21) φ ψ = 0 := by
  rw [F2211oppF21_prop, bilinOf_F4F21_of_ker
    (L12_of_inKerSpan hφ) (L12_of_inKerSpan hψ)]
  norm_num

/-- **GD-iii non-firing, C6**. -/
theorem restrict_C6F21_zero {φ ψ : Fin 5 → ℚ}
    (hφ : inKerSpanF21 φ) (hψ : inKerSpanF21 ψ) :
    bilinOf FC6F21 φ ψ = 0 := by
  rw [FC6F21_prop, bilinOf_F4F21_of_ker
    (L12_of_inKerSpan hφ) (L12_of_inKerSpan hψ)]
  norm_num

end GDF21Channels

section GDF21Theta

/-! ## Θ(2,2,2) at the seat: group data, orbits, kernel -/

/-- F21 multiplication table: element id `s*7 + a` for
`(a, s) ∈ ZMod 7 × ZMod 3`, product
`(a + 2^s * b, s + t)` — the script's `MUL` table. -/
def mulF21 : Fin 21 → Fin 21 → Fin 21 :=
  ![    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20],
    ![1, 2, 3, 4, 5, 6, 0, 8, 9, 10, 11, 12, 13, 7, 15, 16, 17, 18, 19, 20, 14],
    ![2, 3, 4, 5, 6, 0, 1, 9, 10, 11, 12, 13, 7, 8, 16, 17, 18, 19, 20, 14, 15],
    ![3, 4, 5, 6, 0, 1, 2, 10, 11, 12, 13, 7, 8, 9, 17, 18, 19, 20, 14, 15, 16],
    ![4, 5, 6, 0, 1, 2, 3, 11, 12, 13, 7, 8, 9, 10, 18, 19, 20, 14, 15, 16, 17],
    ![5, 6, 0, 1, 2, 3, 4, 12, 13, 7, 8, 9, 10, 11, 19, 20, 14, 15, 16, 17, 18],
    ![6, 0, 1, 2, 3, 4, 5, 13, 7, 8, 9, 10, 11, 12, 20, 14, 15, 16, 17, 18, 19],
    ![7, 9, 11, 13, 8, 10, 12, 14, 16, 18, 20, 15, 17, 19, 0, 2, 4, 6, 1, 3, 5],
    ![8, 10, 12, 7, 9, 11, 13, 15, 17, 19, 14, 16, 18, 20, 1, 3, 5, 0, 2, 4, 6],
    ![9, 11, 13, 8, 10, 12, 7, 16, 18, 20, 15, 17, 19, 14, 2, 4, 6, 1, 3, 5, 0],
    ![10, 12, 7, 9, 11, 13, 8, 17, 19, 14, 16, 18, 20, 15, 3, 5, 0, 2, 4, 6, 1],
    ![11, 13, 8, 10, 12, 7, 9, 18, 20, 15, 17, 19, 14, 16, 4, 6, 1, 3, 5, 0, 2],
    ![12, 7, 9, 11, 13, 8, 10, 19, 14, 16, 18, 20, 15, 17, 5, 0, 2, 4, 6, 1, 3],
    ![13, 8, 10, 12, 7, 9, 11, 20, 15, 17, 19, 14, 16, 18, 6, 1, 3, 5, 0, 2, 4],
    ![14, 18, 15, 19, 16, 20, 17, 0, 4, 1, 5, 2, 6, 3, 7, 11, 8, 12, 9, 13, 10],
    ![15, 19, 16, 20, 17, 14, 18, 1, 5, 2, 6, 3, 0, 4, 8, 12, 9, 13, 10, 7, 11],
    ![16, 20, 17, 14, 18, 15, 19, 2, 6, 3, 0, 4, 1, 5, 9, 13, 10, 7, 11, 8, 12],
    ![17, 14, 18, 15, 19, 16, 20, 3, 0, 4, 1, 5, 2, 6, 10, 7, 11, 8, 12, 9, 13],
    ![18, 15, 19, 16, 20, 17, 14, 4, 1, 5, 2, 6, 3, 0, 11, 8, 12, 9, 13, 10, 7],
    ![19, 16, 20, 17, 14, 18, 15, 5, 2, 6, 3, 0, 4, 1, 12, 9, 13, 10, 7, 11, 8],
    ![20, 17, 14, 18, 15, 19, 16, 6, 3, 0, 4, 1, 5, 2, 13, 10, 7, 11, 8, 12, 9]]

/-- Inverses in F21 — the script's `INV`. -/
def invF21 : Fin 21 → Fin 21 :=
  ![0, 6, 5, 4, 3, 2, 1, 14, 17, 20, 16, 19, 15, 18, 7, 12, 10, 8, 13, 11, 9]

/-- Conjugacy class of an F21 element (the script's
`CLS`): ids 0–6 are the `s = 0` slice (id 0 = `e`;
`{1,2,4}` class 1; `{3,5,6}` class 2), ids 7–13 the
`s = 1` coset (class 3), ids 14–20 the `s = 2` coset
(class 4). -/
def clsF21 : Fin 21 → Fin 5 :=
  ![0, 1, 1, 2, 1, 2, 2, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4]

/-- The 41 Θ gauge-orbit representatives `(g₃, g₅)`
(element ids), in the script's orbit order. -/
def orbRepF21 : Fin 41 → Fin 21 × Fin 21 :=
  ![(0, 0), (0, 1), (0, 3), (0, 7), (0, 14), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 14), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 14), (7, 0), (7, 1), (7, 3), (7, 7), (7, 8), (7, 10), (7, 14), (7, 15), (7, 17), (14, 0), (14, 1), (14, 3), (14, 7), (14, 8), (14, 10), (14, 14), (14, 15), (14, 17)]

/-- Class variable `g₃`: class of the first orbit
component. -/
def tvG3F21 (p : Fin 41) : Fin 5 := clsF21 (orbRepF21 p).1

/-- Class variable `g₅`. -/
def tvG5F21 (p : Fin 41) : Fin 5 := clsF21 (orbRepF21 p).2

/-- Class variable `g₃g₅`. -/
def tvG3G5F21 (p : Fin 41) : Fin 5 :=
  clsF21 (mulF21 (orbRepF21 p).1 (orbRepF21 p).2)

/-- Class variable `g₅g₃`. -/
def tvG5G3F21 (p : Fin 41) : Fin 5 :=
  clsF21 (mulF21 (orbRepF21 p).2 (orbRepF21 p).1)

/-- Class variable `g₃g₅⁻¹`. -/
def tvG3G5invF21 (p : Fin 41) : Fin 5 :=
  clsF21 (mulF21 (orbRepF21 p).1 (invF21 (orbRepF21 p).2))

/-- Class variable `g₃⁻¹g₅` (the third (Θ-2) cycle
reading). -/
def tvG3invG5F21 (p : Fin 41) : Fin 5 :=
  clsF21 (mulF21 (invF21 (orbRepF21 p).1) (orbRepF21 p).2)

/-- Θ orbit fiber counts — the script's `fibT`. -/
def fibThetaF21 : Fin 41 → ℚ :=
  ![194481, 583443, 583443, 1361367, 1361367, 583443, 583443, 583443, 583443, 583443, 583443, 583443, 4084101, 4084101, 583443, 583443, 583443, 583443, 583443, 583443, 583443, 4084101, 4084101, 1361367, 4084101, 4084101, 1361367, 4084101, 4084101, 1361367, 4084101, 4084101, 1361367, 4084101, 4084101, 1361367, 4084101, 4084101, 1361367, 4084101, 4084101]

/-- Support block A of the Θ kernel: the 17 orbits
whose representatives lie in the C₇ subgroup. -/
def blockAF21 : Finset (Fin 41) :=
  {0, 1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20}

/-- Support block B: orbits 29–31. -/
def blockBF21 : Finset (Fin 41) := {29, 30, 31}

/-- Support block C: orbits 35–37. -/
def blockCF21 : Finset (Fin 41) := {35, 36, 37}

/-- The support block of an orbit (`∅` off the three
blocks). -/
def blockOfF21 (p : Fin 41) : Finset (Fin 41) :=
  if p ∈ blockAF21 then blockAF21
  else if p ∈ blockBF21 then blockBF21
  else if p ∈ blockCF21 then blockCF21
  else ∅

/-- Position of an orbit inside block A (`0` outside). -/
def posAF21 : Fin 41 → Fin 17 :=
  ![0, 1, 2, 0, 0, 3, 4, 5, 6, 7, 8, 9, 0, 0, 10, 11, 12, 13, 14, 15, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Position inside block B (`0` outside). -/
def posBF21 : Fin 41 → Fin 3 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Position inside block C (`0` outside). -/
def posCF21 : Fin 41 → Fin 3 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0]

/-- The Θ kernel's block A (17×17) — the script's
extracted orbit kernel restricted to block A. -/
def KThetaAF21 : Fin 17 → Fin 17 → ℚ :=
  ![    ![5/864, -5/5184, -5/5184, -5/5184, -5/5184, 1/2592, 1/2592, 1/2592, 1/2592, 1/2592, -5/5184, 1/2592, 1/2592, -5/5184, 1/2592, 1/2592, 1/2592],
    ![-5/5184, 5/3888, -5/5184, 1/2592, -1/15552, -1/1944, -1/15552, -1/15552, -1/15552, 1/2592, -1/15552, -1/15552, -1/15552, 1/2592, -1/1944, -1/15552, 1/2592],
    ![-5/5184, -5/5184, 5/3888, -1/15552, 1/2592, 1/2592, -1/15552, -1/15552, -1/15552, -1/1944, 1/2592, -1/15552, -1/15552, -1/15552, 1/2592, -1/15552, -1/1944],
    ![-5/5184, 1/2592, -1/15552, 5/3888, -1/15552, -1/15552, -1/15552, -1/1944, -1/15552, -1/1944, -5/5184, -1/15552, -1/15552, 1/2592, 1/2592, 1/2592, -1/15552],
    ![-5/5184, -1/15552, 1/2592, -1/15552, 5/3888, -1/1944, -1/15552, -1/1944, -1/15552, -1/15552, 1/2592, -1/15552, -1/15552, -5/5184, -1/15552, 1/2592, 1/2592],
    ![1/2592, -1/1944, 1/2592, -1/15552, -1/1944, 17/7776, -1/1944, -1/1944, -1/1944, -1/15552, -1/15552, -1/15552, -1/15552, 1/2592, -1/1944, -1/15552, 1/2592],
    ![1/2592, -1/15552, -1/15552, -1/15552, -1/15552, -1/1944, 17/7776, -1/15552, -5/5184, -1/1944, -1/15552, 1/2592, 1/2592, -1/15552, -1/15552, -1/1944, -1/15552],
    ![1/2592, -1/15552, -1/15552, -1/1944, -1/1944, -1/1944, -1/15552, 17/7776, -1/15552, -1/1944, 1/2592, -1/1944, -1/1944, 1/2592, -1/15552, 1/2592, -1/15552],
    ![1/2592, -1/15552, -1/15552, -1/15552, -1/15552, -1/1944, -5/5184, -1/15552, 17/7776, -1/1944, -1/15552, 1/2592, 1/2592, -1/15552, -1/15552, -1/1944, -1/15552],
    ![1/2592, 1/2592, -1/1944, -1/1944, -1/15552, -1/15552, -1/1944, -1/1944, -1/1944, 17/7776, 1/2592, -1/15552, -1/15552, -1/15552, 1/2592, -1/15552, -1/1944],
    ![-5/5184, -1/15552, 1/2592, -5/5184, 1/2592, -1/15552, -1/15552, 1/2592, -1/15552, 1/2592, 5/3888, -1/15552, -1/15552, -1/15552, -1/1944, -1/1944, -1/15552],
    ![1/2592, -1/15552, -1/15552, -1/15552, -1/15552, -1/15552, 1/2592, -1/1944, 1/2592, -1/15552, -1/15552, 17/7776, -5/5184, -1/15552, -1/1944, -1/15552, -1/1944],
    ![1/2592, -1/15552, -1/15552, -1/15552, -1/15552, -1/15552, 1/2592, -1/1944, 1/2592, -1/15552, -1/15552, -5/5184, 17/7776, -1/15552, -1/1944, -1/15552, -1/1944],
    ![-5/5184, 1/2592, -1/15552, 1/2592, -5/5184, 1/2592, -1/15552, 1/2592, -1/15552, -1/15552, -1/15552, -1/15552, -1/15552, 5/3888, -1/15552, -1/1944, -1/1944],
    ![1/2592, -1/1944, 1/2592, 1/2592, -1/15552, -1/1944, -1/15552, -1/15552, -1/15552, 1/2592, -1/1944, -1/1944, -1/1944, -1/15552, 17/7776, -1/1944, -1/15552],
    ![1/2592, -1/15552, -1/15552, 1/2592, 1/2592, -1/15552, -1/1944, 1/2592, -1/1944, -1/15552, -1/1944, -1/15552, -1/15552, -1/1944, -1/1944, 17/7776, -1/1944],
    ![1/2592, 1/2592, -1/1944, -1/15552, 1/2592, 1/2592, -1/15552, -1/15552, -1/15552, -1/1944, -1/15552, -1/1944, -1/1944, -1/1944, -1/15552, -1/1944, 17/7776]]

/-- The Θ kernel's block B (3×3). -/
def KThetaBF21 : Fin 3 → Fin 3 → ℚ :=
  ![    ![1/864, -1/5184, -1/5184],
    ![-1/5184, 1/3888, -1/5184],
    ![-1/5184, -1/5184, 1/3888]]

/-- The Θ kernel's block C (3×3). -/
def KThetaCF21 : Fin 3 → Fin 3 → ℚ :=
  ![    ![1/864, -1/5184, -1/5184],
    ![-1/5184, 1/3888, -1/5184],
    ![-1/5184, -1/5184, 1/3888]]

/-- Block A as an indexed family of orbits. -/
def orbAF21 : Fin 17 → Fin 41 :=
  ![0, 1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20]

/-- Block B as an indexed family of orbits. -/
def orbBF21 : Fin 3 → Fin 41 := ![29, 30, 31]

/-- Block C as an indexed family of orbits. -/
def orbCF21 : Fin 3 → Fin 41 := ![35, 36, 37]

theorem orbA_posA {p : Fin 41} (hp : p ∈ blockAF21) :
    orbAF21 (posAF21 p) = p := by
  fin_cases p <;> simp [orbAF21, posAF21, blockAF21] at hp ⊢

theorem orbB_posB {p : Fin 41} (hp : p ∈ blockBF21) :
    orbBF21 (posBF21 p) = p := by
  fin_cases p <;> simp [orbBF21, posBF21, blockBF21] at hp ⊢

theorem orbC_posC {p : Fin 41} (hp : p ∈ blockCF21) :
    orbCF21 (posCF21 p) = p := by
  fin_cases p <;> simp [orbCF21, posCF21, blockCF21] at hp ⊢

/-- **The Θ(2,2,2) orbit kernel at (F21, ρ₃)**: the
script's extracted 41×41 kernel (BR1-007), block
diagonal with blocks A/B/C above and zero elsewhere —
the block support was verified entrywise against the
script's matrix at generation time. -/
def KThetaF21 (p q : Fin 41) : ℚ :=
  if p ∈ blockAF21 then
    (if q ∈ blockAF21 then KThetaAF21 (posAF21 p) (posAF21 q) else 0)
  else if p ∈ blockBF21 then
    (if q ∈ blockBF21 then KThetaBF21 (posBF21 p) (posBF21 q) else 0)
  else if p ∈ blockCF21 then
    (if q ∈ blockCF21 then KThetaCF21 (posCF21 p) (posCF21 q) else 0)
  else 0

/-- The Θ form matrix: fiber-weighted orbit kernel. -/
def FThetaF21 (p q : Fin 41) : ℚ :=
  fibThetaF21 p * KThetaF21 p q * fibThetaF21 q

/-- Support: the Θ kernel vanishes outside its
support block. -/
theorem KTheta_eq_zero_of_not_mem {p q : Fin 41}
    (h : q ∉ blockOfF21 p) : KThetaF21 p q = 0 := by
  unfold KThetaF21 blockOfF21 at *
  by_cases hA : p ∈ blockAF21
  · rw [if_pos hA] at h ⊢
    exact if_neg h
  · by_cases hB : p ∈ blockBF21
    · rw [if_neg hA, if_pos hB] at h ⊢
      exact if_neg h
    · by_cases hC : p ∈ blockCF21
      · rw [if_neg hA, if_neg hB, if_pos hC] at h ⊢
        exact if_neg h
      · rw [if_neg hA, if_neg hB, if_neg hC] at h ⊢

/-! ## Θ entries and class-variable values (witness data) -/

theorem KTheta_entry_0_0 : KThetaF21 0 0 = 5 / 864 := by
  simp [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
    posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21] <;> norm_num

theorem KTheta_entry_0_1 : KThetaF21 0 1 = -5 / 5184 := by
  simp [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
    posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21] <;> norm_num

theorem KTheta_entry_0_2 : KThetaF21 0 2 = -5 / 5184 := by
  simp [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
    posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21] <;> norm_num

theorem KTheta_entry_0_5 : KThetaF21 0 5 = -5 / 5184 := by
  simp [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
    posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21] <;> norm_num

theorem KTheta_entry_0_6 : KThetaF21 0 6 = -5 / 5184 := by
  simp [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
    posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21] <;> norm_num

theorem KTheta_entry_0_7 : KThetaF21 0 7 = 1 / 2592 := by
  simp [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
    posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21] <;> norm_num

/-- The Θ orbit kernel is not the zero kernel. -/
theorem KTheta_ne_zero : KThetaF21 0 0 ≠ 0 := by
  rw [KTheta_entry_0_0]
  norm_num

theorem tvG3F21_0 : tvG3F21 0 = 0 := by
  simp [tvG3F21, orbRepF21, clsF21, mulF21, invF21]
theorem tvG3F21_1 : tvG3F21 1 = 0 := by
  simp [tvG3F21, orbRepF21, clsF21, mulF21, invF21]
theorem tvG5F21_0 : tvG5F21 0 = 0 := by
  simp [tvG5F21, orbRepF21, clsF21, mulF21, invF21]
theorem tvG5F21_5 : tvG5F21 5 = 0 := by
  simp [tvG5F21, orbRepF21, clsF21, mulF21, invF21]
theorem tvG3G5F21_0 : tvG3G5F21 0 = 0 := by
  simp [tvG3G5F21, orbRepF21, clsF21, mulF21, invF21]
theorem tvG3G5F21_2 : tvG3G5F21 2 = 2 := by
  simp [tvG3G5F21, orbRepF21, clsF21, mulF21, invF21]
theorem tvG3G5F21_7 : tvG3G5F21 7 = 2 := by
  simp [tvG3G5F21, orbRepF21, clsF21, mulF21, invF21]
theorem tvG5G3F21_0 : tvG5G3F21 0 = 0 := by
  simp [tvG5G3F21, orbRepF21, clsF21, mulF21, invF21]
theorem tvG5G3F21_2 : tvG5G3F21 2 = 2 := by
  simp [tvG5G3F21, orbRepF21, clsF21, mulF21, invF21]
theorem tvG5G3F21_7 : tvG5G3F21 7 = 2 := by
  simp [tvG5G3F21, orbRepF21, clsF21, mulF21, invF21]
theorem tvG3G5invF21_0 : tvG3G5invF21 0 = 0 := by
  simp [tvG3G5invF21, orbRepF21, clsF21, mulF21, invF21]
theorem tvG3G5invF21_6 : tvG3G5invF21 6 = 0 := by
  simp [tvG3G5invF21, orbRepF21, clsF21, mulF21, invF21]
theorem tvG3invG5F21_0 : tvG3invG5F21 0 = 0 := by
  simp [tvG3invG5F21, orbRepF21, clsF21, mulF21, invF21]
theorem tvG3invG5F21_6 : tvG3invG5F21 6 = 0 := by
  simp [tvG3invG5F21, orbRepF21, clsF21, mulF21, invF21]

theorem K4F21_0_0 : K4F21 0 0 = 1 / 72 := by
  simp [K4F21, chiRF21, chiIcF21] <;> norm_num

theorem K4F21_0_2 : K4F21 0 2 = -1 / 432 := by
  simp [K4F21, chiRF21, chiIcF21] <;> norm_num

/-! ## Deliverable (4): the Θ escape (Θ-1), proved -/

/-- **Θ-escape, `g₃` factorization fails**: orbits
`(0,0)` and `(0,1)` have the same `g₃`-class pair
`(0,0)` but Θ values `5/864 ≠ -5/5184`. -/
theorem theta_not_factor_g3 :
    ¬ ∃ E : Fin 5 → Fin 5 → ℚ,
      ∀ p q, KThetaF21 p q = E (tvG3F21 p) (tvG3F21 q) := by
  rintro ⟨E, hE⟩
  have h1 := hE 0 0
  have h2 := hE 0 1
  rw [KTheta_entry_0_0, tvG3F21_0] at h1
  rw [KTheta_entry_0_1, tvG3F21_0, tvG3F21_1] at h2
  linarith

/-- **Θ-escape, `g₅` factorization fails** (orbits
`(0,0)` vs `(0,5)`). -/
theorem theta_not_factor_g5 :
    ¬ ∃ E : Fin 5 → Fin 5 → ℚ,
      ∀ p q, KThetaF21 p q = E (tvG5F21 p) (tvG5F21 q) := by
  rintro ⟨E, hE⟩
  have h1 := hE 0 0
  have h2 := hE 0 5
  rw [KTheta_entry_0_0, tvG5F21_0] at h1
  rw [KTheta_entry_0_5, tvG5F21_0, tvG5F21_5] at h2
  linarith

/-- **Θ-escape, `g₃g₅` factorization fails** (orbits
`(0,2)` vs `(0,7)`, same class pair `(0,2)`, values
`-5/5184 ≠ 1/2592`). -/
theorem theta_not_factor_g3g5 :
    ¬ ∃ E : Fin 5 → Fin 5 → ℚ,
      ∀ p q, KThetaF21 p q = E (tvG3G5F21 p) (tvG3G5F21 q) := by
  rintro ⟨E, hE⟩
  have h1 := hE 0 2
  have h2 := hE 0 7
  rw [KTheta_entry_0_2, tvG3G5F21_0, tvG3G5F21_2] at h1
  rw [KTheta_entry_0_7, tvG3G5F21_0, tvG3G5F21_7] at h2
  linarith

/-- **Θ-escape, `g₅g₃` factorization fails** (same
witness orbits as `g₃g₅`). -/
theorem theta_not_factor_g5g3 :
    ¬ ∃ E : Fin 5 → Fin 5 → ℚ,
      ∀ p q, KThetaF21 p q = E (tvG5G3F21 p) (tvG5G3F21 q) := by
  rintro ⟨E, hE⟩
  have h1 := hE 0 2
  have h2 := hE 0 7
  rw [KTheta_entry_0_2, tvG5G3F21_0, tvG5G3F21_2] at h1
  rw [KTheta_entry_0_7, tvG5G3F21_0, tvG5G3F21_7] at h2
  linarith

/-- **Θ-escape, `g₃g₅⁻¹` factorization fails**
(orbits `(0,0)` vs `(0,6)`). -/
theorem theta_not_factor_g3g5inv :
    ¬ ∃ E : Fin 5 → Fin 5 → ℚ,
      ∀ p q, KThetaF21 p q = E (tvG3G5invF21 p) (tvG3G5invF21 q) := by
  rintro ⟨E, hE⟩
  have h1 := hE 0 0
  have h2 := hE 0 6
  rw [KTheta_entry_0_0, tvG3G5invF21_0] at h1
  rw [KTheta_entry_0_6, tvG3G5invF21_0, tvG3G5invF21_6] at h2
  linarith

/-- **Θ-escape, `g₃⁻¹g₅` factorization fails**
(orbits `(0,0)` vs `(0,6)`). -/
theorem theta_not_factor_g3invg5 :
    ¬ ∃ E : Fin 5 → Fin 5 → ℚ,
      ∀ p q, KThetaF21 p q = E (tvG3invG5F21 p) (tvG3invG5F21 q) := by
  rintro ⟨E, hE⟩
  have h1 := hE 0 0
  have h2 := hE 0 6
  rw [KTheta_entry_0_0, tvG3invG5F21_0] at h1
  rw [KTheta_entry_0_6, tvG3invG5F21_0, tvG3invG5F21_6] at h2
  linarith

/-- **Θ-escape, `g₃` pullback is not a κ₄ multiple**:
entry `(0,0)` forces `λ = 5/12`, entry `(0,1)`
contradicts it. -/
theorem theta_not_pullback_g3 :
    ¬ ∃ lam : ℚ, ∀ p q,
      KThetaF21 p q = lam * K4F21 (tvG3F21 p) (tvG3F21 q) := by
  rintro ⟨lam, h⟩
  have h00 := h 0 0
  have h01 := h 0 1
  rw [KTheta_entry_0_0, tvG3F21_0, K4F21_0_0] at h00
  rw [KTheta_entry_0_1, tvG3F21_0, tvG3F21_1, K4F21_0_0] at h01
  have hlam : lam = 5 / 12 := by linarith [h00]
  rw [hlam] at h01
  norm_num at h01

/-- **Θ-escape, `g₅` pullback is not a κ₄ multiple**
(entries `(0,0)`, `(0,5)`). -/
theorem theta_not_pullback_g5 :
    ¬ ∃ lam : ℚ, ∀ p q,
      KThetaF21 p q = lam * K4F21 (tvG5F21 p) (tvG5F21 q) := by
  rintro ⟨lam, h⟩
  have h00 := h 0 0
  have h05 := h 0 5
  rw [KTheta_entry_0_0, tvG5F21_0, K4F21_0_0] at h00
  rw [KTheta_entry_0_5, tvG5F21_0, tvG5F21_5, K4F21_0_0] at h05
  have hlam : lam = 5 / 12 := by linarith [h00]
  rw [hlam] at h05
  norm_num at h05

/-- **Θ-escape, `g₃g₅` pullback is not a κ₄ multiple**
(entries `(0,0)`, `(0,7)`; the second entry's κ₄ value
is `-1/432`). -/
theorem theta_not_pullback_g3g5 :
    ¬ ∃ lam : ℚ, ∀ p q,
      KThetaF21 p q = lam * K4F21 (tvG3G5F21 p) (tvG3G5F21 q) := by
  rintro ⟨lam, h⟩
  have h00 := h 0 0
  have h07 := h 0 7
  rw [KTheta_entry_0_0, tvG3G5F21_0, K4F21_0_0] at h00
  rw [KTheta_entry_0_7, tvG3G5F21_0, tvG3G5F21_7, K4F21_0_2] at h07
  have hlam : lam = 5 / 12 := by linarith [h00]
  rw [hlam] at h07
  norm_num at h07

/-- **Θ-escape, `g₅g₃` pullback is not a κ₄ multiple**
(entries `(0,0)`, `(0,7)`). -/
theorem theta_not_pullback_g5g3 :
    ¬ ∃ lam : ℚ, ∀ p q,
      KThetaF21 p q = lam * K4F21 (tvG5G3F21 p) (tvG5G3F21 q) := by
  rintro ⟨lam, h⟩
  have h00 := h 0 0
  have h07 := h 0 7
  rw [KTheta_entry_0_0, tvG5G3F21_0, K4F21_0_0] at h00
  rw [KTheta_entry_0_7, tvG5G3F21_0, tvG5G3F21_7, K4F21_0_2] at h07
  have hlam : lam = 5 / 12 := by linarith [h00]
  rw [hlam] at h07
  norm_num at h07

/-- **Θ-escape, `g₃g₅⁻¹` pullback is not a κ₄
multiple** (entries `(0,0)`, `(0,6)`). -/
theorem theta_not_pullback_g3g5inv :
    ¬ ∃ lam : ℚ, ∀ p q,
      KThetaF21 p q = lam * K4F21 (tvG3G5invF21 p) (tvG3G5invF21 q) := by
  rintro ⟨lam, h⟩
  have h00 := h 0 0
  have h06 := h 0 6
  rw [KTheta_entry_0_0, tvG3G5invF21_0, K4F21_0_0] at h00
  rw [KTheta_entry_0_6, tvG3G5invF21_0, tvG3G5invF21_6, K4F21_0_0] at h06
  have hlam : lam = 5 / 12 := by linarith [h00]
  rw [hlam] at h06
  norm_num at h06

/-- **Θ-escape, `g₃⁻¹g₅` pullback is not a κ₄
multiple** (entries `(0,0)`, `(0,6)`). -/
theorem theta_not_pullback_g3invg5 :
    ¬ ∃ lam : ℚ, ∀ p q,
      KThetaF21 p q = lam * K4F21 (tvG3invG5F21 p) (tvG3invG5F21 q) := by
  rintro ⟨lam, h⟩
  have h00 := h 0 0
  have h06 := h 0 6
  rw [KTheta_entry_0_0, tvG3invG5F21_0, K4F21_0_0] at h00
  rw [KTheta_entry_0_6, tvG3invG5F21_0, tvG3invG5F21_6, K4F21_0_0] at h06
  have hlam : lam = 5 / 12 := by linarith [h00]
  rw [hlam] at h06
  norm_num at h06

/-- **Θ-ESCAPE (Θ-1), certified (deliverable 4).**
The Θ orbit kernel at (F21, ρ₃) is nonzero, factors
through NONE of the six single class variables, and is
a κ₄-pullback multiple under NONE of them — in
particular there is no positive pullback multiple
under any reading. This is the GD-ii content at this
seat: GD-strong's proportionality fails for Θ. -/
theorem theta_escape_F21 :
    KThetaF21 0 0 ≠ 0
    ∧ (¬ ∃ E : Fin 5 → Fin 5 → ℚ,
        ∀ p q, KThetaF21 p q = E (tvG3F21 p) (tvG3F21 q))
    ∧ (¬ ∃ E : Fin 5 → Fin 5 → ℚ,
        ∀ p q, KThetaF21 p q = E (tvG5F21 p) (tvG5F21 q))
    ∧ (¬ ∃ E : Fin 5 → Fin 5 → ℚ,
        ∀ p q, KThetaF21 p q = E (tvG3G5F21 p) (tvG3G5F21 q))
    ∧ (¬ ∃ E : Fin 5 → Fin 5 → ℚ,
        ∀ p q, KThetaF21 p q = E (tvG5G3F21 p) (tvG5G3F21 q))
    ∧ (¬ ∃ E : Fin 5 → Fin 5 → ℚ,
        ∀ p q, KThetaF21 p q = E (tvG3G5invF21 p) (tvG3G5invF21 q))
    ∧ (¬ ∃ E : Fin 5 → Fin 5 → ℚ,
        ∀ p q, KThetaF21 p q = E (tvG3invG5F21 p) (tvG3invG5F21 q))
    ∧ (¬ ∃ lam : ℚ, ∀ p q,
        KThetaF21 p q = lam * K4F21 (tvG3F21 p) (tvG3F21 q))
    ∧ (¬ ∃ lam : ℚ, ∀ p q,
        KThetaF21 p q = lam * K4F21 (tvG5F21 p) (tvG5F21 q))
    ∧ (¬ ∃ lam : ℚ, ∀ p q,
        KThetaF21 p q = lam * K4F21 (tvG3G5F21 p) (tvG3G5F21 q))
    ∧ (¬ ∃ lam : ℚ, ∀ p q,
        KThetaF21 p q = lam * K4F21 (tvG5G3F21 p) (tvG5G3F21 q))
    ∧ (¬ ∃ lam : ℚ, ∀ p q,
        KThetaF21 p q = lam * K4F21 (tvG3G5invF21 p) (tvG3G5invF21 q))
    ∧ (¬ ∃ lam : ℚ, ∀ p q,
        KThetaF21 p q = lam * K4F21 (tvG3invG5F21 p) (tvG3invG5F21 q)) :=
  ⟨KTheta_ne_zero, theta_not_factor_g3, theta_not_factor_g5,
    theta_not_factor_g3g5, theta_not_factor_g5g3,
    theta_not_factor_g3g5inv, theta_not_factor_g3invg5,
    theta_not_pullback_g3, theta_not_pullback_g5,
    theta_not_pullback_g3g5, theta_not_pullback_g5g3,
    theta_not_pullback_g3g5inv, theta_not_pullback_g3invg5⟩

/-! ## Deliverable (2), Θ part: (Θ-2) kernel restriction -/

/-- The aggregated Θ kernel sum along a class
variable: `D tv p a = ∑_{q : tv q = a} KΘ p q · fib q`. -/
def DThetaF21 (tv : Fin 41 → Fin 5) (p : Fin 41) (a : Fin 5) : ℚ :=
  ∑ q, (if tv q = a then KThetaF21 p q * fibThetaF21 q else 0)

theorem DThetaF21_eq_blockSum (tv : Fin 41 → Fin 5) (p : Fin 41)
    (a : Fin 5) :
    DThetaF21 tv p a
      = ∑ q ∈ blockOfF21 p,
          (if tv q = a then KThetaF21 p q * fibThetaF21 q else 0) := by
  unfold DThetaF21
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro q _ hq
  by_cases htv : tv q = a
  · rw [if_pos htv, KTheta_eq_zero_of_not_mem hq, zero_mul]
  · rw [if_neg htv]

/-- Aggregated Θ sums vanish off the support blocks
(generic in the class variable). -/
theorem DTheta_zero_of_not_mem (tv : Fin 41 → Fin 5) {p : Fin 41}
    (hA : p ∉ blockAF21) (hB : p ∉ blockBF21) (hC : p ∉ blockCF21)
    (a : Fin 5) :
    DThetaF21 tv p a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have h : blockOfF21 p = ∅ := by
    unfold blockOfF21
    rw [if_neg hA, if_neg hB, if_neg hC]
  rw [h, Finset.sum_empty]



/-- Aggregated Θ sums along `tvG3F21` at orbit 0
(block A row): exact rational computation. -/
theorem DTheta_g3_zero_p0 (a : Fin 5) :
    DThetaF21 tvG3F21 0 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (0 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG3F21` at orbit 1
(block A row): exact rational computation. -/
theorem DTheta_g3_zero_p1 (a : Fin 5) :
    DThetaF21 tvG3F21 1 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (1 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG3F21` at orbit 2
(block A row): exact rational computation. -/
theorem DTheta_g3_zero_p2 (a : Fin 5) :
    DThetaF21 tvG3F21 2 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (2 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG3F21` at orbit 5
(block A row): exact rational computation. -/
theorem DTheta_g3_zero_p5 (a : Fin 5) :
    DThetaF21 tvG3F21 5 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (5 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG3F21` at orbit 6
(block A row): exact rational computation. -/
theorem DTheta_g3_zero_p6 (a : Fin 5) :
    DThetaF21 tvG3F21 6 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (6 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG3F21` at orbit 7
(block A row): exact rational computation. -/
theorem DTheta_g3_zero_p7 (a : Fin 5) :
    DThetaF21 tvG3F21 7 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (7 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG3F21` at orbit 8
(block A row): exact rational computation. -/
theorem DTheta_g3_zero_p8 (a : Fin 5) :
    DThetaF21 tvG3F21 8 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (8 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG3F21` at orbit 9
(block A row): exact rational computation. -/
theorem DTheta_g3_zero_p9 (a : Fin 5) :
    DThetaF21 tvG3F21 9 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (9 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG3F21` at orbit 10
(block A row): exact rational computation. -/
theorem DTheta_g3_zero_p10 (a : Fin 5) :
    DThetaF21 tvG3F21 10 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (10 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG3F21` at orbit 11
(block A row): exact rational computation. -/
theorem DTheta_g3_zero_p11 (a : Fin 5) :
    DThetaF21 tvG3F21 11 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (11 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG3F21` at orbit 14
(block A row): exact rational computation. -/
theorem DTheta_g3_zero_p14 (a : Fin 5) :
    DThetaF21 tvG3F21 14 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (14 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG3F21` at orbit 15
(block A row): exact rational computation. -/
theorem DTheta_g3_zero_p15 (a : Fin 5) :
    DThetaF21 tvG3F21 15 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (15 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG3F21` at orbit 16
(block A row): exact rational computation. -/
theorem DTheta_g3_zero_p16 (a : Fin 5) :
    DThetaF21 tvG3F21 16 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (16 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG3F21` at orbit 17
(block A row): exact rational computation. -/
theorem DTheta_g3_zero_p17 (a : Fin 5) :
    DThetaF21 tvG3F21 17 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (17 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG3F21` at orbit 18
(block A row): exact rational computation. -/
theorem DTheta_g3_zero_p18 (a : Fin 5) :
    DThetaF21 tvG3F21 18 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (18 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG3F21` at orbit 19
(block A row): exact rational computation. -/
theorem DTheta_g3_zero_p19 (a : Fin 5) :
    DThetaF21 tvG3F21 19 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (19 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG3F21` at orbit 20
(block A row): exact rational computation. -/
theorem DTheta_g3_zero_p20 (a : Fin 5) :
    DThetaF21 tvG3F21 20 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (20 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG3F21` at orbit 29
(block B row): exact rational computation. -/
theorem DTheta_g3_zero_p29 (a : Fin 5) :
    DThetaF21 tvG3F21 29 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (29 : Fin 41) = blockBF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockBF21,
      Finset.sum_insert (by decide : (29:Fin 41) ∉ ({30, 31} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (30:Fin 41) ∉ ({31} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG3F21` at orbit 30
(block B row): exact rational computation. -/
theorem DTheta_g3_zero_p30 (a : Fin 5) :
    DThetaF21 tvG3F21 30 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (30 : Fin 41) = blockBF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockBF21,
      Finset.sum_insert (by decide : (29:Fin 41) ∉ ({30, 31} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (30:Fin 41) ∉ ({31} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG3F21` at orbit 31
(block B row): exact rational computation. -/
theorem DTheta_g3_zero_p31 (a : Fin 5) :
    DThetaF21 tvG3F21 31 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (31 : Fin 41) = blockBF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockBF21,
      Finset.sum_insert (by decide : (29:Fin 41) ∉ ({30, 31} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (30:Fin 41) ∉ ({31} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG3F21` at orbit 35
(block C row): exact rational computation. -/
theorem DTheta_g3_zero_p35 (a : Fin 5) :
    DThetaF21 tvG3F21 35 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (35 : Fin 41) = blockCF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockCF21,
      Finset.sum_insert (by decide : (35:Fin 41) ∉ ({36, 37} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (36:Fin 41) ∉ ({37} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG3F21` at orbit 36
(block C row): exact rational computation. -/
theorem DTheta_g3_zero_p36 (a : Fin 5) :
    DThetaF21 tvG3F21 36 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (36 : Fin 41) = blockCF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockCF21,
      Finset.sum_insert (by decide : (35:Fin 41) ∉ ({36, 37} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (36:Fin 41) ∉ ({37} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG3F21` at orbit 37
(block C row): exact rational computation. -/
theorem DTheta_g3_zero_p37 (a : Fin 5) :
    DThetaF21 tvG3F21 37 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (37 : Fin 41) = blockCF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockCF21,
      Finset.sum_insert (by decide : (35:Fin 41) ∉ ({36, 37} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (36:Fin 41) ∉ ({37} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG3F21`, block A rows
(assembled from the per-orbit computations). -/
theorem DTheta_tvG3_zero_A (i : Fin 17) (a : Fin 5) :
    DThetaF21 tvG3F21 (orbAF21 i) a = 0 := by
  fin_cases i
  · show DThetaF21 tvG3F21 0 a = 0
    exact DTheta_g3_zero_p0 a
  · show DThetaF21 tvG3F21 1 a = 0
    exact DTheta_g3_zero_p1 a
  · show DThetaF21 tvG3F21 2 a = 0
    exact DTheta_g3_zero_p2 a
  · show DThetaF21 tvG3F21 5 a = 0
    exact DTheta_g3_zero_p5 a
  · show DThetaF21 tvG3F21 6 a = 0
    exact DTheta_g3_zero_p6 a
  · show DThetaF21 tvG3F21 7 a = 0
    exact DTheta_g3_zero_p7 a
  · show DThetaF21 tvG3F21 8 a = 0
    exact DTheta_g3_zero_p8 a
  · show DThetaF21 tvG3F21 9 a = 0
    exact DTheta_g3_zero_p9 a
  · show DThetaF21 tvG3F21 10 a = 0
    exact DTheta_g3_zero_p10 a
  · show DThetaF21 tvG3F21 11 a = 0
    exact DTheta_g3_zero_p11 a
  · show DThetaF21 tvG3F21 14 a = 0
    exact DTheta_g3_zero_p14 a
  · show DThetaF21 tvG3F21 15 a = 0
    exact DTheta_g3_zero_p15 a
  · show DThetaF21 tvG3F21 16 a = 0
    exact DTheta_g3_zero_p16 a
  · show DThetaF21 tvG3F21 17 a = 0
    exact DTheta_g3_zero_p17 a
  · show DThetaF21 tvG3F21 18 a = 0
    exact DTheta_g3_zero_p18 a
  · show DThetaF21 tvG3F21 19 a = 0
    exact DTheta_g3_zero_p19 a
  · show DThetaF21 tvG3F21 20 a = 0
    exact DTheta_g3_zero_p20 a

/-- Aggregated Θ sums along `tvG3F21`, block B rows
(assembled from the per-orbit computations). -/
theorem DTheta_tvG3_zero_B (i : Fin 3) (a : Fin 5) :
    DThetaF21 tvG3F21 (orbBF21 i) a = 0 := by
  fin_cases i
  · show DThetaF21 tvG3F21 29 a = 0
    exact DTheta_g3_zero_p29 a
  · show DThetaF21 tvG3F21 30 a = 0
    exact DTheta_g3_zero_p30 a
  · show DThetaF21 tvG3F21 31 a = 0
    exact DTheta_g3_zero_p31 a

/-- Aggregated Θ sums along `tvG3F21`, block C rows
(assembled from the per-orbit computations). -/
theorem DTheta_tvG3_zero_C (i : Fin 3) (a : Fin 5) :
    DThetaF21 tvG3F21 (orbCF21 i) a = 0 := by
  fin_cases i
  · show DThetaF21 tvG3F21 35 a = 0
    exact DTheta_g3_zero_p35 a
  · show DThetaF21 tvG3F21 36 a = 0
    exact DTheta_g3_zero_p36 a
  · show DThetaF21 tvG3F21 37 a = 0
    exact DTheta_g3_zero_p37 a

/-- **Aggregated Θ sums vanish along `tvG3F21`**:
for every orbit `p` and class `a`,
`∑_{q : tvG3F21 q = a} KΘ p q · fib q = 0`. -/
theorem DTheta_tvG3_zero (p : Fin 41) (a : Fin 5) :
    DThetaF21 tvG3F21 p a = 0 := by
  by_cases hA : p ∈ blockAF21
  · obtain ⟨i, hi⟩ : ∃ i : Fin 17, orbAF21 i = p :=
      ⟨posAF21 p, orbA_posA hA⟩
    rw [← hi]
    exact DTheta_tvG3_zero_A i a
  · by_cases hB : p ∈ blockBF21
    · obtain ⟨i, hi⟩ : ∃ i : Fin 3, orbBF21 i = p :=
        ⟨posBF21 p, orbB_posB hB⟩
      rw [← hi]
      exact DTheta_tvG3_zero_B i a
    · by_cases hC : p ∈ blockCF21
      · obtain ⟨i, hi⟩ : ∃ i : Fin 3, orbCF21 i = p :=
          ⟨posCF21 p, orbC_posC hC⟩
        rw [← hi]
        exact DTheta_tvG3_zero_C i a
      · exact DTheta_zero_of_not_mem tvG3F21 hA hB hC a


/-- Aggregated Θ sums along `tvG5F21` at orbit 0
(block A row): exact rational computation. -/
theorem DTheta_g5_zero_p0 (a : Fin 5) :
    DThetaF21 tvG5F21 0 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (0 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG5F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG5F21` at orbit 1
(block A row): exact rational computation. -/
theorem DTheta_g5_zero_p1 (a : Fin 5) :
    DThetaF21 tvG5F21 1 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (1 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG5F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG5F21` at orbit 2
(block A row): exact rational computation. -/
theorem DTheta_g5_zero_p2 (a : Fin 5) :
    DThetaF21 tvG5F21 2 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (2 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG5F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG5F21` at orbit 5
(block A row): exact rational computation. -/
theorem DTheta_g5_zero_p5 (a : Fin 5) :
    DThetaF21 tvG5F21 5 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (5 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG5F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG5F21` at orbit 6
(block A row): exact rational computation. -/
theorem DTheta_g5_zero_p6 (a : Fin 5) :
    DThetaF21 tvG5F21 6 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (6 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG5F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG5F21` at orbit 7
(block A row): exact rational computation. -/
theorem DTheta_g5_zero_p7 (a : Fin 5) :
    DThetaF21 tvG5F21 7 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (7 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG5F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG5F21` at orbit 8
(block A row): exact rational computation. -/
theorem DTheta_g5_zero_p8 (a : Fin 5) :
    DThetaF21 tvG5F21 8 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (8 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG5F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG5F21` at orbit 9
(block A row): exact rational computation. -/
theorem DTheta_g5_zero_p9 (a : Fin 5) :
    DThetaF21 tvG5F21 9 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (9 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG5F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG5F21` at orbit 10
(block A row): exact rational computation. -/
theorem DTheta_g5_zero_p10 (a : Fin 5) :
    DThetaF21 tvG5F21 10 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (10 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG5F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG5F21` at orbit 11
(block A row): exact rational computation. -/
theorem DTheta_g5_zero_p11 (a : Fin 5) :
    DThetaF21 tvG5F21 11 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (11 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG5F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG5F21` at orbit 14
(block A row): exact rational computation. -/
theorem DTheta_g5_zero_p14 (a : Fin 5) :
    DThetaF21 tvG5F21 14 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (14 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG5F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG5F21` at orbit 15
(block A row): exact rational computation. -/
theorem DTheta_g5_zero_p15 (a : Fin 5) :
    DThetaF21 tvG5F21 15 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (15 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG5F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG5F21` at orbit 16
(block A row): exact rational computation. -/
theorem DTheta_g5_zero_p16 (a : Fin 5) :
    DThetaF21 tvG5F21 16 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (16 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG5F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG5F21` at orbit 17
(block A row): exact rational computation. -/
theorem DTheta_g5_zero_p17 (a : Fin 5) :
    DThetaF21 tvG5F21 17 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (17 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG5F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG5F21` at orbit 18
(block A row): exact rational computation. -/
theorem DTheta_g5_zero_p18 (a : Fin 5) :
    DThetaF21 tvG5F21 18 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (18 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG5F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG5F21` at orbit 19
(block A row): exact rational computation. -/
theorem DTheta_g5_zero_p19 (a : Fin 5) :
    DThetaF21 tvG5F21 19 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (19 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG5F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG5F21` at orbit 20
(block A row): exact rational computation. -/
theorem DTheta_g5_zero_p20 (a : Fin 5) :
    DThetaF21 tvG5F21 20 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (20 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG5F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG5F21` at orbit 29
(block B row): exact rational computation. -/
theorem DTheta_g5_zero_p29 (a : Fin 5) :
    DThetaF21 tvG5F21 29 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (29 : Fin 41) = blockBF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockBF21,
      Finset.sum_insert (by decide : (29:Fin 41) ∉ ({30, 31} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (30:Fin 41) ∉ ({31} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG5F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG5F21` at orbit 30
(block B row): exact rational computation. -/
theorem DTheta_g5_zero_p30 (a : Fin 5) :
    DThetaF21 tvG5F21 30 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (30 : Fin 41) = blockBF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockBF21,
      Finset.sum_insert (by decide : (29:Fin 41) ∉ ({30, 31} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (30:Fin 41) ∉ ({31} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG5F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG5F21` at orbit 31
(block B row): exact rational computation. -/
theorem DTheta_g5_zero_p31 (a : Fin 5) :
    DThetaF21 tvG5F21 31 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (31 : Fin 41) = blockBF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockBF21,
      Finset.sum_insert (by decide : (29:Fin 41) ∉ ({30, 31} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (30:Fin 41) ∉ ({31} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG5F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG5F21` at orbit 35
(block C row): exact rational computation. -/
theorem DTheta_g5_zero_p35 (a : Fin 5) :
    DThetaF21 tvG5F21 35 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (35 : Fin 41) = blockCF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockCF21,
      Finset.sum_insert (by decide : (35:Fin 41) ∉ ({36, 37} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (36:Fin 41) ∉ ({37} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG5F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG5F21` at orbit 36
(block C row): exact rational computation. -/
theorem DTheta_g5_zero_p36 (a : Fin 5) :
    DThetaF21 tvG5F21 36 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (36 : Fin 41) = blockCF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockCF21,
      Finset.sum_insert (by decide : (35:Fin 41) ∉ ({36, 37} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (36:Fin 41) ∉ ({37} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG5F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG5F21` at orbit 37
(block C row): exact rational computation. -/
theorem DTheta_g5_zero_p37 (a : Fin 5) :
    DThetaF21 tvG5F21 37 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (37 : Fin 41) = blockCF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockCF21,
      Finset.sum_insert (by decide : (35:Fin 41) ∉ ({36, 37} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (36:Fin 41) ∉ ({37} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG5F21, orbRepF21, clsF21]

/-- Aggregated Θ sums along `tvG5F21`, block A rows
(assembled from the per-orbit computations). -/
theorem DTheta_tvG5_zero_A (i : Fin 17) (a : Fin 5) :
    DThetaF21 tvG5F21 (orbAF21 i) a = 0 := by
  fin_cases i
  · show DThetaF21 tvG5F21 0 a = 0
    exact DTheta_g5_zero_p0 a
  · show DThetaF21 tvG5F21 1 a = 0
    exact DTheta_g5_zero_p1 a
  · show DThetaF21 tvG5F21 2 a = 0
    exact DTheta_g5_zero_p2 a
  · show DThetaF21 tvG5F21 5 a = 0
    exact DTheta_g5_zero_p5 a
  · show DThetaF21 tvG5F21 6 a = 0
    exact DTheta_g5_zero_p6 a
  · show DThetaF21 tvG5F21 7 a = 0
    exact DTheta_g5_zero_p7 a
  · show DThetaF21 tvG5F21 8 a = 0
    exact DTheta_g5_zero_p8 a
  · show DThetaF21 tvG5F21 9 a = 0
    exact DTheta_g5_zero_p9 a
  · show DThetaF21 tvG5F21 10 a = 0
    exact DTheta_g5_zero_p10 a
  · show DThetaF21 tvG5F21 11 a = 0
    exact DTheta_g5_zero_p11 a
  · show DThetaF21 tvG5F21 14 a = 0
    exact DTheta_g5_zero_p14 a
  · show DThetaF21 tvG5F21 15 a = 0
    exact DTheta_g5_zero_p15 a
  · show DThetaF21 tvG5F21 16 a = 0
    exact DTheta_g5_zero_p16 a
  · show DThetaF21 tvG5F21 17 a = 0
    exact DTheta_g5_zero_p17 a
  · show DThetaF21 tvG5F21 18 a = 0
    exact DTheta_g5_zero_p18 a
  · show DThetaF21 tvG5F21 19 a = 0
    exact DTheta_g5_zero_p19 a
  · show DThetaF21 tvG5F21 20 a = 0
    exact DTheta_g5_zero_p20 a

/-- Aggregated Θ sums along `tvG5F21`, block B rows
(assembled from the per-orbit computations). -/
theorem DTheta_tvG5_zero_B (i : Fin 3) (a : Fin 5) :
    DThetaF21 tvG5F21 (orbBF21 i) a = 0 := by
  fin_cases i
  · show DThetaF21 tvG5F21 29 a = 0
    exact DTheta_g5_zero_p29 a
  · show DThetaF21 tvG5F21 30 a = 0
    exact DTheta_g5_zero_p30 a
  · show DThetaF21 tvG5F21 31 a = 0
    exact DTheta_g5_zero_p31 a

/-- Aggregated Θ sums along `tvG5F21`, block C rows
(assembled from the per-orbit computations). -/
theorem DTheta_tvG5_zero_C (i : Fin 3) (a : Fin 5) :
    DThetaF21 tvG5F21 (orbCF21 i) a = 0 := by
  fin_cases i
  · show DThetaF21 tvG5F21 35 a = 0
    exact DTheta_g5_zero_p35 a
  · show DThetaF21 tvG5F21 36 a = 0
    exact DTheta_g5_zero_p36 a
  · show DThetaF21 tvG5F21 37 a = 0
    exact DTheta_g5_zero_p37 a

/-- **Aggregated Θ sums vanish along `tvG5F21`**:
for every orbit `p` and class `a`,
`∑_{q : tvG5F21 q = a} KΘ p q · fib q = 0`. -/
theorem DTheta_tvG5_zero (p : Fin 41) (a : Fin 5) :
    DThetaF21 tvG5F21 p a = 0 := by
  by_cases hA : p ∈ blockAF21
  · obtain ⟨i, hi⟩ : ∃ i : Fin 17, orbAF21 i = p :=
      ⟨posAF21 p, orbA_posA hA⟩
    rw [← hi]
    exact DTheta_tvG5_zero_A i a
  · by_cases hB : p ∈ blockBF21
    · obtain ⟨i, hi⟩ : ∃ i : Fin 3, orbBF21 i = p :=
        ⟨posBF21 p, orbB_posB hB⟩
      rw [← hi]
      exact DTheta_tvG5_zero_B i a
    · by_cases hC : p ∈ blockCF21
      · obtain ⟨i, hi⟩ : ∃ i : Fin 3, orbCF21 i = p :=
          ⟨posCF21 p, orbC_posC hC⟩
        rw [← hi]
        exact DTheta_tvG5_zero_C i a
      · exact DTheta_zero_of_not_mem tvG5F21 hA hB hC a


/-- Aggregated Θ sums along `tvG3invG5F21` at orbit 0
(block A row): exact rational computation. -/
theorem DTheta_g3invg5_zero_p0 (a : Fin 5) :
    DThetaF21 tvG3invG5F21 0 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (0 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3invG5F21, orbRepF21, clsF21, mulF21, invF21]

/-- Aggregated Θ sums along `tvG3invG5F21` at orbit 1
(block A row): exact rational computation. -/
theorem DTheta_g3invg5_zero_p1 (a : Fin 5) :
    DThetaF21 tvG3invG5F21 1 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (1 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3invG5F21, orbRepF21, clsF21, mulF21, invF21]

/-- Aggregated Θ sums along `tvG3invG5F21` at orbit 2
(block A row): exact rational computation. -/
theorem DTheta_g3invg5_zero_p2 (a : Fin 5) :
    DThetaF21 tvG3invG5F21 2 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (2 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3invG5F21, orbRepF21, clsF21, mulF21, invF21]

/-- Aggregated Θ sums along `tvG3invG5F21` at orbit 5
(block A row): exact rational computation. -/
theorem DTheta_g3invg5_zero_p5 (a : Fin 5) :
    DThetaF21 tvG3invG5F21 5 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (5 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3invG5F21, orbRepF21, clsF21, mulF21, invF21]

/-- Aggregated Θ sums along `tvG3invG5F21` at orbit 6
(block A row): exact rational computation. -/
theorem DTheta_g3invg5_zero_p6 (a : Fin 5) :
    DThetaF21 tvG3invG5F21 6 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (6 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3invG5F21, orbRepF21, clsF21, mulF21, invF21]

/-- Aggregated Θ sums along `tvG3invG5F21` at orbit 7
(block A row): exact rational computation. -/
theorem DTheta_g3invg5_zero_p7 (a : Fin 5) :
    DThetaF21 tvG3invG5F21 7 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (7 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3invG5F21, orbRepF21, clsF21, mulF21, invF21]

/-- Aggregated Θ sums along `tvG3invG5F21` at orbit 8
(block A row): exact rational computation. -/
theorem DTheta_g3invg5_zero_p8 (a : Fin 5) :
    DThetaF21 tvG3invG5F21 8 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (8 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3invG5F21, orbRepF21, clsF21, mulF21, invF21]

/-- Aggregated Θ sums along `tvG3invG5F21` at orbit 9
(block A row): exact rational computation. -/
theorem DTheta_g3invg5_zero_p9 (a : Fin 5) :
    DThetaF21 tvG3invG5F21 9 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (9 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3invG5F21, orbRepF21, clsF21, mulF21, invF21]

/-- Aggregated Θ sums along `tvG3invG5F21` at orbit 10
(block A row): exact rational computation. -/
theorem DTheta_g3invg5_zero_p10 (a : Fin 5) :
    DThetaF21 tvG3invG5F21 10 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (10 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3invG5F21, orbRepF21, clsF21, mulF21, invF21]

/-- Aggregated Θ sums along `tvG3invG5F21` at orbit 11
(block A row): exact rational computation. -/
theorem DTheta_g3invg5_zero_p11 (a : Fin 5) :
    DThetaF21 tvG3invG5F21 11 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (11 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3invG5F21, orbRepF21, clsF21, mulF21, invF21]

/-- Aggregated Θ sums along `tvG3invG5F21` at orbit 14
(block A row): exact rational computation. -/
theorem DTheta_g3invg5_zero_p14 (a : Fin 5) :
    DThetaF21 tvG3invG5F21 14 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (14 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3invG5F21, orbRepF21, clsF21, mulF21, invF21]

/-- Aggregated Θ sums along `tvG3invG5F21` at orbit 15
(block A row): exact rational computation. -/
theorem DTheta_g3invg5_zero_p15 (a : Fin 5) :
    DThetaF21 tvG3invG5F21 15 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (15 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3invG5F21, orbRepF21, clsF21, mulF21, invF21]

/-- Aggregated Θ sums along `tvG3invG5F21` at orbit 16
(block A row): exact rational computation. -/
theorem DTheta_g3invg5_zero_p16 (a : Fin 5) :
    DThetaF21 tvG3invG5F21 16 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (16 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3invG5F21, orbRepF21, clsF21, mulF21, invF21]

/-- Aggregated Θ sums along `tvG3invG5F21` at orbit 17
(block A row): exact rational computation. -/
theorem DTheta_g3invg5_zero_p17 (a : Fin 5) :
    DThetaF21 tvG3invG5F21 17 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (17 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3invG5F21, orbRepF21, clsF21, mulF21, invF21]

/-- Aggregated Θ sums along `tvG3invG5F21` at orbit 18
(block A row): exact rational computation. -/
theorem DTheta_g3invg5_zero_p18 (a : Fin 5) :
    DThetaF21 tvG3invG5F21 18 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (18 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3invG5F21, orbRepF21, clsF21, mulF21, invF21]

/-- Aggregated Θ sums along `tvG3invG5F21` at orbit 19
(block A row): exact rational computation. -/
theorem DTheta_g3invg5_zero_p19 (a : Fin 5) :
    DThetaF21 tvG3invG5F21 19 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (19 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3invG5F21, orbRepF21, clsF21, mulF21, invF21]

/-- Aggregated Θ sums along `tvG3invG5F21` at orbit 20
(block A row): exact rational computation. -/
theorem DTheta_g3invg5_zero_p20 (a : Fin 5) :
    DThetaF21 tvG3invG5F21 20 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (20 : Fin 41) = blockAF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockAF21,
      Finset.sum_insert (by decide : (0:Fin 41) ∉ ({1, 2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (1:Fin 41) ∉ ({2, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (2:Fin 41) ∉ ({5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (5:Fin 41) ∉ ({6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (6:Fin 41) ∉ ({7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (7:Fin 41) ∉ ({8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (8:Fin 41) ∉ ({9, 10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (9:Fin 41) ∉ ({10, 11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (10:Fin 41) ∉ ({11, 14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (11:Fin 41) ∉ ({14, 15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (14:Fin 41) ∉ ({15, 16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (15:Fin 41) ∉ ({16, 17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (16:Fin 41) ∉ ({17, 18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (17:Fin 41) ∉ ({18, 19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (18:Fin 41) ∉ ({19, 20} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (19:Fin 41) ∉ ({20} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3invG5F21, orbRepF21, clsF21, mulF21, invF21]

/-- Aggregated Θ sums along `tvG3invG5F21` at orbit 29
(block B row): exact rational computation. -/
theorem DTheta_g3invg5_zero_p29 (a : Fin 5) :
    DThetaF21 tvG3invG5F21 29 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (29 : Fin 41) = blockBF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockBF21,
      Finset.sum_insert (by decide : (29:Fin 41) ∉ ({30, 31} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (30:Fin 41) ∉ ({31} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3invG5F21, orbRepF21, clsF21, mulF21, invF21]

/-- Aggregated Θ sums along `tvG3invG5F21` at orbit 30
(block B row): exact rational computation. -/
theorem DTheta_g3invg5_zero_p30 (a : Fin 5) :
    DThetaF21 tvG3invG5F21 30 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (30 : Fin 41) = blockBF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockBF21,
      Finset.sum_insert (by decide : (29:Fin 41) ∉ ({30, 31} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (30:Fin 41) ∉ ({31} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3invG5F21, orbRepF21, clsF21, mulF21, invF21]

/-- Aggregated Θ sums along `tvG3invG5F21` at orbit 31
(block B row): exact rational computation. -/
theorem DTheta_g3invg5_zero_p31 (a : Fin 5) :
    DThetaF21 tvG3invG5F21 31 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (31 : Fin 41) = blockBF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockBF21,
      Finset.sum_insert (by decide : (29:Fin 41) ∉ ({30, 31} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (30:Fin 41) ∉ ({31} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3invG5F21, orbRepF21, clsF21, mulF21, invF21]

/-- Aggregated Θ sums along `tvG3invG5F21` at orbit 35
(block C row): exact rational computation. -/
theorem DTheta_g3invg5_zero_p35 (a : Fin 5) :
    DThetaF21 tvG3invG5F21 35 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (35 : Fin 41) = blockCF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockCF21,
      Finset.sum_insert (by decide : (35:Fin 41) ∉ ({36, 37} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (36:Fin 41) ∉ ({37} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3invG5F21, orbRepF21, clsF21, mulF21, invF21]

/-- Aggregated Θ sums along `tvG3invG5F21` at orbit 36
(block C row): exact rational computation. -/
theorem DTheta_g3invg5_zero_p36 (a : Fin 5) :
    DThetaF21 tvG3invG5F21 36 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (36 : Fin 41) = blockCF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockCF21,
      Finset.sum_insert (by decide : (35:Fin 41) ∉ ({36, 37} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (36:Fin 41) ∉ ({37} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3invG5F21, orbRepF21, clsF21, mulF21, invF21]

/-- Aggregated Θ sums along `tvG3invG5F21` at orbit 37
(block C row): exact rational computation. -/
theorem DTheta_g3invg5_zero_p37 (a : Fin 5) :
    DThetaF21 tvG3invG5F21 37 a = 0 := by
  rw [DThetaF21_eq_blockSum]
  have hb : blockOfF21 (37 : Fin 41) = blockCF21 := by
    simp [blockOfF21, blockAF21, blockBF21, blockCF21,
      Finset.mem_insert, Finset.mem_singleton]
  rw [hb]
  fin_cases a <;>
    simp only [blockCF21,
      Finset.sum_insert (by decide : (35:Fin 41) ∉ ({36, 37} : Finset (Fin 41))),
      Finset.sum_insert (by decide : (36:Fin 41) ∉ ({37} : Finset (Fin 41))),
      Finset.sum_singleton] <;>
    norm_num [KThetaF21, blockAF21, blockBF21, blockCF21, posAF21,
      posBF21, posCF21, KThetaAF21, KThetaBF21, KThetaCF21,
      fibThetaF21, tvG3invG5F21, orbRepF21, clsF21, mulF21, invF21]

/-- Aggregated Θ sums along `tvG3invG5F21`, block A rows
(assembled from the per-orbit computations). -/
theorem DTheta_tvG3invG5_zero_A (i : Fin 17) (a : Fin 5) :
    DThetaF21 tvG3invG5F21 (orbAF21 i) a = 0 := by
  fin_cases i
  · show DThetaF21 tvG3invG5F21 0 a = 0
    exact DTheta_g3invg5_zero_p0 a
  · show DThetaF21 tvG3invG5F21 1 a = 0
    exact DTheta_g3invg5_zero_p1 a
  · show DThetaF21 tvG3invG5F21 2 a = 0
    exact DTheta_g3invg5_zero_p2 a
  · show DThetaF21 tvG3invG5F21 5 a = 0
    exact DTheta_g3invg5_zero_p5 a
  · show DThetaF21 tvG3invG5F21 6 a = 0
    exact DTheta_g3invg5_zero_p6 a
  · show DThetaF21 tvG3invG5F21 7 a = 0
    exact DTheta_g3invg5_zero_p7 a
  · show DThetaF21 tvG3invG5F21 8 a = 0
    exact DTheta_g3invg5_zero_p8 a
  · show DThetaF21 tvG3invG5F21 9 a = 0
    exact DTheta_g3invg5_zero_p9 a
  · show DThetaF21 tvG3invG5F21 10 a = 0
    exact DTheta_g3invg5_zero_p10 a
  · show DThetaF21 tvG3invG5F21 11 a = 0
    exact DTheta_g3invg5_zero_p11 a
  · show DThetaF21 tvG3invG5F21 14 a = 0
    exact DTheta_g3invg5_zero_p14 a
  · show DThetaF21 tvG3invG5F21 15 a = 0
    exact DTheta_g3invg5_zero_p15 a
  · show DThetaF21 tvG3invG5F21 16 a = 0
    exact DTheta_g3invg5_zero_p16 a
  · show DThetaF21 tvG3invG5F21 17 a = 0
    exact DTheta_g3invg5_zero_p17 a
  · show DThetaF21 tvG3invG5F21 18 a = 0
    exact DTheta_g3invg5_zero_p18 a
  · show DThetaF21 tvG3invG5F21 19 a = 0
    exact DTheta_g3invg5_zero_p19 a
  · show DThetaF21 tvG3invG5F21 20 a = 0
    exact DTheta_g3invg5_zero_p20 a

/-- Aggregated Θ sums along `tvG3invG5F21`, block B rows
(assembled from the per-orbit computations). -/
theorem DTheta_tvG3invG5_zero_B (i : Fin 3) (a : Fin 5) :
    DThetaF21 tvG3invG5F21 (orbBF21 i) a = 0 := by
  fin_cases i
  · show DThetaF21 tvG3invG5F21 29 a = 0
    exact DTheta_g3invg5_zero_p29 a
  · show DThetaF21 tvG3invG5F21 30 a = 0
    exact DTheta_g3invg5_zero_p30 a
  · show DThetaF21 tvG3invG5F21 31 a = 0
    exact DTheta_g3invg5_zero_p31 a

/-- Aggregated Θ sums along `tvG3invG5F21`, block C rows
(assembled from the per-orbit computations). -/
theorem DTheta_tvG3invG5_zero_C (i : Fin 3) (a : Fin 5) :
    DThetaF21 tvG3invG5F21 (orbCF21 i) a = 0 := by
  fin_cases i
  · show DThetaF21 tvG3invG5F21 35 a = 0
    exact DTheta_g3invg5_zero_p35 a
  · show DThetaF21 tvG3invG5F21 36 a = 0
    exact DTheta_g3invg5_zero_p36 a
  · show DThetaF21 tvG3invG5F21 37 a = 0
    exact DTheta_g3invg5_zero_p37 a

/-- **Aggregated Θ sums vanish along `tvG3invG5F21`**:
for every orbit `p` and class `a`,
`∑_{q : tvG3invG5F21 q = a} KΘ p q · fib q = 0`. -/
theorem DTheta_tvG3invG5_zero (p : Fin 41) (a : Fin 5) :
    DThetaF21 tvG3invG5F21 p a = 0 := by
  by_cases hA : p ∈ blockAF21
  · obtain ⟨i, hi⟩ : ∃ i : Fin 17, orbAF21 i = p :=
      ⟨posAF21 p, orbA_posA hA⟩
    rw [← hi]
    exact DTheta_tvG3invG5_zero_A i a
  · by_cases hB : p ∈ blockBF21
    · obtain ⟨i, hi⟩ : ∃ i : Fin 3, orbBF21 i = p :=
        ⟨posBF21 p, orbB_posB hB⟩
      rw [← hi]
      exact DTheta_tvG3invG5_zero_B i a
    · by_cases hC : p ∈ blockCF21
      · obtain ⟨i, hi⟩ : ∃ i : Fin 3, orbCF21 i = p :=
          ⟨posCF21 p, orbC_posC hC⟩
        rw [← hi]
        exact DTheta_tvG3invG5_zero_C i a
      · exact DTheta_zero_of_not_mem tvG3invG5F21 hA hB hC a

/-- **Θ action on pullbacks vanishes**: for a class
variable whose aggregated sums all vanish, the Θ form
annihilates every pullback profile. -/
theorem theta_action_zero (tv : Fin 41 → Fin 5)
    (hD : ∀ p a, DThetaF21 tv p a = 0) (v : Fin 5 → ℚ)
    (p : Fin 41) :
    (∑ q, FThetaF21 p q * v (tv q)) = 0 := by
  have hveq : ∀ q : Fin 41, v (tv q)
      = ∑ a, (if tv q = a then v a else 0) := by
    intro q
    rw [Finset.sum_eq_single (tv q)]
    · exact (if_pos rfl).symm
    · intro a _ ha
      exact if_neg (fun h => ha h.symm)
    · intro h
      exact absurd (Finset.mem_univ _) h
  have step : ∀ q : Fin 41, FThetaF21 p q * v (tv q)
      = fibThetaF21 p * ((KThetaF21 p q * fibThetaF21 q) * v (tv q)) := by
    intro q
    rw [FThetaF21]
    ring
  rw [Finset.sum_congr rfl (fun q _ => step q), ← Finset.mul_sum]
  have hS : (∑ q, (KThetaF21 p q * fibThetaF21 q) * v (tv q))
      = ∑ a, DThetaF21 tv p a * v a := by
    rw [Finset.sum_congr rfl (fun q _ => by rw [hveq q, Finset.mul_sum])]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    have e : ∀ q : Fin 41,
        (KThetaF21 p q * fibThetaF21 q) * (if tv q = a then v a else 0)
          = (if tv q = a then KThetaF21 p q * fibThetaF21 q else 0)
            * v a := by
      intro q
      by_cases h : tv q = a <;> simp [h] <;> ring
    rw [Finset.sum_congr rfl (fun q _ => e q), ← Finset.sum_mul]
    rfl
  rw [hS]
  simp [hD]

/-- The Θ bilinear form on orbit profiles. -/
def bilinThetaF21 (ψ ψ' : Fin 41 → ℚ) : ℚ :=
  ∑ p, ∑ q, ψ p * FThetaF21 p q * ψ' q

/-- If the Θ form annihilates `ψ'` under the action,
its bilinear form against `ψ'` vanishes for every
left profile. -/
theorem bilinThetaF21_eq_zero_of_action {ψ' : Fin 41 → ℚ}
    (h : ∀ p, (∑ q, FThetaF21 p q * ψ' q) = 0) (ψ : Fin 41 → ℚ) :
    bilinThetaF21 ψ ψ' = 0 := by
  have e : ∀ p : Fin 41, (∑ q, ψ p * FThetaF21 p q * ψ' q) = 0 := by
    intro p
    have e2 : ∀ q : Fin 41, ψ p * FThetaF21 p q * ψ' q
        = ψ p * (FThetaF21 p q * ψ' q) := fun q => by ring
    rw [Finset.sum_congr rfl (fun q _ => e2 q), ← Finset.mul_sum, h p,
      mul_zero]
  unfold bilinThetaF21
  exact Finset.sum_eq_zero (fun p _ => e p)

/-- Bilinearity in the right argument (pointwise sum). -/
theorem bilinThetaF21_add_right (ψ ψ1 ψ2 : Fin 41 → ℚ) :
    bilinThetaF21 ψ (fun q => ψ1 q + ψ2 q)
      = bilinThetaF21 ψ ψ1 + bilinThetaF21 ψ ψ2 := by
  have e : ∀ p : Fin 41,
      (∑ q, ψ p * FThetaF21 p q * (ψ1 q + ψ2 q))
        = (∑ q, ψ p * FThetaF21 p q * ψ1 q)
          + ∑ q, ψ p * FThetaF21 p q * ψ2 q := by
    intro p
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    ring
  unfold bilinThetaF21
  rw [Finset.sum_congr rfl (fun p _ => e p), Finset.sum_add_distrib]

/-- (Θ-2) vanishing for pullbacks along a class
variable with vanishing aggregated sums. -/
theorem bilinThetaF21_pullback_zero (tv : Fin 41 → Fin 5)
    (hD : ∀ p a, DThetaF21 tv p a = 0) (v : Fin 5 → ℚ)
    (ψ : Fin 41 → ℚ) :
    bilinThetaF21 ψ (fun q => v (tv q)) = 0 :=
  bilinThetaF21_eq_zero_of_action
    (fun p => theta_action_zero tv hD v p) ψ

/-- **GD-iii non-firing, Θ reading `g₃` (Θ-2)**: the
restriction of the Θ form to pullbacks of the κ₄
kernel — in fact of ALL class functions — along the
`g₃` cycle reading is exactly zero. -/
theorem restrict_theta_g3_zero (φ ψ : Fin 5 → ℚ) :
    bilinThetaF21 (fun p => φ (tvG3F21 p)) (fun p => ψ (tvG3F21 p))
      = 0 :=
  bilinThetaF21_pullback_zero tvG3F21 DTheta_tvG3_zero ψ _

/-- **GD-iii non-firing, Θ reading `g₅` (Θ-2)**. -/
theorem restrict_theta_g5_zero (φ ψ : Fin 5 → ℚ) :
    bilinThetaF21 (fun p => φ (tvG5F21 p)) (fun p => ψ (tvG5F21 p))
      = 0 :=
  bilinThetaF21_pullback_zero tvG5F21 DTheta_tvG5_zero ψ _

/-- **GD-iii non-firing, Θ reading `g₃⁻¹g₅` (Θ-2)**. -/
theorem restrict_theta_g3invg5_zero (φ ψ : Fin 5 → ℚ) :
    bilinThetaF21 (fun p => φ (tvG3invG5F21 p))
        (fun p => ψ (tvG3invG5F21 p)) = 0 :=
  bilinThetaF21_pullback_zero tvG3invG5F21 DTheta_tvG3invG5_zero ψ _

/-- **GD-iii non-firing, Θ joint span (Θ-2)**: for
every left orbit profile `X` and every joint-span
profile (a sum of one pullback under each of the
three cycle readings), the Θ bilinear form is
exactly zero — the script's joint-span reading
included. -/
theorem restrict_theta_joint_zero (X : Fin 41 → ℚ)
    (v1 v2 v3 : Fin 5 → ℚ) :
    bilinThetaF21 X
        (fun q => v1 (tvG3F21 q) + v2 (tvG5F21 q)
          + v3 (tvG3invG5F21 q)) = 0 := by
  rw [show (fun q => v1 (tvG3F21 q) + v2 (tvG5F21 q)
        + v3 (tvG3invG5F21 q))
      = (fun q => (v1 (tvG3F21 q) + v2 (tvG5F21 q))
        + v3 (tvG3invG5F21 q)) from rfl,
    bilinThetaF21_add_right, bilinThetaF21_add_right]
  rw [bilinThetaF21_pullback_zero tvG3F21 DTheta_tvG3_zero v1 X,
    bilinThetaF21_pullback_zero tvG5F21 DTheta_tvG5_zero v2 X,
    bilinThetaF21_pullback_zero tvG3invG5F21 DTheta_tvG3invG5_zero v3 X]
  norm_num

end GDF21Theta

section GDF21Verdict

/-- **GD-iii NON-FIRING at (F21, ρ₃), certified —
the Route-A-critical headline of this brick.** For
any two observables in `ker κ₄^dep`, every channel's
restriction is exactly zero: the five class-space
channels, and Θ(2,2,2) under all three (Θ-2) cycle
readings and their joint span. No K-Kn event at this
seat; Route A stands here. -/
theorem gd_iii_no_fire_F21 {φ ψ : Fin 5 → ℚ}
    (hφ : inKerSpanF21 φ) (hψ : inKerSpanF21 ψ) :
    bilinOf (quadFormOf K2111F21) φ ψ = 0
    ∧ bilinOf (quadFormOf K3111F21) φ ψ = 0
    ∧ bilinOf (quadFormOf K2211adjF21) φ ψ = 0
    ∧ bilinOf (quadFormOf K2211oppF21) φ ψ = 0
    ∧ bilinOf FC6F21 φ ψ = 0
    ∧ bilinThetaF21 (fun p => φ (tvG3F21 p)) (fun p => ψ (tvG3F21 p)) = 0
    ∧ bilinThetaF21 (fun p => φ (tvG5F21 p)) (fun p => ψ (tvG5F21 p)) = 0
    ∧ bilinThetaF21 (fun p => φ (tvG3invG5F21 p))
        (fun p => ψ (tvG3invG5F21 p)) = 0
    ∧ bilinThetaF21
        (fun p => φ (tvG3F21 p) + φ (tvG5F21 p) + φ (tvG3invG5F21 p))
        (fun p => ψ (tvG3F21 p) + ψ (tvG5F21 p)
          + ψ (tvG3invG5F21 p)) = 0 :=
  ⟨restrict_K2111F21_zero hφ hψ, restrict_K3111F21_zero hφ hψ,
    restrict_K2211adjF21_zero hφ hψ, restrict_K2211oppF21_zero hφ hψ,
    restrict_C6F21_zero hφ hψ, restrict_theta_g3_zero φ ψ,
    restrict_theta_g5_zero φ ψ, restrict_theta_g3invg5_zero φ ψ,
    restrict_theta_joint_zero _ ψ ψ ψ⟩

/-- **GD-PROBE-R-b verdict at Seat 1 (F21, ρ₃),
certified.** The κ₄ kernel is the 3-dimensional span
of `{(1,1,1,0,0), e₃, e₄}`; the five class-space
channels are positive multiples of κ₄
(λ = 10, 31, 50, 25, 7203/320); Θ escapes (Θ-1);
and GD-iii does not fire — every channel restriction
to the kernel is exactly zero. Together with R-a's
Python verdict this certifies **GD-ii at this seat**
(GD-strong dies via the Θ escape; GD-global and
GD-kernel untouched; Route A stands). The joint
two-seat registry entry is R-c's. NO CLAIM; parts 0;
dials 0/4. -/
theorem gd_probe_R_b_verdict_F21 :
    (∀ φ : Fin 5 → ℚ, formOf F4F21 φ = 0 ↔ inKerSpanF21 φ)
    ∧ (∀ φ ψ : Fin 5 → ℚ,
        bilinOf (quadFormOf K2111F21) φ ψ = 10 * bilinOf F4F21 φ ψ)
    ∧ (∀ φ ψ : Fin 5 → ℚ,
        bilinOf (quadFormOf K3111F21) φ ψ = 31 * bilinOf F4F21 φ ψ)
    ∧ (∀ φ ψ : Fin 5 → ℚ,
        bilinOf (quadFormOf K2211adjF21) φ ψ
          = 50 * bilinOf F4F21 φ ψ)
    ∧ (∀ φ ψ : Fin 5 → ℚ,
        bilinOf (quadFormOf K2211oppF21) φ ψ
          = 25 * bilinOf F4F21 φ ψ)
    ∧ (∀ φ ψ : Fin 5 → ℚ,
        bilinOf FC6F21 φ ψ = (7203 / 320) * bilinOf F4F21 φ ψ)
    ∧ (KThetaF21 0 0 ≠ 0
        ∧ (¬ ∃ lam : ℚ, ∀ p q,
            KThetaF21 p q = lam * K4F21 (tvG3F21 p) (tvG3F21 q)))
    ∧ (∀ φ ψ : Fin 5 → ℚ, inKerSpanF21 φ → inKerSpanF21 ψ →
        bilinThetaF21 (fun p => φ (tvG3F21 p))
          (fun p => ψ (tvG3F21 p)) = 0) :=
  ⟨fun φ => K4F21_form_eq_zero_iff φ, fun φ ψ => F2111F21_prop φ ψ,
    fun φ ψ => F3111F21_prop φ ψ, fun φ ψ => F2211adjF21_prop φ ψ,
    fun φ ψ => F2211oppF21_prop φ ψ, fun φ ψ => FC6F21_prop φ ψ,
    ⟨KTheta_ne_zero, theta_not_pullback_g3⟩,
    fun φ ψ _ _ => restrict_theta_g3_zero φ ψ⟩

end GDF21Verdict

end ThetLogos
