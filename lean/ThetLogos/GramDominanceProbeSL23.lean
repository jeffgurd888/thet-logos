import ThetLogos.GramDominanceProbeF21

/-!
# GD-PROBE-R-c: Lean certification, Seat 2 (SL(2,3), ρ₂′) + the joint verdict

**NO CLAIM.** Parts of any official statement closed by this
module: **0**. Dials: **0/4**. Registry: **BR1-007** (the
GD-PROBE-R-a Python verdict this module certifies, jointly
with `ThetLogos.GramDominanceProbeF21`). Governing:
`pack-gd-probe-r-c.md`; re-scope memo
`scoping-gd-discriminator-rescope-2026-10-30.md` §2/§5;
seats script `gdprobeR_seat.py` and its run log
`gdprobeR-run.txt` (Seat 2 section, lines 129–235).

**What is certified here (Seat 2, N = 4).** At
(SL(2,3), ρ₂′), FULL class space (7 classes):
(1) the κ₄^dep kernel theorem — the kernel of the seat's
κ₄ form is the span of the five extraction basis vectors
`(0,1,0,0,0,0,0)`, `(-2,0,-1,1,0,0,0)`,
`(2,0,1,0,1,0,0)`, `(0,0,1,0,0,1,0)`, `(1,0,0,0,0,0,1)`
(run log lines 143–148);
(2) **GD-iii non-firing, certified at Seat 2** — every
channel's restriction to that kernel is exactly zero,
Θ(2,2,2) included (its orbit kernel is identically zero
at this seat, rank 0, 76 orbits);
(3) channel facts: (3,1,1,1) form `= 11 · κ₄` form;
C6 form `= (432/5) · κ₄` form; and the (2,1,1,1),
(2,2,1,1)-adjacent, (2,2,1,1)-opposite and Θ class-space
forms are **identically zero**;
(4) **GD-strong falsified at Seat 2, independently** —
in the seat's own terms (identification stated in the
`GDStrongFalsifiedSL23` section below): GD-0's registered
`GDStrong5`/`GDStrong6` demand a strictly positive
multiple for every channel, and this seat has zero
channels, so the seat-level instances of both demands
fail here — by positivity failure, NOT by Θ escape
(the Seat 1 mechanism);
(5) **the joint verdict** `gd_probe_R_joint_verdict`,
assembling both re-registered seats.

**GD context, on the face.** GD-strong is falsified at
both seats (Θ escape at F21; zero channels at SL(2,3));
GD-iii fired at NEITHER seat; GD-global and GD-kernel
are untouched and stand as the registered targets;
Route A stands.

**BRIDGE-1 notes (script governs; checked line by line
against the run log).** (a) C6 carries TWO multiples,
exactly as at Seat 1: kernel-level (per-support against
per-quad κ₄) `1/16`, form-level `432/5` — the pack's
"C6 = (432/5)·κ₄" is the form-level statement, and both
are proved below (`KC6SL23_prop`, `FC6SL23_prop`).
(b) The pack's "Θ orbit kernel rank 0" and "λ = 0 under
all six single-variable readings" are the same fact seen
twice: the extracted 76×76 orbit kernel is identically
zero, so every reading factors trivially with effective
multiple `0`; there is no nonzero Θ kernel to extract,
and this module accordingly defines the Θ orbit kernel
as the zero kernel the script extracted and proves the
readings from that. No other pack/script conflict was
found: class order (ord1, ord4, ord6, ord3, ord6, ord3,
ord2), sizes, character data, fibers, kernel basis,
channel multiples (11, 432/5) all match the run log.

**Seat architecture (mirrors R-b).** Character/class
level: κ₄^dep is DEFINED as the doubled-column Gram of
the character data,
`K a b = (1/128)(R_a R_b + (3/4) I_a I_b)` with
`R = Re χ_ρ₂′` and `I` the imaginary part in units of
`√3/2` (so `(3/4) I_a I_b = Imχ_a · Imχ_b` in ℚ); the
script's self-check kernel `(1/128)(RRᵀ + IIᵀ)` is then
a THEOREM (`K4SL23_eq`), never a definition into place.
Channel kernels are the script's extracted matrices as
explicit class matrices; every λ is proved against the
independently defined κ₄.
-/

namespace ThetLogos

open Finset

section GDSL23Seat

/-! ## Seat data: classes, character, fibers -/

/-- Conjugacy class sizes of SL(2,3) in the script's
class order: ord1, ord4, ord6, ord3, ord6, ord3, ord2. -/
def classSizeSL23 : Fin 7 → ℚ := ![1, 6, 4, 4, 4, 4, 1]

/-- `Re χ` of ρ₂′ by class:
`(2, 0, -1/2, 1/2, -1/2, 1/2, -2)`. -/
def chiRSL23 : Fin 7 → ℚ := ![2, 0, -1 / 2, 1 / 2, -1 / 2, 1 / 2, -2]

/-- `Im χ` of ρ₂′ by class, in units of `√3 / 2`:
`(0, 0, -1, -1, 1, 1, 0)` (recovered from the script's
sign rule and cross-checked entrywise against its
extracted κ₄ kernel in `K4SL23_eq`). -/
def chiIcSL23 : Fin 7 → ℚ := ![0, 0, -1, -1, 1, 1, 0]

/-- Step-0R (iii) at the character level: `e₁ = 0`, the
size-weighted mean of `Re χ` vanishes (`|G| = 24`). -/
theorem e1_SL23 :
    (∑ a, classSizeSL23 a * chiRSL23 a) / 24 = 0 := by
  rw [Fin.sum_univ_seven]
  simp [classSizeSL23, chiRSL23] <;> norm_num

/-- Irreducibility of ρ₂′ from the character data:
`(1/24) ∑ size_a (R_a² + (3/4) I_a²) = 1`. -/
theorem chi_irred_SL23 :
    (∑ a, classSizeSL23 a * (chiRSL23 a ^ 2 + (3 / 4) * chiIcSL23 a ^ 2)) / 24
      = 1 := by
  rw [Fin.sum_univ_seven]
  simp [classSizeSL23, chiRSL23, chiIcSL23]
  norm_num

/-- Quad fibers at this seat (plaquette = wrap, script):
`[13824, 82944, 55296, 55296, 55296, 55296, 13824]`
(= `13824 · classSize`). -/
def fibQSL23 : Fin 7 → ℚ :=
  ![13824, 82944, 55296, 55296, 55296, 55296, 13824]

/-- C6 fibers at this seat (script):
`[7962624, 47775744, 31850496, 31850496, 31850496,
31850496, 7962624]`. -/
def fibC6SL23 : Fin 7 → ℚ :=
  ![7962624, 47775744, 31850496, 31850496, 31850496, 31850496, 7962624]

/-- The C6 fibers are `576` times the quad fibers,
entrywise (576 = 24²). -/
theorem fibC6SL23_eq (a : Fin 7) :
    fibC6SL23 a = 576 * fibQSL23 a := by
  fin_cases a <;> simp [fibC6SL23, fibQSL23] <;> norm_num

/-! ## κ₄^dep at the seat: Gram definition, script kernel -/

/-- **The seat's κ₄^dep per-quad kernel, DEFINED as the
doubled-column Gram of the character data** in the
script's normalization:
`K a b = (1/128) (R_a R_b + (3/4) I_a I_b)`, where the
`(3/4) I_a I_b` term is `Imχ_a · Imχ_b` in rational
coordinates (`Imχ = I · √3/2`). -/
def K4SL23 (a b : Fin 7) : ℚ :=
  (1 / 128) * (chiRSL23 a * chiRSL23 b + (3 / 4) * (chiIcSL23 a * chiIcSL23 b))

/-- **BRIDGE-1 certificate**: the Gram definition above
reproduces the script's extracted per-quad kernel
entrywise (run log, Seat 2 κ₄ plaquette = wrap). -/
theorem K4SL23_eq (a b : Fin 7) :
    K4SL23 a b =
      ![![1 / 32, 0, -1 / 128, 1 / 128, -1 / 128, 1 / 128, -1 / 32],
        ![0, 0, 0, 0, 0, 0, 0],
        ![-1 / 128, 0, 1 / 128, 1 / 256, -1 / 256, -1 / 128, 1 / 128],
        ![1 / 128, 0, 1 / 256, 1 / 128, -1 / 128, -1 / 256, -1 / 128],
        ![-1 / 128, 0, -1 / 256, -1 / 128, 1 / 128, 1 / 256, 1 / 128],
        ![1 / 128, 0, -1 / 128, -1 / 256, 1 / 256, 1 / 128, -1 / 128],
        ![-1 / 32, 0, 1 / 128, -1 / 128, 1 / 128, -1 / 128, 1 / 32]] a b := by
  fin_cases a <;> fin_cases b <;>
    simp [K4SL23, chiRSL23, chiIcSL23] <;> norm_num

/-- The κ₄ kernel's **fiber-weighted** margins vanish
exactly — the script's margins-zero. -/
theorem K4SL23_fibMargins (a : Fin 7) :
    ∑ b, K4SL23 a b * fibQSL23 b = 0 := by
  rw [Fin.sum_univ_seven]
  fin_cases a <;> simp [K4SL23, chiRSL23, chiIcSL23, fibQSL23] <;> norm_num

/-- The census total kernel: `192` plaquette quads plus
`48` wrap quads; the script found the two per-quad
kernels equal, so the total is `240 • K`. -/
def K4totSL23 (a b : Fin 7) : ℚ := 240 * K4SL23 a b

/-- **The κ₄^dep form matrix** `F4 = D K_tot D`,
`D = diag(quad fibers)` — the script's `F4` (run log,
Seat 2), the matrix whose kernel is deliverable (1). -/
def F4SL23 (a b : Fin 7) : ℚ := fibQSL23 a * K4totSL23 a b * fibQSL23 b

/-- The first Gram vector of the form: `u_a = fib_a · R_a`
`= (27648, 0, -27648, 27648, -27648, 27648, -27648)`. -/
def uSL23 (a : Fin 7) : ℚ := fibQSL23 a * chiRSL23 a

/-- The second Gram vector: `v_a = fib_a · I_a`
`= (0, 0, -55296, -55296, 55296, 55296, 0)`. -/
def vSL23 (a : Fin 7) : ℚ := fibQSL23 a * chiIcSL23 a

theorem uSL23_0 : uSL23 0 = 27648 := by
  simp [uSL23, fibQSL23, chiRSL23] <;> norm_num
theorem uSL23_1 : uSL23 1 = 0 := by simp [uSL23, fibQSL23, chiRSL23]
theorem uSL23_2 : uSL23 2 = -27648 := by
  simp [uSL23, fibQSL23, chiRSL23] <;> norm_num
theorem uSL23_3 : uSL23 3 = 27648 := by
  simp [uSL23, fibQSL23, chiRSL23] <;> norm_num
theorem uSL23_4 : uSL23 4 = -27648 := by
  simp [uSL23, fibQSL23, chiRSL23] <;> norm_num
theorem uSL23_5 : uSL23 5 = 27648 := by
  simp [uSL23, fibQSL23, chiRSL23] <;> norm_num
theorem uSL23_6 : uSL23 6 = -27648 := by
  simp [uSL23, fibQSL23, chiRSL23] <;> norm_num
theorem vSL23_0 : vSL23 0 = 0 := by simp [vSL23, fibQSL23, chiIcSL23]
theorem vSL23_1 : vSL23 1 = 0 := by simp [vSL23, fibQSL23, chiIcSL23]
theorem vSL23_2 : vSL23 2 = -55296 := by
  simp [vSL23, fibQSL23, chiIcSL23] <;> norm_num
theorem vSL23_3 : vSL23 3 = -55296 := by
  simp [vSL23, fibQSL23, chiIcSL23] <;> norm_num
theorem vSL23_4 : vSL23 4 = 55296 := by
  simp [vSL23, fibQSL23, chiIcSL23] <;> norm_num
theorem vSL23_5 : vSL23 5 = 55296 := by
  simp [vSL23, fibQSL23, chiIcSL23] <;> norm_num
theorem vSL23_6 : vSL23 6 = 0 := by simp [vSL23, fibQSL23, chiIcSL23]

/-- **Gram factorization of the κ₄ form**:
`F4 a b = (15/8) (u_a u_b + (3/4) v_a v_b)`
(`240/128 = 15/8`). -/
theorem F4SL23_gram (a b : Fin 7) :
    F4SL23 a b = (15 / 8) * (uSL23 a * uSL23 b
      + (3 / 4) * (vSL23 a * vSL23 b)) := by
  simp [F4SL23, K4totSL23, K4SL23, uSL23, vSL23]
  ring

/-- The κ₄ form's margins vanish exactly. -/
theorem F4SL23_margins (a : Fin 7) : ∑ b, F4SL23 a b = 0 := by
  rw [Fin.sum_univ_seven]
  fin_cases a <;>
    simp [F4SL23, K4totSL23, K4SL23, chiRSL23, chiIcSL23, fibQSL23] <;>
    norm_num

end GDSL23Seat

section GDSL23Kernel

/-! ## Bilinear forms, the two kernel functionals -/

/-- The bilinear form of a class matrix at this seat
(7 classes; distinct from the 5-class `bilinOf`). -/
def bilinS23 (M : Fin 7 → Fin 7 → ℚ) (φ ψ : Fin 7 → ℚ) : ℚ :=
  ∑ a, ∑ b, φ a * M a b * ψ b

/-- The diagonal form of a class matrix at this seat. -/
def formS23 (M : Fin 7 → Fin 7 → ℚ) (φ : Fin 7 → ℚ) : ℚ :=
  bilinS23 M φ φ

/-- First kernel functional: `L₁ φ = ∑ a, φ_a u_a`. -/
def L1SL23 (φ : Fin 7 → ℚ) : ℚ := ∑ a, φ a * uSL23 a

/-- Second kernel functional: `L₂ φ = ∑ a, φ_a v_a`. -/
def L2SL23 (φ : Fin 7 → ℚ) : ℚ := ∑ a, φ a * vSL23 a

theorem L1SL23_eq (φ : Fin 7 → ℚ) :
    L1SL23 φ = 27648 * φ 0 - 27648 * φ 2 + 27648 * φ 3
      - 27648 * φ 4 + 27648 * φ 5 - 27648 * φ 6 := by
  rw [L1SL23, Fin.sum_univ_seven, uSL23_0, uSL23_1, uSL23_2, uSL23_3,
    uSL23_4, uSL23_5, uSL23_6]
  ring

theorem L2SL23_eq (φ : Fin 7 → ℚ) :
    L2SL23 φ = -55296 * φ 2 - 55296 * φ 3 + 55296 * φ 4 + 55296 * φ 5 := by
  rw [L2SL23, Fin.sum_univ_seven, vSL23_0, vSL23_1, vSL23_2, vSL23_3,
    vSL23_4, vSL23_5, vSL23_6]
  ring

/-- **The κ₄ bilinear form, Gram-expanded**:
`φᵀ F4 ψ = (15/8) (L₁φ·L₁ψ + (3/4) L₂φ·L₂ψ)`. -/
theorem bilinS23_F4SL23 (φ ψ : Fin 7 → ℚ) :
    bilinS23 F4SL23 φ ψ = (15 / 8) * (L1SL23 φ * L1SL23 ψ
      + (3 / 4) * (L2SL23 φ * L2SL23 ψ)) := by
  have e : ∀ a b : Fin 7, φ a * F4SL23 a b * ψ b
      = ((15 / 8) * (φ a * uSL23 a)) * (ψ b * uSL23 b)
        + ((15 / 8) * (3 / 4) * (φ a * vSL23 a)) * (ψ b * vSL23 b) := by
    intro a b
    rw [F4SL23_gram]
    ring
  unfold bilinS23 L1SL23 L2SL23
  rw [Finset.sum_congr rfl (fun a _ =>
    Finset.sum_congr rfl (fun b _ => e a b))]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_add_distrib),
    Finset.sum_add_distrib, ← Finset.sum_mul_sum, ← Finset.sum_mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- The row action of the κ₄ form matrix:
`∑ a, φ_a F4 a b = (15/8)(L₁φ · u_b + (3/4) L₂φ · v_b)`. -/
theorem rowAction_F4SL23 (φ : Fin 7 → ℚ) (b : Fin 7) :
    (∑ a, φ a * F4SL23 a b)
      = (15 / 8) * (L1SL23 φ * uSL23 b + (3 / 4) * (L2SL23 φ * vSL23 b)) := by
  have e : ∀ a : Fin 7, φ a * F4SL23 a b
      = ((15 / 8) * (φ a * uSL23 a)) * uSL23 b
        + ((15 / 8) * (3 / 4) * (φ a * vSL23 a)) * vSL23 b := by
    intro a
    rw [F4SL23_gram]
    ring
  rw [Finset.sum_congr rfl (fun a _ => e a), Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum]
  unfold L1SL23 L2SL23
  ring

/-! ## Deliverable (1): the kernel theorem -/

/-- The five kernel basis profiles — the script's
extraction nullspace basis of `F4` (run log lines
143–148). -/
def kv0SL23 : Fin 7 → ℚ := ![0, 1, 0, 0, 0, 0, 0]
def kv1SL23 : Fin 7 → ℚ := ![-2, 0, -1, 1, 0, 0, 0]
def kv2SL23 : Fin 7 → ℚ := ![2, 0, 1, 0, 1, 0, 0]
def kv3SL23 : Fin 7 → ℚ := ![0, 0, 1, 0, 0, 1, 0]
def kv4SL23 : Fin 7 → ℚ := ![1, 0, 0, 0, 0, 0, 1]

/-- Membership in the kernel span, concretely:
`φ = c₀·kv0 + c₁·kv1 + c₂·kv2 + c₃·kv3 + c₄·kv4`. -/
def inKerSpanSL23 (φ : Fin 7 → ℚ) : Prop :=
  ∃ c0 c1 c2 c3 c4 : ℚ, φ = fun a =>
    c0 * kv0SL23 a + c1 * kv1SL23 a + c2 * kv2SL23 a
      + c3 * kv3SL23 a + c4 * kv4SL23 a

/-- Span membership is exactly the two coordinate
relations `φ₂ = -φ₃ + φ₄ + φ₅` and
`φ₀ = -2φ₃ + 2φ₄ + φ₆` (classes 1, 3, 4, 5, 6 are the
free coordinates, read off the basis). -/
theorem inKerSpanSL23_iff (φ : Fin 7 → ℚ) :
    inKerSpanSL23 φ ↔ (φ 2 = -φ 3 + φ 4 + φ 5
      ∧ φ 0 = -2 * φ 3 + 2 * φ 4 + φ 6) := by
  constructor
  · rintro ⟨c0, c1, c2, c3, c4, h⟩
    have e : ∀ a, φ a = c0 * kv0SL23 a + c1 * kv1SL23 a
        + c2 * kv2SL23 a + c3 * kv3SL23 a + c4 * kv4SL23 a :=
      fun a => congrFun h a
    have e0 := e 0
    have e2 := e 2
    have e3 := e 3
    have e4 := e 4
    have e5 := e 5
    have e6 := e 6
    simp [kv0SL23, kv1SL23, kv2SL23, kv3SL23, kv4SL23] at e0 e2 e3 e4 e5 e6
    constructor <;> linarith
  · rintro ⟨h2, h0⟩
    refine ⟨φ 1, φ 3, φ 4, φ 5, φ 6, ?_⟩
    funext a
    fin_cases a <;>
      simp [kv0SL23, kv1SL23, kv2SL23, kv3SL23, kv4SL23] <;> linarith

/-- `L₁ φ = 0 ∧ L₂ φ = 0` iff `φ` lies in the kernel
span — the two functionals are the two coordinate
relations, rescaled. -/
theorem L12_eq_zero_iff_SL23 (φ : Fin 7 → ℚ) :
    (L1SL23 φ = 0 ∧ L2SL23 φ = 0) ↔ inKerSpanSL23 φ := by
  rw [L1SL23_eq, L2SL23_eq, inKerSpanSL23_iff]
  constructor
  · rintro ⟨h1, h2⟩
    have h2' : φ 2 = -φ 3 + φ 4 + φ 5 := by linarith
    refine ⟨h2', ?_⟩
    linarith
  · rintro ⟨h2, h0⟩
    constructor <;> linarith

/-- Kernel-span membership gives the `L₁ = L₂ = 0`
functionals. -/
theorem L12_of_inKerSpanSL23 {φ : Fin 7 → ℚ} (h : inKerSpanSL23 φ) :
    L1SL23 φ = 0 ∧ L2SL23 φ = 0 :=
  (L12_eq_zero_iff_SL23 φ).mpr h

/-- **Kernel theorem, form version (deliverable 1).**
The κ₄^dep diagonal form at (SL(2,3), ρ₂′) vanishes
exactly on the span of the extraction's five basis
vectors — a 5-dimensional kernel. -/
theorem K4SL23_form_eq_zero_iff (φ : Fin 7 → ℚ) :
    formS23 F4SL23 φ = 0 ↔ inKerSpanSL23 φ := by
  rw [formS23, bilinS23_F4SL23]
  constructor
  · intro h
    have hS : L1SL23 φ * L1SL23 φ + (3 / 4) * (L2SL23 φ * L2SL23 φ) = 0 := by
      nlinarith [h]
    have h1 : L1SL23 φ * L1SL23 φ = 0 := by
      have g1 : 0 ≤ L1SL23 φ * L1SL23 φ := mul_self_nonneg _
      have g2 : 0 ≤ (3 / 4 : ℚ) * (L2SL23 φ * L2SL23 φ) := by
        apply mul_nonneg (by norm_num) (mul_self_nonneg _)
      linarith
    have h2 : L2SL23 φ * L2SL23 φ = 0 := by
      have g1 : 0 ≤ L1SL23 φ * L1SL23 φ := mul_self_nonneg _
      have g2 : 0 ≤ (3 / 4 : ℚ) * (L2SL23 φ * L2SL23 φ) := by
        apply mul_nonneg (by norm_num) (mul_self_nonneg _)
      nlinarith
    have hL : L1SL23 φ = 0 ∧ L2SL23 φ = 0 :=
      ⟨mul_self_eq_zero.mp h1, mul_self_eq_zero.mp h2⟩
    exact (L12_eq_zero_iff_SL23 φ).mp hL
  · intro h
    have hL : L1SL23 φ = 0 ∧ L2SL23 φ = 0 := L12_of_inKerSpanSL23 h
    rw [hL.1, hL.2]
    norm_num

/-- **Kernel theorem, matrix version (deliverable 1).**
`φ` is annihilated by the κ₄^dep form matrix iff it
lies in the same span. -/
theorem K4SL23_matrixKer_iff (φ : Fin 7 → ℚ) :
    (∀ b, (∑ a, φ a * F4SL23 a b) = 0) ↔ inKerSpanSL23 φ := by
  constructor
  · intro h
    have h0 := h 0
    rw [rowAction_F4SL23, uSL23_0, vSL23_0] at h0
    have hL1 : L1SL23 φ = 0 := by nlinarith [h0]
    have h2 := h 2
    rw [rowAction_F4SL23, uSL23_2, vSL23_2, hL1] at h2
    have hL2 : L2SL23 φ = 0 := by nlinarith [h2]
    exact (L12_eq_zero_iff_SL23 φ).mp ⟨hL1, hL2⟩
  · intro h b
    have hL : L1SL23 φ = 0 ∧ L2SL23 φ = 0 := L12_of_inKerSpanSL23 h
    rw [rowAction_F4SL23, hL.1, hL.2]
    norm_num

/-- The kernel is exactly 5-dimensional: the five basis
profiles are linearly independent (evaluation at
classes 1, 3, 4, 5, 6 separates the coefficients) and
span the kernel by `K4SL23_form_eq_zero_iff`. -/
theorem kv_independentSL23 (c0 c1 c2 c3 c4 : ℚ)
    (h : (fun a => c0 * kv0SL23 a + c1 * kv1SL23 a + c2 * kv2SL23 a
      + c3 * kv3SL23 a + c4 * kv4SL23 a) = fun _ => 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 := by
  have h1 := congrFun h 1
  have h3 := congrFun h 3
  have h4 := congrFun h 4
  have h5 := congrFun h 5
  have h6 := congrFun h 6
  simp [kv0SL23, kv1SL23, kv2SL23, kv3SL23, kv4SL23] at h1 h3 h4 h5 h6
  exact ⟨h1, h3, h4, h5, h6⟩

end GDSL23Kernel

section GDSL23Channels

/-! ## The five class-space channels: extracted kernels -/

/-- The order-5 channel (2,1,1,1) per-quad kernel at
this seat — the script's extracted matrix is
**identically zero** (run log, Seat 2 (2,1,1,1) channel:
every entry `0`, plaquette = wrap). -/
def K2111SL23 : Fin 7 → Fin 7 → ℚ := fun _ _ => 0

/-- The order-6 channel (3,1,1,1) per-quad kernel
(run log, Seat 2 (3,1,1,1) channel). -/
def K3111SL23 : Fin 7 → Fin 7 → ℚ :=
  ![![11 / 32, 0, -11 / 128, 11 / 128, -11 / 128, 11 / 128, -11 / 32],
    ![0, 0, 0, 0, 0, 0, 0],
    ![-11 / 128, 0, 11 / 128, 11 / 256, -11 / 256, -11 / 128, 11 / 128],
    ![11 / 128, 0, 11 / 256, 11 / 128, -11 / 128, -11 / 256, -11 / 128],
    ![-11 / 128, 0, -11 / 256, -11 / 128, 11 / 128, 11 / 256, 11 / 128],
    ![11 / 128, 0, -11 / 128, -11 / 256, 11 / 256, 11 / 128, -11 / 128],
    ![-11 / 32, 0, 11 / 128, -11 / 128, 11 / 128, -11 / 128, 11 / 32]]

/-- The order-6 channel (2,2,1,1)-adjacent per-quad
kernel — **identically zero** in the script's
extraction (run log, Seat 2). -/
def K2211adjSL23 : Fin 7 → Fin 7 → ℚ := fun _ _ => 0

/-- The order-6 channel (2,2,1,1)-opposite per-quad
kernel — **identically zero** in the script's
extraction (run log, Seat 2). -/
def K2211oppSL23 : Fin 7 → Fin 7 → ℚ := fun _ _ => 0

/-- The order-6 channel C6 per-support kernel
(run log, Seat 2 C6 channel). -/
def KC6SL23 : Fin 7 → Fin 7 → ℚ :=
  ![![1 / 512, 0, -1 / 2048, 1 / 2048, -1 / 2048, 1 / 2048, -1 / 512],
    ![0, 0, 0, 0, 0, 0, 0],
    ![-1 / 2048, 0, 1 / 2048, 1 / 4096, -1 / 4096, -1 / 2048, 1 / 2048],
    ![1 / 2048, 0, 1 / 4096, 1 / 2048, -1 / 2048, -1 / 4096, -1 / 2048],
    ![-1 / 2048, 0, -1 / 4096, -1 / 2048, 1 / 2048, 1 / 4096, 1 / 2048],
    ![1 / 2048, 0, -1 / 2048, -1 / 4096, 1 / 4096, 1 / 2048, -1 / 2048],
    ![-1 / 512, 0, 1 / 2048, -1 / 2048, 1 / 2048, -1 / 2048, 1 / 512]]

/-- A quad channel's form matrix: quad fibers and the
census factor `240`, as for κ₄. -/
def quadFormOfS23 (K : Fin 7 → Fin 7 → ℚ) (a b : Fin 7) : ℚ :=
  fibQSL23 a * (240 * K a b) * fibQSL23 b

/-- The C6 channel's form matrix: C6 fibers times the
per-support kernel (the script's `form_matrix`). -/
def FC6SL23 (a b : Fin 7) : ℚ := fibC6SL23 a * KC6SL23 a b * fibC6SL23 b

/-! ## Deliverable (3): proportionality, kernel level -/

/-- (2,1,1,1) kernel `= 0 · κ₄` kernel — the zero
channel (script λ = 0). -/
theorem K2111SL23_prop (a b : Fin 7) :
    K2111SL23 a b = 0 * K4SL23 a b := by
  simp [K2111SL23]

/-- (3,1,1,1) kernel `= 11 · κ₄` kernel. -/
theorem K3111SL23_prop (a b : Fin 7) :
    K3111SL23 a b = 11 * K4SL23 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [K3111SL23, K4SL23, chiRSL23, chiIcSL23] <;> norm_num

/-- (2,2,1,1)-adjacent kernel `= 0 · κ₄` kernel — the
zero channel (script λ = 0). -/
theorem K2211adjSL23_prop (a b : Fin 7) :
    K2211adjSL23 a b = 0 * K4SL23 a b := by
  simp [K2211adjSL23]

/-- (2,2,1,1)-opposite kernel `= 0 · κ₄` kernel — the
zero channel (script λ = 0). -/
theorem K2211oppSL23_prop (a b : Fin 7) :
    K2211oppSL23 a b = 0 * K4SL23 a b := by
  simp [K2211oppSL23]

/-- C6 per-support kernel `= (1/16) · κ₄` kernel (the
kernel-level multiple; the form-level multiple is
`432/5`, see `FC6SL23_prop`). -/
theorem KC6SL23_prop (a b : Fin 7) :
    KC6SL23 a b = (1 / 16) * K4SL23 a b := by
  fin_cases a <;> fin_cases b <;>
    simp [KC6SL23, K4SL23, chiRSL23, chiIcSL23] <;> norm_num

/-! ## Deliverable (3): proportionality, form level -/

/-- Bilinear forms respect entrywise proportionality
(this seat's version). -/
theorem bilinS23_of_entrywise {M M' : Fin 7 → Fin 7 → ℚ} {lam : ℚ}
    (h : ∀ a b, M a b = lam * M' a b) (φ ψ : Fin 7 → ℚ) :
    bilinS23 M φ ψ = lam * bilinS23 M' φ ψ := by
  have e : ∀ a b, φ a * M a b * ψ b
      = lam * (φ a * M' a b * ψ b) := by
    intro a b
    rw [h a b]
    ring
  unfold bilinS23
  rw [Finset.sum_congr rfl (fun a _ =>
    Finset.sum_congr rfl (fun b _ => e a b)), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]

/-- **(2,1,1,1) form is identically zero** (not merely
`0 · κ₄` form — the bilinear form itself vanishes for
all inputs). -/
theorem F2111SL23_zero (φ ψ : Fin 7 → ℚ) :
    bilinS23 (quadFormOfS23 K2111SL23) φ ψ = 0 := by
  simp [bilinS23, quadFormOfS23, K2111SL23]

/-- (3,1,1,1) form `= 11 · κ₄` form, λ = 11 > 0. -/
theorem F3111SL23_prop (φ ψ : Fin 7 → ℚ) :
    bilinS23 (quadFormOfS23 K3111SL23) φ ψ
      = 11 * bilinS23 F4SL23 φ ψ := by
  apply bilinS23_of_entrywise
  intro a b
  rw [quadFormOfS23, F4SL23, K4totSL23, K3111SL23_prop]
  ring

/-- **(2,2,1,1)-adjacent form is identically zero.** -/
theorem F2211adjSL23_zero (φ ψ : Fin 7 → ℚ) :
    bilinS23 (quadFormOfS23 K2211adjSL23) φ ψ = 0 := by
  simp [bilinS23, quadFormOfS23, K2211adjSL23]

/-- **(2,2,1,1)-opposite form is identically zero.** -/
theorem F2211oppSL23_zero (φ ψ : Fin 7 → ℚ) :
    bilinS23 (quadFormOfS23 K2211oppSL23) φ ψ = 0 := by
  simp [bilinS23, quadFormOfS23, K2211oppSL23]

/-- **C6 form `= (432/5) · κ₄` form** — the form-level
multiple: kernel multiple `1/16`, fiber ratio `576²`,
census factor `240`:
`576² / (16 · 240) = 432/5 > 0`. -/
theorem FC6SL23_prop_entry (a b : Fin 7) :
    FC6SL23 a b = (432 / 5) * F4SL23 a b := by
  rw [FC6SL23, F4SL23, K4totSL23, KC6SL23_prop, fibC6SL23_eq,
    fibC6SL23_eq]
  ring

theorem FC6SL23_prop (φ ψ : Fin 7 → ℚ) :
    bilinS23 FC6SL23 φ ψ = (432 / 5) * bilinS23 F4SL23 φ ψ :=
  bilinS23_of_entrywise FC6SL23_prop_entry φ ψ

/-- The seat's form-level multiples, on the face:
`λ(2,1,1,1) = 0`, `λ(3,1,1,1) = 11 > 0`,
`λ(2,2,1,1)-adj = 0`, `λ(2,2,1,1)-opp = 0`,
`λ(C6) = 432/5 > 0`, `λ(Θ) = 0`. The three zero
multiples are the GD-strong killers at this seat. -/
theorem lambdas_SL23 :
    (0:ℚ) < 11 ∧ (0:ℚ) < 432 / 5 ∧ ¬ (0:ℚ) < 0 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-! ## Deliverable (2), class channels: GD-iii non-firing -/

/-- The κ₄ bilinear form vanishes on kernel pairs —
immediate from the Gram expansion. -/
theorem bilinS23_F4SL23_of_ker {φ ψ : Fin 7 → ℚ}
    (hφ : L1SL23 φ = 0 ∧ L2SL23 φ = 0)
    (hψ : L1SL23 ψ = 0 ∧ L2SL23 ψ = 0) :
    bilinS23 F4SL23 φ ψ = 0 := by
  rw [bilinS23_F4SL23, hφ.1, hφ.2, hψ.1, hψ.2]
  norm_num

/-- **GD-iii non-firing, (2,1,1,1)**: the form is
identically zero, so its restriction to `ker κ₄^dep`
is exactly zero. -/
theorem restrict_K2111SL23_zero (φ ψ : Fin 7 → ℚ) :
    bilinS23 (quadFormOfS23 K2111SL23) φ ψ = 0 :=
  F2111SL23_zero φ ψ

/-- **GD-iii non-firing, (3,1,1,1)**. -/
theorem restrict_K3111SL23_zero {φ ψ : Fin 7 → ℚ}
    (hφ : inKerSpanSL23 φ) (hψ : inKerSpanSL23 ψ) :
    bilinS23 (quadFormOfS23 K3111SL23) φ ψ = 0 := by
  rw [F3111SL23_prop, bilinS23_F4SL23_of_ker
    (L12_of_inKerSpanSL23 hφ) (L12_of_inKerSpanSL23 hψ)]
  norm_num

/-- **GD-iii non-firing, (2,2,1,1)-adjacent**: the form
is identically zero. -/
theorem restrict_K2211adjSL23_zero (φ ψ : Fin 7 → ℚ) :
    bilinS23 (quadFormOfS23 K2211adjSL23) φ ψ = 0 :=
  F2211adjSL23_zero φ ψ

/-- **GD-iii non-firing, (2,2,1,1)-opposite**: the form
is identically zero. -/
theorem restrict_K2211oppSL23_zero (φ ψ : Fin 7 → ℚ) :
    bilinS23 (quadFormOfS23 K2211oppSL23) φ ψ = 0 :=
  F2211oppSL23_zero φ ψ

/-- **GD-iii non-firing, C6**. -/
theorem restrict_C6SL23_zero {φ ψ : Fin 7 → ℚ}
    (hφ : inKerSpanSL23 φ) (hψ : inKerSpanSL23 ψ) :
    bilinS23 FC6SL23 φ ψ = 0 := by
  rw [FC6SL23_prop, bilinS23_F4SL23_of_ker
    (L12_of_inKerSpanSL23 hφ) (L12_of_inKerSpanSL23 hψ)]
  norm_num

end GDSL23Channels

section GDSL23Theta

/-! ## Θ(2,2,2) at the seat: the identically zero kernel -/

/-- **The Θ(2,2,2) orbit kernel at (SL(2,3), ρ₂′)**:
the script's extraction over the **76** gauge orbits of
`(g₃, g₅)` is **identically zero** (orbit kernel rank
0; run log, Seat 2 Θ section). There is no nonzero Θ
matrix to extract at this seat — the zero kernel IS the
extracted data. -/
def KThetaSL23 : Fin 76 → Fin 76 → ℚ := fun _ _ => 0

/-- The Θ bilinear form on orbit space at this seat. -/
def bilinThetaS23 (ψ ψ' : Fin 76 → ℚ) : ℚ :=
  ∑ p, ∑ q, ψ p * KThetaSL23 p q * ψ' q

/-- The Θ form is identically zero at this seat. -/
theorem bilinThetaS23_zero (ψ ψ' : Fin 76 → ℚ) :
    bilinThetaS23 ψ ψ' = 0 := by
  simp [bilinThetaS23, KThetaSL23]

/-- The effective **class-space kernel** of Θ under a
single class variable `tv : orbits → classes`: the
orbit kernel aggregated over the fibers of `tv`. -/
def thetaClassKernelSL23 (tv : Fin 76 → Fin 7) (a b : Fin 7) : ℚ :=
  ∑ p ∈ Finset.univ.filter (fun p => tv p = a),
    ∑ q ∈ Finset.univ.filter (fun q => tv q = b), KThetaSL23 p q

/-- **Θ's class-space form is identically zero** under
every single-variable reading (deliverable 3). -/
theorem thetaClassKernelSL23_zero (tv : Fin 76 → Fin 7) (a b : Fin 7) :
    thetaClassKernelSL23 tv a b = 0 := by
  simp [thetaClassKernelSL23, KThetaSL23]

/-- **(Θ-1) at this seat: no escape, trivially.** Under
every single class variable `tv` — in particular each
of the script's six readings `g₃`, `g₅`, `g₃g₅`,
`g₅g₃`, `g₃g₅⁻¹`, `g₃⁻¹g₅` — the Θ kernel factors
through `tv` with effective multiple `λ = 0`: it is the
zero form, so it factors with the zero multiple and
with no positive one. -/
theorem theta_readings_zero_lambda (tv : Fin 76 → Fin 7) (p q : Fin 76) :
    KThetaSL23 p q = 0 * K4SL23 (tv p) (tv q) := by
  simp [KThetaSL23]

/-- **(Θ-2) at this seat**: the pullback of the Θ form
along ANY class variable vanishes identically — in
particular along the three registered 4-cycle readings
(`g₃`, `g₅`, `g₃⁻¹g₅`) — for ALL observables, hence in
particular on `ker κ₄^dep`. GD-iii does not fire via Θ
at this seat. -/
theorem restrict_theta_SL23_zero (tv : Fin 76 → Fin 7)
    (φ ψ : Fin 7 → ℚ) :
    bilinThetaS23 (fun p => φ (tv p)) (fun p => ψ (tv p)) = 0 :=
  bilinThetaS23_zero _ _

/-- **(Θ-2), joint span**: the pullback along the sum
of any three class-variable readings also vanishes
identically. -/
theorem restrict_theta_joint_SL23_zero
    (tv1 tv2 tv3 : Fin 76 → Fin 7) (φ ψ : Fin 7 → ℚ) :
    bilinThetaS23
      (fun p => φ (tv1 p) + φ (tv2 p) + φ (tv3 p))
      (fun p => ψ (tv1 p) + ψ (tv2 p) + ψ (tv3 p)) = 0 :=
  bilinThetaS23_zero _ _

end GDSL23Theta

section GDStrongFalsifiedSL23

/-! ## Deliverable (4): GD-strong falsified at Seat 2

**Identification, on the face (per the pack's fallback,
named here):** the registered `GDStrong5` / `GDStrong6`
of `ThetLogos.GramDominance` quantify over the owned
`LayerLink` forms at general `(G, ρ, N)`; they are not
imported here (the import is not cheap, and a finite
seat cannot refute the general statement anyway). What
is falsified below is the **seat-level instance** of
exactly their demand pattern — every channel at this
seat an exact **strictly positive** rational multiple
of this seat's κ₄ form, as bilinear forms on the full
class space — which is the statement the R-a routing
(GD-ii) actually routes on. At Seat 1 the instance died
by Θ escape; here it dies independently, by zero
channels. -/

/-- The seat-level instance of `GDStrong5`: the
order-5 channel (2,1,1,1) is a strictly positive
multiple of the seat's κ₄ form. -/
def GDStrong5SeatSL23 : Prop :=
  ∃ lam : ℚ, 0 < lam ∧ ∀ φ ψ : Fin 7 → ℚ,
    bilinS23 (quadFormOfS23 K2111SL23) φ ψ
      = lam * bilinS23 F4SL23 φ ψ

/-- The seat-level instance of `GDStrong6`: each
order-6 channel — (3,1,1,1), (2,2,1,1)-adjacent,
(2,2,1,1)-opposite, C6 (the seat splits the registered
(2,2,1,1) channel into its adjacent/opposite parts) —
is a strictly positive multiple of the seat's κ₄ form. -/
def GDStrong6SeatSL23 : Prop :=
  (∃ lam : ℚ, 0 < lam ∧ ∀ φ ψ : Fin 7 → ℚ,
    bilinS23 (quadFormOfS23 K3111SL23) φ ψ
      = lam * bilinS23 F4SL23 φ ψ)
  ∧ (∃ lam : ℚ, 0 < lam ∧ ∀ φ ψ : Fin 7 → ℚ,
    bilinS23 (quadFormOfS23 K2211adjSL23) φ ψ
      = lam * bilinS23 F4SL23 φ ψ)
  ∧ (∃ lam : ℚ, 0 < lam ∧ ∀ φ ψ : Fin 7 → ℚ,
    bilinS23 (quadFormOfS23 K2211oppSL23) φ ψ
      = lam * bilinS23 F4SL23 φ ψ)
  ∧ (∃ lam : ℚ, 0 < lam ∧ ∀ φ ψ : Fin 7 → ℚ,
    bilinS23 FC6SL23 φ ψ = lam * bilinS23 F4SL23 φ ψ)

/-- A test observable with nonzero κ₄ form:
`e₀`-profile `![1, 0, 0, 0, 0, 0, 0]`. -/
def seatTestVecSL23 : Fin 7 → ℚ := ![1, 0, 0, 0, 0, 0, 0]

theorem L1_testVecSL23 : L1SL23 seatTestVecSL23 = 27648 := by
  rw [L1SL23_eq]
  simp [seatTestVecSL23] <;> norm_num

theorem L2_testVecSL23 : L2SL23 seatTestVecSL23 = 0 := by
  rw [L2SL23_eq]
  simp [seatTestVecSL23]

theorem bilinF4_testVecSL23_ne :
    bilinS23 F4SL23 seatTestVecSL23 seatTestVecSL23 ≠ 0 := by
  rw [bilinS23_F4SL23, L1_testVecSL23, L2_testVecSL23]
  norm_num

/-- **GD-strong (order 5) FALSIFIED at Seat 2**: the
(2,1,1,1) form is identically zero while the κ₄ form
is not, so no strictly positive multiple exists. -/
theorem not_GDStrong5SeatSL23 : ¬ GDStrong5SeatSL23 := by
  rintro ⟨lam, hpos, h⟩
  have hEq := h seatTestVecSL23 seatTestVecSL23
  rw [F2111SL23_zero] at hEq
  have hne : lam * bilinS23 F4SL23 seatTestVecSL23 seatTestVecSL23 ≠ 0 :=
    mul_ne_zero (ne_of_gt hpos) bilinF4_testVecSL23_ne
  exact hne hEq.symm

/-- **GD-strong (order 6) FALSIFIED at Seat 2**: the
(2,2,1,1)-adjacent form is identically zero (the
opposite part and Θ would each serve as well), so its
strictly-positive-multiple demand fails. -/
theorem not_GDStrong6SeatSL23 : ¬ GDStrong6SeatSL23 := by
  rintro ⟨_, ⟨lam, hpos, h⟩, _, _⟩
  have hEq := h seatTestVecSL23 seatTestVecSL23
  rw [F2211adjSL23_zero] at hEq
  have hne : lam * bilinS23 F4SL23 seatTestVecSL23 seatTestVecSL23 ≠ 0 :=
    mul_ne_zero (ne_of_gt hpos) bilinF4_testVecSL23_ne
  exact hne hEq.symm

end GDStrongFalsifiedSL23

section GDSL23Verdict

/-- **GD-iii NON-FIRING at (SL(2,3), ρ₂′), certified.**
For any two observables in `ker κ₄^dep`, every
channel's restriction is exactly zero: the five
class-space channels, and Θ(2,2,2) under every
single-variable reading and every joint three-reading
span (the Θ statements hold for all observables, the
kernel being identically zero). No K-Kn event at this
seat; Route A stands here. -/
theorem gd_iii_no_fire_SL23 {φ ψ : Fin 7 → ℚ}
    (hφ : inKerSpanSL23 φ) (hψ : inKerSpanSL23 ψ) :
    bilinS23 (quadFormOfS23 K2111SL23) φ ψ = 0
    ∧ bilinS23 (quadFormOfS23 K3111SL23) φ ψ = 0
    ∧ bilinS23 (quadFormOfS23 K2211adjSL23) φ ψ = 0
    ∧ bilinS23 (quadFormOfS23 K2211oppSL23) φ ψ = 0
    ∧ bilinS23 FC6SL23 φ ψ = 0
    ∧ (∀ tv : Fin 76 → Fin 7,
        bilinThetaS23 (fun p => φ (tv p)) (fun p => ψ (tv p)) = 0)
    ∧ (∀ tv1 tv2 tv3 : Fin 76 → Fin 7,
        bilinThetaS23
          (fun p => φ (tv1 p) + φ (tv2 p) + φ (tv3 p))
          (fun p => ψ (tv1 p) + ψ (tv2 p) + ψ (tv3 p)) = 0) :=
  ⟨restrict_K2111SL23_zero φ ψ, restrict_K3111SL23_zero hφ hψ,
    restrict_K2211adjSL23_zero φ ψ, restrict_K2211oppSL23_zero φ ψ,
    restrict_C6SL23_zero hφ hψ, fun tv => restrict_theta_SL23_zero tv φ ψ,
    fun tv1 tv2 tv3 => restrict_theta_joint_SL23_zero tv1 tv2 tv3 φ ψ⟩

/-- **GD-PROBE-R-c verdict at Seat 2 (SL(2,3), ρ₂′),
certified.** The κ₄ kernel is the 5-dimensional span
of the extraction's five basis vectors; the nonzero
class-space channels are positive multiples of κ₄
((3,1,1,1) λ = 11, C6 λ = 432/5); the (2,1,1,1),
(2,2,1,1)-adjacent, (2,2,1,1)-opposite and Θ forms are
identically zero; GD-strong is falsified at this seat
independently (zero channels against the
strict-positivity demand); and GD-iii does not fire —
every channel restriction to the kernel is exactly
zero. Together with R-a's Python verdict this certifies
the Seat 2 half of **GD-ii** (GD-global and GD-kernel
untouched; Route A stands). NO CLAIM; parts 0;
dials 0/4. -/
theorem gd_probe_R_c_verdict_SL23 :
    (∀ φ : Fin 7 → ℚ, formS23 F4SL23 φ = 0 ↔ inKerSpanSL23 φ)
    ∧ (∀ φ ψ : Fin 7 → ℚ,
        bilinS23 (quadFormOfS23 K3111SL23) φ ψ
          = 11 * bilinS23 F4SL23 φ ψ)
    ∧ (∀ φ ψ : Fin 7 → ℚ,
        bilinS23 FC6SL23 φ ψ = (432 / 5) * bilinS23 F4SL23 φ ψ)
    ∧ (∀ φ ψ : Fin 7 → ℚ,
        bilinS23 (quadFormOfS23 K2111SL23) φ ψ = 0)
    ∧ (∀ φ ψ : Fin 7 → ℚ,
        bilinS23 (quadFormOfS23 K2211adjSL23) φ ψ = 0)
    ∧ (∀ φ ψ : Fin 7 → ℚ,
        bilinS23 (quadFormOfS23 K2211oppSL23) φ ψ = 0)
    ∧ (∀ p q : Fin 76, KThetaSL23 p q = 0)
    ∧ (∀ (tv : Fin 76 → Fin 7) (a b : Fin 7),
        thetaClassKernelSL23 tv a b = 0)
    ∧ (¬ GDStrong5SeatSL23 ∧ ¬ GDStrong6SeatSL23)
    ∧ (∀ φ ψ : Fin 7 → ℚ, inKerSpanSL23 φ → inKerSpanSL23 ψ →
        bilinS23 (quadFormOfS23 K2111SL23) φ ψ = 0
        ∧ bilinS23 (quadFormOfS23 K3111SL23) φ ψ = 0
        ∧ bilinS23 (quadFormOfS23 K2211adjSL23) φ ψ = 0
        ∧ bilinS23 (quadFormOfS23 K2211oppSL23) φ ψ = 0
        ∧ bilinS23 FC6SL23 φ ψ = 0
        ∧ (∀ tv : Fin 76 → Fin 7,
            bilinThetaS23 (fun p => φ (tv p)) (fun p => ψ (tv p)) = 0)
        ∧ (∀ tv1 tv2 tv3 : Fin 76 → Fin 7,
            bilinThetaS23
              (fun p => φ (tv1 p) + φ (tv2 p) + φ (tv3 p))
              (fun p => ψ (tv1 p) + ψ (tv2 p) + ψ (tv3 p)) = 0)) :=
  ⟨fun φ => K4SL23_form_eq_zero_iff φ, fun φ ψ => F3111SL23_prop φ ψ,
    fun φ ψ => FC6SL23_prop φ ψ, fun φ ψ => F2111SL23_zero φ ψ,
    fun φ ψ => F2211adjSL23_zero φ ψ, fun φ ψ => F2211oppSL23_zero φ ψ,
    fun p q => rfl, fun tv a b => thetaClassKernelSL23_zero tv a b,
    ⟨not_GDStrong5SeatSL23, not_GDStrong6SeatSL23⟩,
    fun φ ψ hφ hψ => gd_iii_no_fire_SL23 hφ hψ⟩

/-- **THE JOINT GD-PROBE-R VERDICT, both re-registered
seats, certified.** Assembling R-b (Seat 1, (F21, ρ₃))
and R-c (Seat 2, (SL(2,3), ρ₂′)):

* **GD-strong is falsified at both seats** — at F21 by
the Θ escape (the Θ orbit kernel is nonzero and a κ₄
multiple under no single-variable reading, R-b's
verdict), and at SL(2,3) independently by zero channels
against the strict-positivity demand (R-c's verdict,
seat-level instances as identified in
`GDStrongFalsifiedSL23`).
* **GD-iii fired at NEITHER seat** — every channel
restriction to `ker κ₄^dep` is exactly zero at both
seats, Θ under all registered readings included: no
K-Kn event anywhere; **Route A stands**.
* **GD-global and GD-kernel are untouched** by this
verdict and stand as the registered targets.

This is the certified GD-ii routing of memo §4.5.
NO CLAIM; parts 0; dials 0/4. -/
theorem gd_probe_R_joint_verdict :
    -- Seat 1 (F21, ρ₃): R-b's certified verdict, in full.
    ((∀ φ : Fin 5 → ℚ, formOf F4F21 φ = 0 ↔ inKerSpanF21 φ)
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
          (fun p => ψ (tvG3F21 p)) = 0))
    -- Seat 1: GD-iii non-firing package, in full.
    ∧ (∀ φ ψ : Fin 5 → ℚ, inKerSpanF21 φ → inKerSpanF21 ψ →
        bilinOf (quadFormOf K2111F21) φ ψ = 0
        ∧ bilinOf (quadFormOf K3111F21) φ ψ = 0
        ∧ bilinOf (quadFormOf K2211adjF21) φ ψ = 0
        ∧ bilinOf (quadFormOf K2211oppF21) φ ψ = 0
        ∧ bilinOf FC6F21 φ ψ = 0
        ∧ bilinThetaF21 (fun p => φ (tvG3F21 p))
            (fun p => ψ (tvG3F21 p)) = 0
        ∧ bilinThetaF21 (fun p => φ (tvG5F21 p))
            (fun p => ψ (tvG5F21 p)) = 0
        ∧ bilinThetaF21 (fun p => φ (tvG3invG5F21 p))
            (fun p => ψ (tvG3invG5F21 p)) = 0
        ∧ bilinThetaF21
            (fun p => φ (tvG3F21 p) + φ (tvG5F21 p)
              + φ (tvG3invG5F21 p))
            (fun p => ψ (tvG3F21 p) + ψ (tvG5F21 p)
              + ψ (tvG3invG5F21 p)) = 0)
    -- Seat 2 (SL(2,3), ρ₂′): R-c's certified verdict, in full.
    ∧ ((∀ φ : Fin 7 → ℚ, formS23 F4SL23 φ = 0 ↔ inKerSpanSL23 φ)
    ∧ (∀ φ ψ : Fin 7 → ℚ,
        bilinS23 (quadFormOfS23 K3111SL23) φ ψ
          = 11 * bilinS23 F4SL23 φ ψ)
    ∧ (∀ φ ψ : Fin 7 → ℚ,
        bilinS23 FC6SL23 φ ψ = (432 / 5) * bilinS23 F4SL23 φ ψ)
    ∧ (∀ φ ψ : Fin 7 → ℚ,
        bilinS23 (quadFormOfS23 K2111SL23) φ ψ = 0)
    ∧ (∀ φ ψ : Fin 7 → ℚ,
        bilinS23 (quadFormOfS23 K2211adjSL23) φ ψ = 0)
    ∧ (∀ φ ψ : Fin 7 → ℚ,
        bilinS23 (quadFormOfS23 K2211oppSL23) φ ψ = 0)
    ∧ (∀ p q : Fin 76, KThetaSL23 p q = 0)
    ∧ (∀ (tv : Fin 76 → Fin 7) (a b : Fin 7),
        thetaClassKernelSL23 tv a b = 0)
    ∧ (¬ GDStrong5SeatSL23 ∧ ¬ GDStrong6SeatSL23)
    ∧ (∀ φ ψ : Fin 7 → ℚ, inKerSpanSL23 φ → inKerSpanSL23 ψ →
        bilinS23 (quadFormOfS23 K2111SL23) φ ψ = 0
        ∧ bilinS23 (quadFormOfS23 K3111SL23) φ ψ = 0
        ∧ bilinS23 (quadFormOfS23 K2211adjSL23) φ ψ = 0
        ∧ bilinS23 (quadFormOfS23 K2211oppSL23) φ ψ = 0
        ∧ bilinS23 FC6SL23 φ ψ = 0
        ∧ (∀ tv : Fin 76 → Fin 7,
            bilinThetaS23 (fun p => φ (tv p)) (fun p => ψ (tv p)) = 0)
        ∧ (∀ tv1 tv2 tv3 : Fin 76 → Fin 7,
            bilinThetaS23
              (fun p => φ (tv1 p) + φ (tv2 p) + φ (tv3 p))
              (fun p => ψ (tv1 p) + ψ (tv2 p) + ψ (tv3 p)) = 0))) :=
  ⟨gd_probe_R_b_verdict_F21,
    fun φ ψ hφ hψ => gd_iii_no_fire_F21 hφ hψ,
    gd_probe_R_c_verdict_SL23⟩

end GDSL23Verdict

end ThetLogos
