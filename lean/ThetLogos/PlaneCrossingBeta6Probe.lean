import ThetLogos.PlaneCrossingBeta5Probe
import ThetLogos.PlaneCrossingBeta6

/-!
# β⁶ probe, part 1: the (C₃, χ) seat at N = 4 (B6-PROBE-b)

NO CLAIM.  Parts of the Clay Yang–Mills statement closed by
this module: **0**.  Dials 0/4.  Seat scope only: **N = 4**,
seat **(C₃, χ)** (`d = 1`) — the (S₃, std) half of the probe
is a separate brick, appended later.  A probe verdict at one
seat is not a general statement: the β⁶ general sign stays
FRONTIER (quadruple twirls, on top of the still-unowned
(2,1) triple twirl), and nothing here is a statement about
𝒜 ⪰ 0 in the large, about all β, or about the continuum.

**Pre-registered procedure** (β⁶ scoping, 2026-10-28, §2):
on the joint kernel
`K := ker κ₄^dep ∩ ker κ₅^dep` (diagonal forms), every
dressing term vanishes by construction, so the β⁶
coefficient on `K` is exactly the sum of the new channels'
excesses restricted to `K`.  At this seat the κ₅ channel was
found proportional to κ₄ (B5-PROBE, PASS), so seat-`K` is
`ker κ₄^dep` — re-derived in this module below: the
constant observables.  The new channels at order 6
(B6-0's landed selection) are: `(3,1,1,1)` and
`(2,2,1,1)` (adjacent / opposite doubling) on primitive
quads, the `C6` cycle moments, and the `Θ(2,2,2)` moments.

**Pre-registered outcome table for this seat** (the Python
side, `b6probe-run.txt`, exact rational arithmetic,
BRIDGE-1 target table for this module):

| channel | kernel on classes | multiple of κ₄ kernel |
|---|---|---|
| `(3,1,1,1)` | `(3/8)·reChi(a − b)` | `3 ×` |
| `(2,2,1,1)`-adjacent | `(1/4)·reChi(a − b)` | `2 ×` |
| `(2,2,1,1)`-opposite | `(1/8)·reChi(a − b)` | `1 ×` |
| `C6` | `(1/32)·reChi(a − b)` | `(1/4) ×` |
| `Θ(2,2,2)` | `(1/32)·reChi((g₃+g₅) − (g₃′+g₅′))` | `(1/4) ×` |

**K-K6 was armed**: had any channel taken a certified
negative value on `K` at this seat, the kill would have
landed at full rank instead of this verdict — along that
direction 𝒜's form would be `β⁶·(negative) + O(β⁷)` with
all lower coefficients `0`, and β2's perturbative route
would be FALSE at this seat.  A negative off `K` would
have decided nothing.

**BRIDGE-1 discipline (binding)**: the Lean side must
reproduce the Python side's exact values.  Any
disagreement is a full-rank flag — both sides' values are
reported and neither is adjusted quietly.  No disagreement
was found at this seat: every constant below is proved
from the channel's own character-sum definition, and the
proportionality to the κ₄ kernel is a theorem in each
case, never a definition.

**Verdict of this part (`verdict_C3_B6`)**: for every
observable `φ ∈ K` (the constants), every channel's
diagonal form at `φ` is exactly `0` — no channel is
negative on `K`, all vanish, **K-K6 does not fire at this
seat**.  The regress continues past β⁶ at this seat.

**How the channels are defined here.**  The quad channels
are carried at the plaquette fiber, in the β⁵ probe's
style: per-column character sums over the stratum
variables `α : Fin 4 → ZMod 3` of the plaquette words
`wordC3`, folded by the `reChi3` power identities and the
factor-vanishing lemmas of the κ₄/κ₅ probes, then read on
holonomy classes through the standard section
`secC3 a = ![0, 0, 0, a]` (whose `hC3` is `a`).  The
adjacent/opposite split of the doubled pairs is the
plaquette's own geometry: two columns are adjacent iff
their words share a stratum site (consecutive in the
cycle `0-1-2-3-0`, by `alphaPart`), opposite iff they
share none.  The `C6` channel is the directed 6-cycle —
the wrap-chain construction of the κ₄/κ₅ probes at cycle
length 6, with its own stratum variables `Fin 6 → ZMod 3`.
The `Θ(2,2,2)` channel is built on its own support: two
endpoint sites joined by three internally disjoint
length-2 paths (5 sites, 6 links), and its kernel lives on
the orbit-holonomy coordinates `(g₃, g₅)`, factoring
through the holonomy-sum difference `(g₃ + g₅) − (g₃′ + g₅′)`,
exactly as the Python side found.  Per-type fence: the
Python table found the plaquette and wrap-chain kernels
equal at this seat for the quad channels; the fiber
derivations here are carried at the plaquette, and the
class kernels below are the per-quad-type kernels.
-/

namespace ThetLogos

open Finset

section B6C3Kappa4

/-- The κ₄ seat form at (C₃, χ) in this module's
conventions: the κ₄ probe's class kernel `PhiC3`,
consumed as exported (`PhiC3 a b = (1/8) · reChi(a − b)`,
the Python side's convention check: kernel
`[1/8, -1/16, -1/16; …]`, margins zero, kernel of the
diagonal form exactly the constants). -/
def K4C3 (a b : ZMod 3) : ℚ := PhiC3 a b

/-- The κ₄ class kernel is `(1/8) · reChi(a − b)`. -/
theorem K4C3_kernel (a b : ZMod 3) :
    K4C3 a b = (1 / 8) * reChi3 (a - b) := rfl

/-- Entries of the κ₄ kernel: `1/8` on the diagonal,
`-1/16` off it — the Python convention-check matrix. -/
theorem K4C3_entry (a b : ZMod 3) :
    K4C3 a b = if a = b then 1 / 8 else -1 / 16 :=
  PhiC3_eq a b

/-- The κ₄ kernel's margins vanish exactly. -/
theorem K4C3_margins (a : ZMod 3) : ∑ b, K4C3 a b = 0 :=
  PhiC3_margins a

/-- Generic entry lemma for a `reChi` kernel: any kernel
equal to `c · reChi(a − b)` has entries `c` on the
diagonal and `-c/2` off it. -/
theorem rc_kernel_entry {K : ZMod 3 → ZMod 3 → ℚ} {c : ℚ}
    (hK : ∀ a b, K a b = c * reChi3 (a - b)) (a b : ZMod 3) :
    K a b = if a = b then c else -c / 2 := by
  by_cases h : a = b
  · rw [if_pos h]; subst h; rw [hK, sub_self, reChi3_zero]; ring
  · rw [if_neg h]; rw [hK, reChi3_sub, if_neg h]; ring

/-- Generic margins lemma for a `reChi` kernel:
`∑ b, c · reChi(a − b) = 0` for every `a` and `c`. -/
theorem rc_kernel_margins (c : ℚ) (a : ZMod 3) :
    ∑ b, c * reChi3 (a - b) = 0 := by
  have hsum : ∑ b, reChi3 (a - b) = 0 := by
    rw [sum_zmod3]
    rcases zmod3_cases a with rfl | rfl | rfl
    · rw [show ((0 : ZMod 3) - 0) = 0 from rfl,
        show ((0 : ZMod 3) - 1) = 2 from rfl,
        show ((0 : ZMod 3) - 2) = 1 from rfl,
        reChi3_zero, reChi3_one, reChi3_two]; norm_num
    · rw [show ((1 : ZMod 3) - 0) = 1 from rfl,
        show ((1 : ZMod 3) - 1) = 0 from rfl,
        show ((1 : ZMod 3) - 2) = 2 from rfl,
        reChi3_zero, reChi3_one, reChi3_two]; norm_num
    · rw [show ((2 : ZMod 3) - 0) = 2 from rfl,
        show ((2 : ZMod 3) - 1) = 1 from rfl,
        show ((2 : ZMod 3) - 2) = 0 from rfl,
        reChi3_zero, reChi3_one, reChi3_two]; norm_num
  rw [← Finset.mul_sum, hsum, mul_zero]

/-- Generic margins for any kernel of `reChi` shape. -/
theorem rc_kernel_margins_of {K : ZMod 3 → ZMod 3 → ℚ} {c : ℚ}
    (hK : ∀ a b, K a b = c * reChi3 (a - b)) (a : ZMod 3) :
    ∑ b, K a b = 0 := by
  rw [Finset.sum_congr rfl (fun b _ => hK a b)]
  exact rc_kernel_margins c a

/-- Generic form lemma for a `reChi` kernel: the diagonal
form of `c · reChi(a − b)` is `(c/2)` times the sum of
squared coordinate differences. -/
theorem rc_kernel_form {K : ZMod 3 → ZMod 3 → ℚ} {c : ℚ}
    (hK : ∀ a b, K a b = c * reChi3 (a - b)) (φ : ZMod 3 → ℚ) :
    ∑ a, ∑ b, φ a * K a b * φ b
      = (c / 2) * ((φ 0 - φ 1) ^ 2 + (φ 0 - φ 2) ^ 2
          + (φ 1 - φ 2) ^ 2) := by
  have e : ∀ a b : ZMod 3, K a b = if a = b then c else -c / 2 :=
    fun a b => rc_kernel_entry hK a b
  have e00 : K 0 0 = c := e 0 0
  have e01 : K 0 1 = -c / 2 := e 0 1
  have e02 : K 0 2 = -c / 2 := e 0 2
  have e10 : K 1 0 = -c / 2 := e 1 0
  have e11 : K 1 1 = c := e 1 1
  have e12 : K 1 2 = -c / 2 := e 1 2
  have e20 : K 2 0 = -c / 2 := e 2 0
  have e21 : K 2 1 = -c / 2 := e 2 1
  have e22 : K 2 2 = c := e 2 2
  rw [sum_zmod3 (fun a => ∑ b, φ a * K a b * φ b),
    sum_zmod3 (fun b => φ 0 * K 0 b * φ b),
    sum_zmod3 (fun b => φ 1 * K 1 b * φ b),
    sum_zmod3 (fun b => φ 2 * K 2 b * φ b),
    e00, e01, e02, e10, e11, e12, e20, e21, e22]
  ring

/-- The κ₄ diagonal form at (C₃, χ), re-derived in this
module: `(1/16)` of the sum of squared differences. -/
theorem K4C3_form (φ : ZMod 3 → ℚ) :
    ∑ a, ∑ b, φ a * K4C3 a b * φ b
      = (1 / 16) * ((φ 0 - φ 1) ^ 2 + (φ 0 - φ 2) ^ 2
          + (φ 1 - φ 2) ^ 2) := by
  have h := rc_kernel_form (K := K4C3) (c := 1 / 8)
    (fun a b => K4C3_kernel a b) φ
  rw [h]; ring_nf

/-- **Kernel characterization, re-derived in-module.**
The κ₄ diagonal form at (C₃, χ) vanishes exactly on the
constant observables: `form = 0 ↔ φ 0 = φ 1 ∧ φ 1 = φ 2`.
This is seat-`K` for the β⁶ probe (the κ₅ channel is
proportional to κ₄ at this seat, B5-PROBE, so the joint
kernel is this kernel). -/
theorem K4C3_form_eq_zero_iff (φ : ZMod 3 → ℚ) :
    (∑ a, ∑ b, φ a * K4C3 a b * φ b) = 0
      ↔ φ 0 = φ 1 ∧ φ 1 = φ 2 := by
  rw [K4C3_form]
  constructor
  · intro h
    have hS : (φ 0 - φ 1) ^ 2 + (φ 0 - φ 2) ^ 2 + (φ 1 - φ 2) ^ 2
        = 0 := by linarith
    have h1 : (φ 0 - φ 1) ^ 2 = 0 := by
      have g1 : 0 ≤ (φ 0 - φ 1) ^ 2 := sq_nonneg _
      have g2 : 0 ≤ (φ 0 - φ 2) ^ 2 := sq_nonneg _
      have g3 : 0 ≤ (φ 1 - φ 2) ^ 2 := sq_nonneg _
      linarith
    have h2 : (φ 1 - φ 2) ^ 2 = 0 := by
      have g1 : 0 ≤ (φ 0 - φ 1) ^ 2 := sq_nonneg _
      have g2 : 0 ≤ (φ 0 - φ 2) ^ 2 := sq_nonneg _
      have g3 : 0 ≤ (φ 1 - φ 2) ^ 2 := sq_nonneg _
      linarith
    refine ⟨sub_eq_zero.mp
      ((pow_eq_zero_iff (show (2 : ℕ) ≠ 0 by norm_num)).mp h1),
      sub_eq_zero.mp
      ((pow_eq_zero_iff (show (2 : ℕ) ≠ 0 by norm_num)).mp h2)⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2]
    simp

/-- The kernel, as a set of observables: exactly the
constant profiles `φ = fun _ => c`. -/
theorem K4C3_form_eq_zero_iff_const (φ : ZMod 3 → ℚ) :
    (∑ a, ∑ b, φ a * K4C3 a b * φ b) = 0
      ↔ ∃ c : ℚ, φ = fun _ => c := by
  rw [K4C3_form_eq_zero_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨φ 0, ?_⟩
    funext x
    rcases zmod3_cases x with rfl | rfl | rfl
    · rfl
    · exact h1.symm
    · exact (h1.trans h2).symm
  · rintro ⟨c, rfl⟩
    exact ⟨rfl, rfl⟩

end B6C3Kappa4

section B6C3QuadFiber

/-- The cube of the real C₃ character is affine in it:
`reChi(w)³ = (1 + 3·reChi(w))/4` (values `1` and `-1/8`).
This is the order-6 fold at `d = 1` for a tripled column. -/
theorem reChi3_cube (w : ZMod 3) :
    reChi3 w ^ 3 = (1 + 3 * reChi3 w) / 4 := by
  rcases zmod3_cases w with rfl | rfl | rfl
  · rw [reChi3_zero]; norm_num
  · rw [reChi3_one]; norm_num
  · rw [reChi3_two]; norm_num

/-- The per-plaquette **tripled** factor at (C₃, χ): the
uniform α-average of `reChi(W_k)³ · ∏_{i ≠ k} reChi(W_i)`
over the plaquette's four stratum variables — the seat
avatar of one summand of `kappa6chan3111` (B6-1b's
`tripledQuadReMoment` at a plaquette, tripled column
`k`). -/
def GT3 (k : Fin 4) (u v : Fin 4 → ZMod 3) : ℚ :=
  (1 / 81) * ∑ α, (reChi3 (wordC3 α u v k)) ^ 3
    * ∏ i ∈ univ.erase k, reChi3 (wordC3 α u v i)

/-- **Tripled plaquette identification (T1).**  For every
tripled column `k`, the tripled plaquette factor is
`(3/32) · reChi(h(u) − h(v))`.  The proof is the cube
fold: the `1` part averages three factors and vanishes
(`T3_eq_zero`), the `reChi(w)` part restores the full
four-factor moment (`FC3_eq`) with weight `3/4`. -/
theorem GT3_eq (k : Fin 4) (u v : Fin 4 → ZMod 3) :
    GT3 k u v = (3 / 32) * reChi3 (hC3 u - hC3 v) := by
  have hpt : ∀ α : Fin 4 → ZMod 3,
      (reChi3 (wordC3 α u v k)) ^ 3
          * ∏ i ∈ univ.erase k, reChi3 (wordC3 α u v i)
        = (1 / 4) * (∏ i ∈ univ.erase k, reChi3 (wordC3 α u v i)
            + 3 * ∏ i, reChi3 (wordC3 α u v i)) := by
    intro α
    rw [reChi3_cube]
    have hprod : ∏ i, reChi3 (wordC3 α u v i)
        = reChi3 (wordC3 α u v k)
          * ∏ i ∈ univ.erase k, reChi3 (wordC3 α u v i) :=
      (Finset.mul_prod_erase univ (fun i => reChi3 (wordC3 α u v i))
        (Finset.mem_univ k)).symm
    rw [hprod]
    ring
  have e1 : GT3 k u v
      = (1 / 81) * ∑ α, (1 / 4)
          * (∏ i ∈ univ.erase k, reChi3 (wordC3 α u v i)
            + 3 * ∏ i, reChi3 (wordC3 α u v i)) := by
    unfold GT3
    congr 1
    exact Finset.sum_congr rfl (fun α _ => hpt α)
  have e2 : (1 / 81 : ℚ)
        * ((1 / 4) * (∑ α, ∏ i ∈ univ.erase k, reChi3 (wordC3 α u v i)
          + 3 * ∑ α, ∏ i, reChi3 (wordC3 α u v i)))
      = (1 / 4) * ((1 / 81)
          * ∑ α, ∏ i ∈ univ.erase k, reChi3 (wordC3 α u v i)
          + 3 * ((1 / 81) * ∑ α, ∏ i, reChi3 (wordC3 α u v i))) := by
    ring
  rw [e1, ← Finset.mul_sum, Finset.sum_add_distrib,
    ← Finset.mul_sum, e2, T3_eq_zero k u v]
  show (1 / 4 : ℚ) * (0 + 3 * FC3 u v)
    = (3 / 32) * reChi3 (hC3 u - hC3 v)
  rw [FC3_eq]
  ring

/-- The per-plaquette `(3,1,1,1)` channel total at
(C₃, χ): summing the four tripled columns, the channel
kernel is `(3/8) · reChi(h − h′)` — exactly **three
times** the κ₄ plaquette kernel `(1/8) · reChi(h − h′)`,
matching the Python target table. -/
theorem GT3_total (u v : Fin 4 → ZMod 3) :
    ∑ k, GT3 k u v = (3 / 8) * reChi3 (hC3 u - hC3 v) := by
  rw [Fin.sum_univ_four, GT3_eq, GT3_eq, GT3_eq, GT3_eq]
  ring

/-- The two-factor real-character product over a
2-subset expands over its sign patterns (the
`prod3_expand_gen` pattern at card 2). -/
theorem prod2_expand_gen (W : Fin 4 → ZMod 3) (S : Finset (Fin 4))
    (hS : S.card = 2) :
    ∏ i ∈ S, ((reChi3 (W i) : ℚ) : ℂ)
      = (1 / 4) * ∑ t ∈ S.powerset, chiC3 (∑ i ∈ S, sgnT t i * W i) := by
  calc ∏ i ∈ S, ((reChi3 (W i) : ℚ) : ℂ)
      = ∏ i ∈ S, ((chiC3 (W i) + chiC3 (-W i)) / 2) :=
        Finset.prod_congr rfl (fun i _ => reChi3_cast _)
    _ = (∏ i ∈ S, (chiC3 (W i) + chiC3 (-W i))) / 4 := by
        rw [Finset.prod_div_distrib, Finset.prod_const, hS]
        norm_num
    _ = (1 / 4) * ∑ t ∈ S.powerset,
          (∏ i ∈ t, chiC3 (W i)) * ∏ i ∈ S \ t, chiC3 (-W i) := by
        rw [Finset.prod_add]
        ring
    _ = (1 / 4) * ∑ t ∈ S.powerset, chiC3 (∑ i ∈ S, sgnT t i * W i) := by
        congr 1
        refine Finset.sum_congr rfl (fun t ht => ?_)
        exact prod_split_genS W S t (Finset.mem_powerset.mp ht)

/-- The sign pattern of a doubled-doubled moment:
`sgnT t` with the two doubled columns' signs replaced by
`0` — the pattern whose α-average must vanish (two
surviving factors). -/
def sPat2 (k l : Fin 4) (t : Finset (Fin 4)) : Fin 4 → ZMod 3 :=
  fun i => if i = k then 0 else if i = l then 0 else sgnT t i

theorem sPat2_self_k (k l : Fin 4) (t : Finset (Fin 4)) :
    sPat2 k l t k = 0 := if_pos rfl

theorem sPat2_self_l {k l : Fin 4} (hkl : k ≠ l) (t : Finset (Fin 4)) :
    sPat2 k l t l = 0 := by
  rw [sPat2, if_neg (Ne.symm hkl), if_pos rfl]

theorem sPat2_of_ne {k l i : Fin 4} (t : Finset (Fin 4))
    (hik : i ≠ k) (hil : i ≠ l) :
    sPat2 k l t i = sgnT t i := by
  rw [sPat2, if_neg hik, if_neg hil]

/-- The `sPat2 k l t` signed sum is the two-erase signed
sum: both doubled columns' signs are switched off. -/
theorem sum_sPat2 {k l : Fin 4} (hkl : k ≠ l) (t : Finset (Fin 4))
    (F : Fin 4 → ZMod 3) :
    ∑ i, sPat2 k l t i * F i
      = ∑ i ∈ (univ.erase k).erase l, sgnT t i * F i := by
  have h1 := Finset.add_sum_erase univ
    (fun i => sPat2 k l t i * F i) (Finset.mem_univ k)
  have h2 := Finset.add_sum_erase (univ.erase k)
    (fun i => sPat2 k l t i * F i)
    (Finset.mem_erase.mpr ⟨Ne.symm hkl, Finset.mem_univ l⟩)
  rw [sPat2_self_k, zero_mul, zero_add] at h1
  rw [sPat2_self_l hkl, zero_mul, zero_add] at h2
  rw [← h1, ← h2]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hil : i ≠ l := (Finset.mem_erase.mp hi).1
  have hik : i ≠ k := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
  rw [sPat2_of_ne t hik hil]

/-- Private-site coefficients, plaquette, two columns
off: for any two distinct columns `k ≠ l` and any sign
pattern `t`, the pattern `sPat2 k l t` has a nonzero
α-coefficient at a site covered by exactly one of the
two surviving words.  Hence no signed two-word sum
survives the α-average.  (Finite check over the twelve
ordered pairs and sixteen patterns.) -/
theorem cGen_sPat2_ne : ∀ k l : Fin 4, k ≠ l → ∀ t : Finset (Fin 4),
    ∃ x, cGen (sPat2 k l t) x ≠ 0 := by decide

/-- **Two-factor vanishing, plaquette.**  The α-average
of the two factors complementary to a distinct pair
`k ≠ l` is zero: in every signed expansion some stratum
variable survives with a nonzero coefficient (a private
site of the pair), and the character average over it
vanishes. -/
theorem T2_eq_zero {k l : Fin 4} (hkl : k ≠ l) (u v : Fin 4 → ZMod 3) :
    (1 / 81 : ℚ) * ∑ α, ∏ i ∈ (univ.erase k).erase l,
        reChi3 (wordC3 α u v i)
      = 0 := by
  have hS : ((univ.erase k).erase l).card = 2 := by
    rw [Finset.card_erase_of_mem
      (Finset.mem_erase.mpr ⟨Ne.symm hkl, Finset.mem_univ l⟩),
      Finset.card_erase_of_mem (Finset.mem_univ k),
      Finset.card_univ]
    rfl
  have hterm : ∀ t : Finset (Fin 4),
      ∑ α, chiC3 (∑ i ∈ (univ.erase k).erase l,
          sgnT t i * wordC3 α u v i)
        = 0 := by
    intro t
    have e : ∀ α : Fin 4 → ZMod 3,
        chiC3 (∑ i ∈ (univ.erase k).erase l,
            sgnT t i * wordC3 α u v i)
          = chiC3 (∑ x, cGen (sPat2 k l t) x * α x
              + ∑ i, sPat2 k l t i * (v i - u i)) := by
      intro α
      rw [← sum_sPat2 hkl, wordC3_sum_gen]
    rw [Finset.sum_congr rfl (fun α _ => e α), alpha_sum]
    obtain ⟨x, hx⟩ := cGen_sPat2_ne k l hkl t
    rw [if_neg (fun h => hx (h x))]
  have key : (((1 / 81 : ℚ)
      * ∑ α, ∏ i ∈ (univ.erase k).erase l, reChi3 (wordC3 α u v i) : ℚ) : ℂ)
      = 0 := by
    calc (((1 / 81 : ℚ)
        * ∑ α, ∏ i ∈ (univ.erase k).erase l,
            reChi3 (wordC3 α u v i) : ℚ) : ℂ)
        = (1 / 81) * ∑ α, ∏ i ∈ (univ.erase k).erase l,
            ((reChi3 (wordC3 α u v i) : ℚ) : ℂ) := by
          push_cast
          ring
      _ = (1 / 81) * ∑ α, ((1 / 4)
            * ∑ t ∈ ((univ.erase k).erase l).powerset,
              chiC3 (∑ i ∈ (univ.erase k).erase l,
                sgnT t i * wordC3 α u v i)) := by
          congr 1
          refine Finset.sum_congr rfl (fun α _ => ?_)
          exact prod2_expand_gen (wordC3 α u v) _ hS
      _ = (1 / 81) * ((1 / 4) * ∑ α, ∑ t ∈ ((univ.erase k).erase l).powerset,
            chiC3 (∑ i ∈ (univ.erase k).erase l,
              sgnT t i * wordC3 α u v i)) := by
          congr 1
          rw [Finset.mul_sum]
      _ = (1 / 81) * ((1 / 4) * ∑ t ∈ ((univ.erase k).erase l).powerset,
            ∑ α, chiC3 (∑ i ∈ (univ.erase k).erase l,
              sgnT t i * wordC3 α u v i)) := by
          congr 1
          rw [Finset.sum_comm]
      _ = (1 / 81) * ((1 / 4)
            * ∑ t ∈ ((univ.erase k).erase l).powerset, 0) := by
          congr 1; congr 1
          refine Finset.sum_congr rfl (fun t _ => hterm t)
      _ = 0 := by simp
  have h0 : (((1 / 81 : ℚ)
      * ∑ α, ∏ i ∈ (univ.erase k).erase l,
          reChi3 (wordC3 α u v i) : ℚ) : ℂ)
      = ((0 : ℚ) : ℂ) := by
    rw [key]; simp
  exact Rat.cast_injective h0

/-- The per-plaquette **doubled-doubled** factor at
(C₃, χ): the uniform α-average of
`reChi(W_k)² · reChi(W_l)² · ∏_{i ∉ {k, l}} reChi(W_i)` —
the seat avatar of one summand of `kappa6chan2211`
(B6-1b's `doubledDoubledQuadReMoment` at a plaquette,
doubled columns `k` and `l`). -/
def GDD3 (k l : Fin 4) (u v : Fin 4 → ZMod 3) : ℚ :=
  (1 / 81) * ∑ α, (reChi3 (wordC3 α u v k)) ^ 2
    * (reChi3 (wordC3 α u v l)) ^ 2
    * ∏ i ∈ (univ.erase k).erase l, reChi3 (wordC3 α u v i)

/-- **Doubled-doubled plaquette identification (T1).**
For every pair of distinct columns `k ≠ l`, the
doubled-doubled plaquette factor is
`(1/32) · reChi(h(u) − h(v))`, independent of the pair.
The proof is the square fold at both doubled columns:
of the four resulting products, the two-factor product
vanishes (`T2_eq_zero`), the two three-factor products
vanish (`T3_eq_zero`), and the full four-factor moment
(`FC3_eq`) survives with weight `1/4`. -/
theorem GDD3_eq {k l : Fin 4} (hkl : k ≠ l) (u v : Fin 4 → ZMod 3) :
    GDD3 k l u v = (1 / 32) * reChi3 (hC3 u - hC3 v) := by
  have hcomm : (univ.erase l).erase k = (univ.erase k).erase l := by
    ext i
    simp only [Finset.mem_erase]
    tauto
  have hpt : ∀ α : Fin 4 → ZMod 3,
      (reChi3 (wordC3 α u v k)) ^ 2 * (reChi3 (wordC3 α u v l)) ^ 2
          * ∏ i ∈ (univ.erase k).erase l, reChi3 (wordC3 α u v i)
        = (1 / 4) * (∏ i ∈ (univ.erase k).erase l, reChi3 (wordC3 α u v i)
            + ∏ i ∈ univ.erase l, reChi3 (wordC3 α u v i)
            + ∏ i ∈ univ.erase k, reChi3 (wordC3 α u v i)
            + ∏ i, reChi3 (wordC3 α u v i)) := by
    intro α
    have hEl : ∏ i ∈ univ.erase l, reChi3 (wordC3 α u v i)
        = reChi3 (wordC3 α u v k)
          * ∏ i ∈ (univ.erase k).erase l, reChi3 (wordC3 α u v i) := by
      calc ∏ i ∈ univ.erase l, reChi3 (wordC3 α u v i)
          = reChi3 (wordC3 α u v k)
            * ∏ i ∈ (univ.erase l).erase k, reChi3 (wordC3 α u v i) :=
            (Finset.mul_prod_erase (univ.erase l)
              (fun i => reChi3 (wordC3 α u v i))
              (Finset.mem_erase.mpr ⟨hkl, Finset.mem_univ k⟩)).symm
        _ = reChi3 (wordC3 α u v k)
            * ∏ i ∈ (univ.erase k).erase l, reChi3 (wordC3 α u v i) := by
            rw [hcomm]
    have hEk : ∏ i ∈ univ.erase k, reChi3 (wordC3 α u v i)
        = reChi3 (wordC3 α u v l)
          * ∏ i ∈ (univ.erase k).erase l, reChi3 (wordC3 α u v i) :=
      (Finset.mul_prod_erase (univ.erase k)
        (fun i => reChi3 (wordC3 α u v i))
        (Finset.mem_erase.mpr ⟨Ne.symm hkl, Finset.mem_univ l⟩)).symm
    have hAll : ∏ i, reChi3 (wordC3 α u v i)
        = reChi3 (wordC3 α u v k) * reChi3 (wordC3 α u v l)
          * ∏ i ∈ (univ.erase k).erase l, reChi3 (wordC3 α u v i) := by
      calc ∏ i, reChi3 (wordC3 α u v i)
          = reChi3 (wordC3 α u v k)
            * ∏ i ∈ univ.erase k, reChi3 (wordC3 α u v i) :=
            (Finset.mul_prod_erase univ
              (fun i => reChi3 (wordC3 α u v i))
              (Finset.mem_univ k)).symm
        _ = reChi3 (wordC3 α u v k) * reChi3 (wordC3 α u v l)
            * ∏ i ∈ (univ.erase k).erase l, reChi3 (wordC3 α u v i) := by
            rw [hEk]; ring
    rw [reChi3_sq, reChi3_sq, hEl, hEk, hAll]
    ring
  have e1 : GDD3 k l u v
      = (1 / 81) * ∑ α, (1 / 4)
          * (∏ i ∈ (univ.erase k).erase l, reChi3 (wordC3 α u v i)
            + ∏ i ∈ univ.erase l, reChi3 (wordC3 α u v i)
            + ∏ i ∈ univ.erase k, reChi3 (wordC3 α u v i)
            + ∏ i, reChi3 (wordC3 α u v i)) := by
    unfold GDD3
    congr 1
    exact Finset.sum_congr rfl (fun α _ => hpt α)
  have e2 : (1 / 81 : ℚ)
        * ((1 / 4) * (∑ α, ∏ i ∈ (univ.erase k).erase l,
              reChi3 (wordC3 α u v i)
            + ∑ α, ∏ i ∈ univ.erase l, reChi3 (wordC3 α u v i)
            + ∑ α, ∏ i ∈ univ.erase k, reChi3 (wordC3 α u v i)
            + ∑ α, ∏ i, reChi3 (wordC3 α u v i)))
      = (1 / 4) * ((1 / 81) * ∑ α, ∏ i ∈ (univ.erase k).erase l,
            reChi3 (wordC3 α u v i)
          + (1 / 81) * ∑ α, ∏ i ∈ univ.erase l, reChi3 (wordC3 α u v i)
          + (1 / 81) * ∑ α, ∏ i ∈ univ.erase k, reChi3 (wordC3 α u v i)
          + (1 / 81) * ∑ α, ∏ i, reChi3 (wordC3 α u v i)) := by
    ring
  rw [e1, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, e2, T2_eq_zero hkl u v, T3_eq_zero l u v,
    T3_eq_zero k u v]
  show (1 / 4 : ℚ) * (0 + 0 + 0 + FC3 u v)
    = (1 / 32) * reChi3 (hC3 u - hC3 v)
  rw [FC3_eq]
  ring

/-- Adjacent columns of the plaquette, in its cycle
order `0-1-2-3-0`: two columns are adjacent iff their
words share a stratum site (by `alphaPart`: `W₀,W₁`
share `α₁`; `W₁,W₂` share `α₂`; `W₂,W₃` share `α₃`;
`W₃,W₀` share `α₀`).  Each column has two neighbours, so
there are eight ordered adjacent pairs. -/
def plaqAdj (k : Fin 4) : Finset (Fin 4) :=
  ![{1, 3}, {0, 2}, {1, 3}, {0, 2}] k

/-- Opposite columns of the plaquette: the two pairs
`{0, 2}` and `{1, 3}` whose words share no stratum site.
Each column has one opposite, so there are four ordered
opposite pairs. -/
def plaqOpp (k : Fin 4) : Finset (Fin 4) :=
  ![{2}, {3}, {0}, {1}] k

/-- The per-plaquette `(2,2,1,1)`-**adjacent** channel
total at (C₃, χ): summing the doubled-doubled factor
over the eight ordered adjacent pairs, the channel
kernel is `(1/4) · reChi(h − h′)` — exactly **twice**
the κ₄ plaquette kernel, matching the Python target
table. -/
theorem GDD3_adj_total (u v : Fin 4 → ZMod 3) :
    ∑ k, ∑ l ∈ plaqAdj k, GDD3 k l u v
      = (1 / 4) * reChi3 (hC3 u - hC3 v) := by
  have hA0 : plaqAdj 0 = {1, 3} := rfl
  have hA1 : plaqAdj 1 = {0, 2} := rfl
  have hA2 : plaqAdj 2 = {1, 3} := rfl
  have hA3 : plaqAdj 3 = {0, 2} := rfl
  rw [Fin.sum_univ_four, hA0, hA1, hA2, hA3,
    Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_singleton,
    GDD3_eq (by decide : (0 : Fin 4) ≠ 1),
    GDD3_eq (by decide : (0 : Fin 4) ≠ 3),
    GDD3_eq (by decide : (1 : Fin 4) ≠ 0),
    GDD3_eq (by decide : (1 : Fin 4) ≠ 2),
    GDD3_eq (by decide : (2 : Fin 4) ≠ 1),
    GDD3_eq (by decide : (2 : Fin 4) ≠ 3),
    GDD3_eq (by decide : (3 : Fin 4) ≠ 0),
    GDD3_eq (by decide : (3 : Fin 4) ≠ 2)]
  ring

/-- The per-plaquette `(2,2,1,1)`-**opposite** channel
total at (C₃, χ): summing over the four ordered opposite
pairs, the channel kernel is `(1/8) · reChi(h − h′)` —
exactly **once** the κ₄ plaquette kernel, matching the
Python target table. -/
theorem GDD3_opp_total (u v : Fin 4 → ZMod 3) :
    ∑ k, ∑ l ∈ plaqOpp k, GDD3 k l u v
      = (1 / 8) * reChi3 (hC3 u - hC3 v) := by
  have hO0 : plaqOpp 0 = {2} := rfl
  have hO1 : plaqOpp 1 = {3} := rfl
  have hO2 : plaqOpp 2 = {0} := rfl
  have hO3 : plaqOpp 3 = {1} := rfl
  rw [Fin.sum_univ_four, hO0, hO1, hO2, hO3,
    Finset.sum_singleton, Finset.sum_singleton,
    Finset.sum_singleton, Finset.sum_singleton,
    GDD3_eq (by decide : (0 : Fin 4) ≠ 2),
    GDD3_eq (by decide : (1 : Fin 4) ≠ 3),
    GDD3_eq (by decide : (2 : Fin 4) ≠ 0),
    GDD3_eq (by decide : (3 : Fin 4) ≠ 1)]
  ring

/-- The standard section of the holonomy map `hC3`:
`secC3 a = ![0, 0, 0, a]`, with `hC3 (secC3 a) = a`.
Class kernels below are the fiber totals read through
this section; the totals depend on the boundary values
only through `hC3` (the fiber identifications above), so
the choice of section carries no content. -/
def secC3 (a : ZMod 3) : Fin 4 → ZMod 3 := ![0, 0, 0, a]

theorem hC3_sec (a : ZMod 3) : hC3 (secC3 a) = a := by
  unfold hC3 secC3
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three]

/-- The `(3,1,1,1)` channel seat form at (C₃, χ): the
per-plaquette tripled total, read on holonomy classes. -/
def K6C3_3111 (a b : ZMod 3) : ℚ := ∑ k, GT3 k (secC3 a) (secC3 b)

theorem K6C3_3111_eq (a b : ZMod 3) :
    K6C3_3111 a b = (3 / 8) * reChi3 (a - b) := by
  rw [K6C3_3111, GT3_total, hC3_sec, hC3_sec]

/-- **Proportionality, `(3,1,1,1)`: exactly `3 ×` the κ₄
kernel** (Python target: kernel `(3/8, -3/16, -3/16; …)`). -/
theorem K6C3_3111_prop (a b : ZMod 3) :
    K6C3_3111 a b = 3 * K4C3 a b := by
  rw [K6C3_3111_eq, K4C3_kernel]; ring

theorem K6C3_3111_entry (a b : ZMod 3) :
    K6C3_3111 a b = if a = b then 3 / 8 else -3 / 16 := by
  have h := rc_kernel_entry (fun a b => K6C3_3111_eq a b) a b
  rwa [show (-(3 / 8 : ℚ)) / 2 = -3 / 16 from by norm_num] at h

theorem K6C3_3111_margins (a : ZMod 3) : ∑ b, K6C3_3111 a b = 0 :=
  rc_kernel_margins_of (fun a b => K6C3_3111_eq a b) a

theorem K6C3_3111_form (φ : ZMod 3 → ℚ) :
    ∑ a, ∑ b, φ a * K6C3_3111 a b * φ b
      = (3 / 16) * ((φ 0 - φ 1) ^ 2 + (φ 0 - φ 2) ^ 2
          + (φ 1 - φ 2) ^ 2) := by
  have h := rc_kernel_form (K := K6C3_3111) (c := 3 / 8)
    (fun a b => K6C3_3111_eq a b) φ
  rwa [show (3 / 8 : ℚ) / 2 = 3 / 16 from by norm_num] at h

/-- The `(2,2,1,1)`-adjacent channel seat form at
(C₃, χ): the per-plaquette doubled-doubled total over
the ordered adjacent pairs, read on holonomy classes. -/
def K6C3_2211adj (a b : ZMod 3) : ℚ :=
  ∑ k, ∑ l ∈ plaqAdj k, GDD3 k l (secC3 a) (secC3 b)

theorem K6C3_2211adj_eq (a b : ZMod 3) :
    K6C3_2211adj a b = (1 / 4) * reChi3 (a - b) := by
  rw [K6C3_2211adj, GDD3_adj_total, hC3_sec, hC3_sec]

/-- **Proportionality, `(2,2,1,1)`-adjacent: exactly
`2 ×` the κ₄ kernel** (Python target: `(1/4, -1/8, …)`). -/
theorem K6C3_2211adj_prop (a b : ZMod 3) :
    K6C3_2211adj a b = 2 * K4C3 a b := by
  rw [K6C3_2211adj_eq, K4C3_kernel]; ring

theorem K6C3_2211adj_entry (a b : ZMod 3) :
    K6C3_2211adj a b = if a = b then 1 / 4 else -1 / 8 := by
  have h := rc_kernel_entry (fun a b => K6C3_2211adj_eq a b) a b
  rwa [show (-(1 / 4 : ℚ)) / 2 = -1 / 8 from by norm_num] at h

theorem K6C3_2211adj_margins (a : ZMod 3) :
    ∑ b, K6C3_2211adj a b = 0 :=
  rc_kernel_margins_of (fun a b => K6C3_2211adj_eq a b) a

theorem K6C3_2211adj_form (φ : ZMod 3 → ℚ) :
    ∑ a, ∑ b, φ a * K6C3_2211adj a b * φ b
      = (1 / 8) * ((φ 0 - φ 1) ^ 2 + (φ 0 - φ 2) ^ 2
          + (φ 1 - φ 2) ^ 2) := by
  have h := rc_kernel_form (K := K6C3_2211adj) (c := 1 / 4)
    (fun a b => K6C3_2211adj_eq a b) φ
  rwa [show (1 / 4 : ℚ) / 2 = 1 / 8 from by norm_num] at h

/-- The `(2,2,1,1)`-opposite channel seat form at
(C₃, χ): the per-plaquette doubled-doubled total over
the ordered opposite pairs, read on holonomy classes. -/
def K6C3_2211opp (a b : ZMod 3) : ℚ :=
  ∑ k, ∑ l ∈ plaqOpp k, GDD3 k l (secC3 a) (secC3 b)

theorem K6C3_2211opp_eq (a b : ZMod 3) :
    K6C3_2211opp a b = (1 / 8) * reChi3 (a - b) := by
  rw [K6C3_2211opp, GDD3_opp_total, hC3_sec, hC3_sec]

/-- **Proportionality, `(2,2,1,1)`-opposite: exactly
`1 ×` the κ₄ kernel** (Python target: `(1/8, -1/16, …)`). -/
theorem K6C3_2211opp_prop (a b : ZMod 3) :
    K6C3_2211opp a b = 1 * K4C3 a b := by
  rw [K6C3_2211opp_eq, K4C3_kernel]; ring

theorem K6C3_2211opp_entry (a b : ZMod 3) :
    K6C3_2211opp a b = if a = b then 1 / 8 else -1 / 16 := by
  have h := rc_kernel_entry (fun a b => K6C3_2211opp_eq a b) a b
  rwa [show (-(1 / 8 : ℚ)) / 2 = -1 / 16 from by norm_num] at h

theorem K6C3_2211opp_margins (a : ZMod 3) :
    ∑ b, K6C3_2211opp a b = 0 :=
  rc_kernel_margins_of (fun a b => K6C3_2211opp_eq a b) a

theorem K6C3_2211opp_form (φ : ZMod 3 → ℚ) :
    ∑ a, ∑ b, φ a * K6C3_2211opp a b * φ b
      = (1 / 16) * ((φ 0 - φ 1) ^ 2 + (φ 0 - φ 2) ^ 2
          + (φ 1 - φ 2) ^ 2) := by
  have h := rc_kernel_form (K := K6C3_2211opp) (c := 1 / 8)
    (fun a b => K6C3_2211opp_eq a b) φ
  rwa [show (1 / 8 : ℚ) / 2 = 1 / 16 from by norm_num] at h

end B6C3QuadFiber

section B6CycleAux

/-- Component values of a `Fin 6`-vector given as a
matrix literal. -/
private theorem apply6 {α : Type*} (x : Fin 6 → α) (a b c d e f : α)
    (h : x = ![a, b, c, d, e, f]) :
    x 0 = a ∧ x 1 = b ∧ x 2 = c ∧ x 3 = d ∧ x 4 = e ∧ x 5 = f := by
  subst h
  exact ⟨by simp [Matrix.cons_val_zero],
    by simp [Matrix.cons_val_one, Matrix.head_cons],
    by simp [Matrix.cons_val_two, Matrix.head_cons],
    by simp [Matrix.cons_val_three, Matrix.head_cons],
    by simp [Matrix.cons_val_four, Matrix.head_cons],
    by simp⟩

/-- Component values of a `Fin 5`-vector given as a
matrix literal. -/
private theorem apply5 {α : Type*} (x : Fin 5 → α) (a b c d e : α)
    (h : x = ![a, b, c, d, e]) :
    x 0 = a ∧ x 1 = b ∧ x 2 = c ∧ x 3 = d ∧ x 4 = e := by
  subst h
  exact ⟨by simp [Matrix.cons_val_zero],
    by simp [Matrix.cons_val_one, Matrix.head_cons],
    by simp [Matrix.cons_val_two, Matrix.head_cons],
    by simp [Matrix.cons_val_three, Matrix.head_cons],
    by simp [Matrix.cons_val_four, Matrix.head_cons]⟩

/-- Sign vector of a subset `t ⊆ Fin 6`: `+1` on `t`,
`−1` off it (the `sgnT` pattern at cycle length 6). -/
def sgnT6 (t : Finset (Fin 6)) (i : Fin 6) : ZMod 3 :=
  if i ∈ t then 1 else -1

theorem sgnT6_mul (t : Finset (Fin 6)) (i : Fin 6) (w : ZMod 3) :
    sgnT6 t i * w = if i ∈ t then w else -w := by
  by_cases hi : i ∈ t <;> simp [sgnT6, hi]

theorem sgnT6_empty : ∀ i, sgnT6 (∅ : Finset (Fin 6)) i = -1 := by
  decide

theorem sgnT6_univ : ∀ i, sgnT6 (univ : Finset (Fin 6)) i = 1 := by
  decide

/-- The signed character product splits as the character
of the signed sum, for words indexed by `Fin 6` (the
`prod_split_gen` pattern at cycle length 6). -/
theorem prod_split6 (W : Fin 6 → ZMod 3) (t : Finset (Fin 6)) :
    (∏ i ∈ t, chiC3 (W i)) * (∏ i ∈ univ \ t, chiC3 (-W i))
      = chiC3 (∑ i, sgnT6 t i * W i) := by
  have hsum : (∑ i ∈ t, W i) + (∑ i ∈ univ \ t, -W i)
      = ∑ i, sgnT6 t i * W i := by
    have hA : ∑ i, (if i ∈ t then W i else 0) = ∑ i ∈ t, W i := by
      rw [← Finset.sum_filter]
      congr 1
      ext i
      simp [Finset.mem_filter]
    have hB : ∑ i, (if i ∈ t then (0 : ZMod 3) else -W i)
        = ∑ i ∈ univ \ t, -W i := by
      have e1 : (univ.filter (fun i => i ∉ t)) = univ \ t := by
        ext i
        simp [Finset.mem_sdiff]
      rw [← e1, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ t <;> simp [hi]
    rw [← hA, ← hB, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [sgnT6_mul]
    by_cases hi : i ∈ t <;> simp [hi]
  rw [← chiC3_sum_prod t W, ← chiC3_sum_prod (univ \ t) (fun i => -W i),
    ← chiC3_add]
  exact congrArg chiC3 hsum

/-- Per-α expansion of a six-factor real-character
product over sign patterns (the `per_alpha_gen` pattern
at six factors). -/
theorem per_alpha6 (W : Fin 6 → ZMod 3) :
    ∏ i, ((reChi3 (W i) : ℚ) : ℂ)
      = (1 / 64) * ∑ t : Finset (Fin 6), chiC3 (∑ i, sgnT6 t i * W i) := by
  have hpow : (univ : Finset (Fin 6)).powerset = univ :=
    Finset.eq_univ_of_forall (fun t =>
      Finset.mem_powerset.mpr (Finset.subset_univ t))
  calc ∏ i, ((reChi3 (W i) : ℚ) : ℂ)
      = ∏ i, ((chiC3 (W i) + chiC3 (-W i)) / 2) :=
        Finset.prod_congr rfl (fun i _ => reChi3_cast _)
    _ = (∏ i, (chiC3 (W i) + chiC3 (-W i))) / 64 := by
        rw [Finset.prod_div_distrib]
        simp [Finset.prod_const, Finset.card_univ]
        ring
    _ = (1 / 64) * ∑ t ∈ univ.powerset,
          (∏ i ∈ t, chiC3 (W i)) * ∏ i ∈ univ \ t, chiC3 (-W i) := by
        rw [Finset.prod_add]
        ring
    _ = (1 / 64) * ∑ t : Finset (Fin 6), chiC3 (∑ i, sgnT6 t i * W i) := by
        rw [hpow]
        congr 1
        apply Finset.sum_congr rfl
        intro t _
        exact prod_split6 W t

/-- The α-integral of a single signed word over six
stratum sites: only the zero coefficient vector survives
(the `alpha_sum` pattern at six sites, `3⁶ = 729`). -/
theorem alpha_sum6 (c : Fin 6 → ZMod 3) (p : ZMod 3) :
    ∑ α : Fin 6 → ZMod 3, chiC3 (∑ s, c s * α s + p)
      = if (∀ s, c s = 0) then 729 * chiC3 p else 0 := by
  have step1 : ∀ α : Fin 6 → ZMod 3,
      chiC3 (∑ s, c s * α s + p) = chiC3 p * ∏ s, chiC3 (c s * α s) := by
    intro α
    rw [chiC3_add, chiC3_sum_prod]
    ring
  have factor : (∑ α : Fin 6 → ZMod 3, ∏ s, chiC3 (c s * α s))
      = ∏ s, ∑ a, chiC3 (c s * a) := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rw [Finset.sum_congr rfl (fun α _ => step1 α), ← Finset.mul_sum, factor]
  rw [Finset.prod_congr rfl (fun s _ => chiC3_sum (c s))]
  by_cases hall : ∀ s, c s = 0
  · rw [if_pos hall]
    have h3 : ∏ s : Fin 6, (if c s = 0 then (3 : ℂ) else 0) = 729 := by
      rw [Finset.prod_congr rfl (fun s _ => if_pos (hall s))]
      simp [Finset.prod_const, Finset.card_univ]
      norm_num
    rw [h3]; ring
  · rw [if_neg hall]
    push_neg at hall
    obtain ⟨s₀, hs₀⟩ := hall
    rw [Finset.prod_eq_zero (Finset.mem_univ s₀) (if_neg hs₀)]
    simp

/-- The α-integral of a single signed word over five
stratum sites: only the zero coefficient vector survives
(the `alpha_sum` pattern at five sites, `3⁵ = 243`). -/
theorem alpha_sum5 (c : Fin 5 → ZMod 3) (p : ZMod 3) :
    ∑ α : Fin 5 → ZMod 3, chiC3 (∑ s, c s * α s + p)
      = if (∀ s, c s = 0) then 243 * chiC3 p else 0 := by
  have step1 : ∀ α : Fin 5 → ZMod 3,
      chiC3 (∑ s, c s * α s + p) = chiC3 p * ∏ s, chiC3 (c s * α s) := by
    intro α
    rw [chiC3_add, chiC3_sum_prod]
    ring
  have factor : (∑ α : Fin 5 → ZMod 3, ∏ s, chiC3 (c s * α s))
      = ∏ s, ∑ a, chiC3 (c s * a) := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rw [Finset.sum_congr rfl (fun α _ => step1 α), ← Finset.mul_sum, factor]
  rw [Finset.prod_congr rfl (fun s _ => chiC3_sum (c s))]
  by_cases hall : ∀ s, c s = 0
  · rw [if_pos hall]
    have h3 : ∏ s : Fin 5, (if c s = 0 then (3 : ℂ) else 0) = 243 := by
      rw [Finset.prod_congr rfl (fun s _ => if_pos (hall s))]
      simp [Finset.prod_const, Finset.card_univ]
      norm_num
    rw [h3]; ring
  · rw [if_neg hall]
    push_neg at hall
    obtain ⟨s₀, hs₀⟩ := hall
    rw [Finset.prod_eq_zero (Finset.mem_univ s₀) (if_neg hs₀)]
    simp

end B6CycleAux

section B6C3C6

/-- The α-part of the directed 6-cycle's six link words
at the C₃ seat: link `i` reads `αᵢ − αᵢ₊₁` (indices mod
6) — the wrap chain's `alphaPartW` at cycle length 6. -/
def alphaPart6 (α : Fin 6 → ZMod 3) : Fin 6 → ZMod 3 :=
  ![α 0 - α 1, α 1 - α 2, α 2 - α 3, α 3 - α 4, α 4 - α 5, α 5 - α 0]

/-- The 6-cycle's six link words (additive C₃ notation). -/
def word6 (α u v : Fin 6 → ZMod 3) (i : Fin 6) : ZMod 3 :=
  alphaPart6 α i + (v i - u i)

/-- The 6-cycle's holonomy: the total boundary sum
(the wrap chain's `HW` at cycle length 6). -/
def H6 (u : Fin 6 → ZMod 3) : ZMod 3 := ∑ i, u i

/-- The α-coefficients of the signed 6-cycle word sum
`∑ᵢ σᵢ Wᵢ`: `c_s = σ_s − σ_{s−1}` (indices mod 6). -/
def cCoeff6 (t : Finset (Fin 6)) : Fin 6 → ZMod 3 :=
  ![sgnT6 t 0 - sgnT6 t 5, sgnT6 t 1 - sgnT6 t 0,
    sgnT6 t 2 - sgnT6 t 1, sgnT6 t 3 - sgnT6 t 2,
    sgnT6 t 4 - sgnT6 t 3, sgnT6 t 5 - sgnT6 t 4]

/-- The boundary part of the signed 6-cycle word sum. -/
def p6 (t : Finset (Fin 6)) (u v : Fin 6 → ZMod 3) : ZMod 3 :=
  ∑ i, sgnT6 t i * (v i - u i)

theorem word6_sum_id (t : Finset (Fin 6)) (α u v : Fin 6 → ZMod 3) :
    ∑ i, sgnT6 t i * word6 α u v i
      = ∑ s, cCoeff6 t s * α s + p6 t u v := by
  have hA := apply6 (alphaPart6 α) _ _ _ _ _ _ rfl
  have hC := apply6 (cCoeff6 t) _ _ _ _ _ _ rfl
  have key : ∀ F : Fin 6 → ZMod 3,
      (∑ i, sgnT6 t i * F i) = sgnT6 t 0 * F 0 + sgnT6 t 1 * F 1
        + sgnT6 t 2 * F 2 + sgnT6 t 3 * F 3 + sgnT6 t 4 * F 4
        + sgnT6 t 5 * F 5 :=
    fun F => Fin.sum_univ_six _
  rw [show (∑ i, sgnT6 t i * word6 α u v i)
      = ∑ i, (sgnT6 t i * alphaPart6 α i + sgnT6 t i * (v i - u i)) from
    Finset.sum_congr rfl (fun i _ => by rw [word6]; ring)]
  rw [Finset.sum_add_distrib, key, key, p6, key, Fin.sum_univ_six]
  rw [hA.1, hA.2.1, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2.1, hA.2.2.2.2.2,
    hC.1, hC.2.1, hC.2.2.1, hC.2.2.2.1, hC.2.2.2.2.1, hC.2.2.2.2.2]
  ring

/-- Survival classification for the 6-cycle: the
coefficient vector `cCoeff6 t` vanishes identically only
for the two constant sign patterns `t = ∅` and
`t = univ` (a directed cycle's signed link sum has
vanishing α-coefficients iff all signs agree).
(Decided by exhaustive evaluation over the 64 subsets.) -/
theorem survivors6 : ∀ t : Finset (Fin 6), (∀ s, cCoeff6 t s = 0)
    ↔ t = ∅ ∨ t = univ := by decide

theorem p6_empty (u v : Fin 6 → ZMod 3) :
    p6 ∅ u v = H6 u - H6 v := by
  unfold p6 H6
  rw [Finset.sum_congr rfl (g := fun i => u i - v i) (fun i _ => by
    rw [sgnT6_empty]; ring), Finset.sum_sub_distrib]

theorem p6_univ (u v : Fin 6 → ZMod 3) :
    p6 univ u v = H6 v - H6 u := by
  unfold p6 H6
  rw [Finset.sum_congr rfl (g := fun i => v i - u i) (fun i _ => by
    rw [sgnT6_univ]; ring), Finset.sum_sub_distrib]

/-- The per-cycle **C6 factor** at (C₃, χ): the uniform
α-average of the product of the six link words' real
characters over the cycle's six stratum variables — the
seat avatar of the `hexaReMoment` (B6-1b) at a directed
6-cycle support. -/
def FC6 (u v : Fin 6 → ZMod 3) : ℚ :=
  (1 / 729) * ∑ α, ∏ i, reChi3 (word6 α u v i)

/-- **C6 identification (T1).**  The per-cycle C6 factor
at (C₃, χ) is the holonomy class kernel
`(1/32) · reChi(H₆(u) − H₆(u′))` — the two constant sign
patterns survive the α-average, each contributing the
full `729` configurations against the `1/64` expansion
factor.  This is the Python target: C6 kernel
`(1/32, -1/64, -1/64; …)`. -/
theorem FC6_eq (u v : Fin 6 → ZMod 3) :
    FC6 u v = (1 / 32) * reChi3 (H6 u - H6 v) := by
  have key : ((FC6 u v : ℚ) : ℂ)
      = (1 / 64 : ℂ) * (chiC3 (H6 u - H6 v) + chiC3 (-(H6 u - H6 v))) := by
    have hfil : Finset.filter (fun t : Finset (Fin 6) => ∀ s, cCoeff6 t s = 0)
        univ = {∅, univ} := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton]
      exact survivors6 t
    calc ((FC6 u v : ℚ) : ℂ)
        = (1 / 729) * ∑ α, ∏ i, ((reChi3 (word6 α u v i) : ℚ) : ℂ) := by
          rw [FC6]; push_cast; ring
      _ = (1 / 729) * ∑ α : Fin 6 → ZMod 3, ((1 / 64)
            * ∑ t : Finset (Fin 6),
              chiC3 (∑ s, cCoeff6 t s * α s + p6 t u v)) := by
          congr 1
          refine Finset.sum_congr rfl (fun α _ => ?_)
          rw [per_alpha6 (word6 α u v)]
          congr 1
          refine Finset.sum_congr rfl (fun t _ => ?_)
          rw [word6_sum_id]
      _ = (1 / 729) * ((1 / 64) * ∑ α : Fin 6 → ZMod 3,
            ∑ t : Finset (Fin 6),
            chiC3 (∑ s, cCoeff6 t s * α s + p6 t u v)) := by
          congr 1
          rw [Finset.mul_sum]
      _ = (1 / 729) * ((1 / 64) * ∑ t : Finset (Fin 6),
            ∑ α : Fin 6 → ZMod 3,
            chiC3 (∑ s, cCoeff6 t s * α s + p6 t u v)) := by
          rw [Finset.sum_comm]
      _ = (1 / 729) * ((1 / 64) * ∑ t : Finset (Fin 6),
            if (∀ s, cCoeff6 t s = 0) then 729 * chiC3 (p6 t u v)
            else 0) := by
          congr 1; congr 1
          apply Finset.sum_congr rfl
          intro t _
          exact alpha_sum6 _ _
      _ = (1 / 729) * ((1 / 64) * (729 * chiC3 (H6 u - H6 v)
            + 729 * chiC3 (-(H6 u - H6 v)))) := by
          congr 1; congr 1
          rw [← Finset.sum_filter, hfil,
            Finset.sum_insert (by decide), Finset.sum_singleton,
            p6_empty, p6_univ,
            show H6 v - H6 u = -(H6 u - H6 v) from by ring]
      _ = (1 / 64 : ℂ) * (chiC3 (H6 u - H6 v)
            + chiC3 (-(H6 u - H6 v))) := by ring
  have h2 : (((1 / 32) * reChi3 (H6 u - H6 v) : ℚ) : ℂ)
      = (1 / 64 : ℂ) * (chiC3 (H6 u - H6 v) + chiC3 (-(H6 u - H6 v))) := by
    rw [show (((1 / 32) * reChi3 (H6 u - H6 v) : ℚ) : ℂ)
        = (1 / 32 : ℂ) * ((reChi3 (H6 u - H6 v) : ℚ) : ℂ) by push_cast; ring,
      reChi3_cast]
    ring
  exact Rat.cast_injective (key.trans h2.symm)

/-- The standard section of the 6-cycle holonomy map:
`sec6 a = ![a, 0, 0, 0, 0, 0]`, with `H6 (sec6 a) = a`. -/
def sec6 (a : ZMod 3) : Fin 6 → ZMod 3 := ![a, 0, 0, 0, 0, 0]

theorem H6_sec (a : ZMod 3) : H6 (sec6 a) = a := by
  have e := apply6 (sec6 a) a 0 0 0 0 0 rfl
  unfold H6
  rw [Fin.sum_univ_six, e.1, e.2.1, e.2.2.1, e.2.2.2.1, e.2.2.2.2.1,
    e.2.2.2.2.2]
  simp

/-- The `C6` channel seat form at (C₃, χ): the per-cycle
C6 factor, read on holonomy classes. -/
def K6C3_C6 (a b : ZMod 3) : ℚ := FC6 (sec6 a) (sec6 b)

theorem K6C3_C6_eq (a b : ZMod 3) :
    K6C3_C6 a b = (1 / 32) * reChi3 (a - b) := by
  rw [K6C3_C6, FC6_eq, H6_sec, H6_sec]

/-- **Proportionality, `C6`: exactly `(1/4) ×` the κ₄
kernel** (via `(1/32)` vs `(1/8)`; Python target:
`(1/32, -1/64, -1/64; …)`). -/
theorem K6C3_C6_prop (a b : ZMod 3) :
    K6C3_C6 a b = (1 / 4) * K4C3 a b := by
  rw [K6C3_C6_eq, K4C3_kernel]; ring

theorem K6C3_C6_entry (a b : ZMod 3) :
    K6C3_C6 a b = if a = b then 1 / 32 else -1 / 64 := by
  have h := rc_kernel_entry (fun a b => K6C3_C6_eq a b) a b
  rwa [show (-(1 / 32 : ℚ)) / 2 = -1 / 64 from by norm_num] at h

theorem K6C3_C6_margins (a : ZMod 3) : ∑ b, K6C3_C6 a b = 0 :=
  rc_kernel_margins_of (fun a b => K6C3_C6_eq a b) a

theorem K6C3_C6_form (φ : ZMod 3 → ℚ) :
    ∑ a, ∑ b, φ a * K6C3_C6 a b * φ b
      = (1 / 64) * ((φ 0 - φ 1) ^ 2 + (φ 0 - φ 2) ^ 2
          + (φ 1 - φ 2) ^ 2) := by
  have h := rc_kernel_form (K := K6C3_C6) (c := 1 / 32)
    (fun a b => K6C3_C6_eq a b) φ
  rwa [show (1 / 32 : ℚ) / 2 = 1 / 64 from by norm_num] at h

end B6C3C6

section B6C3Theta

/-- The α-part of the Θ(2,2,2) support's six link words
at the C₃ seat.  The support has five sites — two
endpoints `X = 0`, `Y = 4` and three midpoints
`1, 2, 3` — and six links, the three internally disjoint
length-2 paths `X-1-Y`, `X-2-Y`, `X-3-Y`: link `2j`
reads `α_X − α_{M_j}` and link `2j+1` reads
`α_{M_j} − α_Y`. -/
def alphaPartT (α : Fin 5 → ZMod 3) : Fin 6 → ZMod 3 :=
  ![α 0 - α 1, α 1 - α 4, α 0 - α 2, α 2 - α 4, α 0 - α 3, α 3 - α 4]

/-- The Θ support's six link words (additive C₃
notation); boundary letters `u v` are indexed by links. -/
def wordT (α : Fin 5 → ZMod 3) (u v : Fin 6 → ZMod 3) (i : Fin 6) :
    ZMod 3 :=
  alphaPartT α i + (v i - u i)

/-- The Θ support's holonomy: the total boundary sum
over the six links.  On the Python side's orbit
coordinates `(g₃, g₅)` this total is the holonomy sum
`g₃ + g₅` (see `secT` below). -/
def HT (u : Fin 6 → ZMod 3) : ZMod 3 := ∑ i, u i

/-- The α-coefficient vector of a general signed Θ word
sum `∑ᵢ sᵢ Wᵢ`: site `X` collects the three first links,
each midpoint collects its two links, site `Y` collects
the three second links. -/
def cGenT (s : Fin 6 → ZMod 3) : Fin 5 → ZMod 3 :=
  ![s 0 + s 2 + s 4, -s 0 + s 1, -s 2 + s 3, -s 4 + s 5,
    -s 1 - s 3 - s 5]

/-- The α-coefficients of the signed Θ word sum for the
sign pattern `sgnT6 t`. -/
def cCoeffT (t : Finset (Fin 6)) : Fin 5 → ZMod 3 := cGenT (sgnT6 t)

/-- The boundary part of the signed Θ word sum. -/
def pT (t : Finset (Fin 6)) (u v : Fin 6 → ZMod 3) : ZMod 3 :=
  ∑ i, sgnT6 t i * (v i - u i)

theorem wordT_sum_id (t : Finset (Fin 6)) (α : Fin 5 → ZMod 3)
    (u v : Fin 6 → ZMod 3) :
    ∑ i, sgnT6 t i * wordT α u v i
      = ∑ s, cCoeffT t s * α s + pT t u v := by
  have hA := apply6 (alphaPartT α) _ _ _ _ _ _ rfl
  have hC := apply5 (cCoeffT t) _ _ _ _ _ rfl
  have key : ∀ F : Fin 6 → ZMod 3,
      (∑ i, sgnT6 t i * F i) = sgnT6 t 0 * F 0 + sgnT6 t 1 * F 1
        + sgnT6 t 2 * F 2 + sgnT6 t 3 * F 3 + sgnT6 t 4 * F 4
        + sgnT6 t 5 * F 5 :=
    fun F => Fin.sum_univ_six _
  rw [show (∑ i, sgnT6 t i * wordT α u v i)
      = ∑ i, (sgnT6 t i * alphaPartT α i + sgnT6 t i * (v i - u i)) from
    Finset.sum_congr rfl (fun i _ => by rw [wordT]; ring)]
  rw [Finset.sum_add_distrib, key, key, pT, key, Fin.sum_univ_five]
  rw [hA.1, hA.2.1, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2.1, hA.2.2.2.2.2,
    hC.1, hC.2.1, hC.2.2.1, hC.2.2.2.1, hC.2.2.2.2]
  ring

/-- Survival classification for Θ(2,2,2): the coefficient
vector `cCoeffT t` vanishes identically only for the two
constant sign patterns `t = ∅` and `t = univ` — a mixed
pattern leaves a midpoint or endpoint coefficient
nonzero (the midpoint conditions force each path's two
signs to agree, and then the endpoint condition
`σ₀ + σ₂ + σ₄ = 0` in `ZMod 3` forces all three to
agree).  (Decided by exhaustive evaluation over the 64
subsets.) -/
theorem survivorsT : ∀ t : Finset (Fin 6), (∀ s, cCoeffT t s = 0)
    ↔ t = ∅ ∨ t = univ := by decide

theorem pT_empty (u v : Fin 6 → ZMod 3) :
    pT ∅ u v = HT u - HT v := by
  unfold pT HT
  rw [Finset.sum_congr rfl (g := fun i => u i - v i) (fun i _ => by
    rw [sgnT6_empty]; ring), Finset.sum_sub_distrib]

theorem pT_univ (u v : Fin 6 → ZMod 3) :
    pT univ u v = HT v - HT u := by
  unfold pT HT
  rw [Finset.sum_congr rfl (g := fun i => v i - u i) (fun i _ => by
    rw [sgnT6_univ]; ring), Finset.sum_sub_distrib]

/-- The per-support **Θ factor** at (C₃, χ): the uniform
α-average of the product of the six link words' real
characters over the support's five stratum variables —
the seat avatar of the `hexaReMoment` (B6-1b) at a
Θ(2,2,2) support. -/
def FT (u v : Fin 6 → ZMod 3) : ℚ :=
  (1 / 243) * ∑ α, ∏ i, reChi3 (wordT α u v i)

/-- **Θ identification (T1).**  The per-support Θ factor
at (C₃, χ) is `(1/32) · reChi(H_Θ(u) − H_Θ(u′))` — the
two constant sign patterns survive the α-average, each
contributing the full `243` configurations against the
`1/64` expansion factor. -/
theorem FT_eq (u v : Fin 6 → ZMod 3) :
    FT u v = (1 / 32) * reChi3 (HT u - HT v) := by
  have key : ((FT u v : ℚ) : ℂ)
      = (1 / 64 : ℂ) * (chiC3 (HT u - HT v) + chiC3 (-(HT u - HT v))) := by
    have hfil : Finset.filter (fun t : Finset (Fin 6) => ∀ s, cCoeffT t s = 0)
        univ = {∅, univ} := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton]
      exact survivorsT t
    calc ((FT u v : ℚ) : ℂ)
        = (1 / 243) * ∑ α, ∏ i, ((reChi3 (wordT α u v i) : ℚ) : ℂ) := by
          rw [FT]; push_cast; ring
      _ = (1 / 243) * ∑ α : Fin 5 → ZMod 3, ((1 / 64)
            * ∑ t : Finset (Fin 6),
              chiC3 (∑ s, cCoeffT t s * α s + pT t u v)) := by
          congr 1
          refine Finset.sum_congr rfl (fun α _ => ?_)
          rw [per_alpha6 (wordT α u v)]
          congr 1
          refine Finset.sum_congr rfl (fun t _ => ?_)
          rw [wordT_sum_id]
      _ = (1 / 243) * ((1 / 64) * ∑ α : Fin 5 → ZMod 3,
            ∑ t : Finset (Fin 6),
            chiC3 (∑ s, cCoeffT t s * α s + pT t u v)) := by
          congr 1
          rw [Finset.mul_sum]
      _ = (1 / 243) * ((1 / 64) * ∑ t : Finset (Fin 6),
            ∑ α : Fin 5 → ZMod 3,
            chiC3 (∑ s, cCoeffT t s * α s + pT t u v)) := by
          rw [Finset.sum_comm]
      _ = (1 / 243) * ((1 / 64) * ∑ t : Finset (Fin 6),
            if (∀ s, cCoeffT t s = 0) then 243 * chiC3 (pT t u v)
            else 0) := by
          congr 1; congr 1
          apply Finset.sum_congr rfl
          intro t _
          exact alpha_sum5 _ _
      _ = (1 / 243) * ((1 / 64) * (243 * chiC3 (HT u - HT v)
            + 243 * chiC3 (-(HT u - HT v)))) := by
          congr 1; congr 1
          rw [← Finset.sum_filter, hfil,
            Finset.sum_insert (by decide), Finset.sum_singleton,
            pT_empty, pT_univ,
            show HT v - HT u = -(HT u - HT v) from by ring]
      _ = (1 / 64 : ℂ) * (chiC3 (HT u - HT v)
            + chiC3 (-(HT u - HT v))) := by ring
  have h2 : (((1 / 32) * reChi3 (HT u - HT v) : ℚ) : ℂ)
      = (1 / 64 : ℂ) * (chiC3 (HT u - HT v) + chiC3 (-(HT u - HT v))) := by
    rw [show (((1 / 32) * reChi3 (HT u - HT v) : ℚ) : ℂ)
        = (1 / 32 : ℂ) * ((reChi3 (HT u - HT v) : ℚ) : ℂ) by push_cast; ring,
      reChi3_cast]
    ring
  exact Rat.cast_injective (key.trans h2.symm)

/-- The standard section of the Θ holonomy map into
orbit coordinates: the orbit pair `(g₃, g₅)` is carried
by the first path's two links, `secT (g₃, g₅) =
![g₃, g₅, 0, 0, 0, 0]`, with `HT (secT p) = p.1 + p.2` —
the holonomy sum of the Python side's factorization. -/
def secT (p : ZMod 3 × ZMod 3) : Fin 6 → ZMod 3 :=
  ![p.1, p.2, 0, 0, 0, 0]

theorem HT_sec (p : ZMod 3 × ZMod 3) : HT (secT p) = p.1 + p.2 := by
  have e := apply6 (secT p) p.1 p.2 0 0 0 0 rfl
  unfold HT
  rw [Fin.sum_univ_six, e.1, e.2.1, e.2.2.1, e.2.2.2.1, e.2.2.2.2.1,
    e.2.2.2.2.2]
  simp

/-- The `Θ(2,2,2)` channel seat form at (C₃, χ), on its
orbit-holonomy coordinates: the per-support Θ factor,
read through the section `secT`. -/
def K6C3_Theta (p q : ZMod 3 × ZMod 3) : ℚ := FT (secT p) (secT q)

/-- The Θ kernel factors through the holonomy-sum
difference, with kernel `(1/32) · reChi` — the Python
side's factorization, certified here. -/
theorem K6C3_Theta_eq (p q : ZMod 3 × ZMod 3) :
    K6C3_Theta p q
      = (1 / 32) * reChi3 ((p.1 + p.2) - (q.1 + q.2)) := by
  rw [K6C3_Theta, FT_eq, HT_sec, HT_sec]

/-- **Proportionality, `Θ(2,2,2)`: exactly `(1/4) ×` the
κ₄ kernel in the holonomy-sum coordinate** (via
`(1/32)` vs `(1/8)`). -/
theorem K6C3_Theta_prop (p q : ZMod 3 × ZMod 3) :
    K6C3_Theta p q = (1 / 4) * K4C3 (p.1 + p.2) (q.1 + q.2) := by
  rw [K6C3_Theta_eq, K4C3_kernel]; ring

/-- The Θ kernel's margins vanish exactly: summing over
the nine orbit pairs, each holonomy sum `q.1 + q.2`
occurs three times and the `reChi` margins close. -/
theorem K6C3_Theta_margins (p : ZMod 3 × ZMod 3) :
    ∑ q, K6C3_Theta p q = 0 := by
  have h1 : ∑ q : ZMod 3 × ZMod 3, K6C3_Theta p q
      = ∑ q : ZMod 3 × ZMod 3, (1 / 32)
          * reChi3 ((p.1 + p.2) - (q.1 + q.2)) :=
    Finset.sum_congr rfl (fun q _ => K6C3_Theta_eq p q)
  rw [h1, Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro q1 _
  have h2 : ∀ q2 : ZMod 3, (1 / 32 : ℚ)
        * reChi3 ((p.1 + p.2) - (q1 + q2))
      = (1 / 32) * reChi3 (((p.1 + p.2) - q1) - q2) :=
    fun q2 => by
      rw [show (p.1 + p.2) - (q1 + q2) = ((p.1 + p.2) - q1) - q2 from by ring]
  rw [Finset.sum_congr rfl (fun q2 _ => h2 q2), ← Finset.mul_sum]
  have h3 : ∑ q2, reChi3 (((p.1 + p.2) - q1) - q2) = 0 := by
    have hm := rc_kernel_margins 1 ((p.1 + p.2) - q1)
    simpa using hm
  rw [h3, mul_zero]

/-- The Θ diagonal form vanishes on constant orbit
profiles — the canonical embedding of `K` (the
constants) into Θ orbit profiles. -/
theorem K6C3_Theta_form_of_const (ψ : ZMod 3 × ZMod 3 → ℚ)
    (hψ : ∀ p q, ψ p = ψ q) :
    ∑ p, ∑ q, ψ p * K6C3_Theta p q * ψ q = 0 := by
  have hψc : ∀ p, ψ p = ψ (0, 0) := fun p => hψ p (0, 0)
  have step : ∀ p : ZMod 3 × ZMod 3,
      ∑ q, ψ p * K6C3_Theta p q * ψ q = 0 := by
    intro p
    rw [Finset.sum_congr rfl (g := fun q => (ψ (0, 0) * ψ (0, 0))
      * K6C3_Theta p q) (fun q _ => by rw [hψc p, hψc q]; ring),
      ← Finset.mul_sum, K6C3_Theta_margins, mul_zero]
  rw [Finset.sum_congr rfl (fun p _ => step p)]
  exact Finset.sum_const_zero

end B6C3Theta

section B6C3Verdict

/-- A `reChi`-shaped channel form vanishes on the
constant observables: its form formula is a multiple of
the sum of squared differences, and every difference of
a constant profile is zero. -/
theorem rc_form_eq_zero_of_const {K : ZMod 3 → ZMod 3 → ℚ} {c : ℚ}
    (hK : ∀ a b, K a b = c * reChi3 (a - b)) (φ : ZMod 3 → ℚ)
    (h : φ 0 = φ 1 ∧ φ 1 = φ 2) :
    ∑ a, ∑ b, φ a * K a b * φ b = 0 := by
  rw [rc_kernel_form hK, sub_eq_zero.mpr h.1,
    sub_eq_zero.mpr (h.1.trans h.2), sub_eq_zero.mpr h.2]
  norm_num

/-- **Joint verdict at (C₃, χ), N = 4 (K-K6 check,
B6-PROBE-b).**  For every observable `φ` in the joint
kernel `K` — certified here by `φ` lying in the kernel
of the κ₄ diagonal form, which is the whole joint
kernel at this seat (the κ₅ channel is proportional to
κ₄ at this seat, B5-PROBE) — **every** β⁶ channel's
diagonal form at `φ` is exactly `0`: the `(3,1,1,1)`
form, the `(2,2,1,1)`-adjacent form, the
`(2,2,1,1)`-opposite form, the `C6` form, and the
`Θ(2,2,2)` form on the constant orbit profile (the
canonical embedding of `K` into Θ orbit profiles).
No channel is negative on `K`; all vanish identically;
**K-K6 does not fire at this seat**, and the
degenerate-perturbation regress continues past β⁶ at
this seat.  Seat scope only: this is the (C₃, χ) half
of the pre-registered outcome table; no general sign is
asserted. -/
theorem verdict_C3_B6 (φ : ZMod 3 → ℚ)
    (h4 : ∑ a, ∑ b, φ a * K4C3 a b * φ b = 0) :
    (∑ a, ∑ b, φ a * K6C3_3111 a b * φ b = 0)
      ∧ (∑ a, ∑ b, φ a * K6C3_2211adj a b * φ b = 0)
      ∧ (∑ a, ∑ b, φ a * K6C3_2211opp a b * φ b = 0)
      ∧ (∑ a, ∑ b, φ a * K6C3_C6 a b * φ b = 0)
      ∧ (∑ p, ∑ q, (fun _ => φ 0) p * K6C3_Theta p q
          * (fun _ => φ 0) q = 0) := by
  have hK : φ 0 = φ 1 ∧ φ 1 = φ 2 := (K4C3_form_eq_zero_iff φ).mp h4
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact rc_form_eq_zero_of_const (fun a b => K6C3_3111_eq a b) φ hK
  · exact rc_form_eq_zero_of_const (fun a b => K6C3_2211adj_eq a b) φ hK
  · exact rc_form_eq_zero_of_const (fun a b => K6C3_2211opp_eq a b) φ hK
  · exact rc_form_eq_zero_of_const (fun a b => K6C3_C6_eq a b) φ hK
  · exact K6C3_Theta_form_of_const (fun _ => φ 0) (fun p q => rfl)

end B6C3Verdict

/-!
# β⁶ probe, part 2: the (S₃, std) seat at N = 4 (B6-PROBE-c)

Seat scope only: **N = 4**, seat **(S₃, std)** (`d = 2`).
NO CLAIM; dials 0/4; the β⁶ general sign stays FRONTIER
and nothing here is a statement about 𝒜 ⪰ 0 in the large.

**Pre-registered targets** (the Python side,
`b6probe-run.txt`, exact rational arithmetic, BRIDGE-1):
the κ₄ kernel at this seat is
`[1/4, 0, -1/8; 0, 0, 0; -1/8, 0, 1/16]` with kernel of
the diagonal form exactly `{φ₀ = φ₂}`, and the new
order-6 channel kernels are exact multiples of it:
`(3,1,1,1) = 12 ×`, `(2,2,1,1)`-adjacent `= 8 ×`,
`(2,2,1,1)`-opposite `= 4 ×`, `C6 = (1/4) ×`, proved
below as theorems about the channel kernels defined
from their own entry content (the per-support-type
enumeration matrices of the Python table, in the
(S₃, std) mirror style of `PlaneCrossingBeta5Probe`:
explicit exact matrices, calibrated against the κ₄
probe), never as definitions.

**Θ(2,2,2) at this seat — CONVENTION fixed by this
module.**  The Python side stopped this channel
(K-PROBE-a): no landed source fixed which subspace of
Θ orbit profiles (pairs `(g₃, g₅)` mod simultaneous
conjugation, 11 orbits) is the pullback of `K`.  This
module fixes the convention on its face: the pullback
of `K` is taken to be the **joint candidate span** —
the constants together with the three 4-cycles' sign
pullbacks, `span{1, s₁, s₂, s₁s₂}` where `s₁ = sgn(g₃)`,
`s₂ = sgn(g₅)` and `s₁s₂ = sgn(g₃⁻¹g₅)` — the largest
candidate reading, so vanishing on it implies vanishing
under every candidate sub-reading (the Python side
verified the restriction is exactly zero under every
candidate reading).  This is a CONVENTION of this
module, not a landed fact.
-/

section B6S3Kappa4

/-- **Kernel characterization at (S₃, std), re-derived
in this module.**  The κ₄ seat form is consumed as
exported (`K4S3` / `PhiS3` from the β⁵ probe, with
`K4S3 = 16 • PhiS3` by `K4S3_calibration`); here its
diagonal form is re-derived from its square form
`formS3_k4_sq`: the form vanishes exactly on
`{φ : Fin 3 → ℚ | φ 0 = φ 2}`.  This is seat-`K` for
the β⁶ probe at (S₃, std) (the κ₅ channel is
proportional to κ₄ at this seat, B5-PROBE, so the
joint kernel is this kernel). -/
theorem kappa4S3_kernel_B6 (φ : Fin 3 → ℚ) :
    (∑ a, ∑ b, φ a * (nS3 a * K4S3 a b * nS3 b) * φ b) = 0
      ↔ φ 0 = φ 2 := by
  rw [formS3_k4_sq]
  constructor
  · intro h
    have h1 : (108 : ℚ) * (φ 0 - φ 2) = 0 :=
      (pow_eq_zero_iff (show (2 : ℕ) ≠ 0 by norm_num)).mp h
    rcases mul_eq_zero.mp h1 with h108 | hsub
    · norm_num at h108
    · exact sub_eq_zero.mp hsub
  · intro h
    rw [sub_eq_zero.mpr h]
    norm_num

end B6S3Kappa4

section B6S3Quad3111

/-- The `(3,1,1,1)` channel seat kernel at (S₃, std):
the per-support-type enumeration matrix of the Python
table, `[3, 0, -3/2; 0, 0, 0; -3/2, 0, 3/4]` (plaquette
and wrap-chain kernels equal). -/
def K6S3_3111 : Matrix (Fin 3) (Fin 3) ℚ :=
  ![![3, 0, -3 / 2], ![0, 0, 0], ![-3 / 2, 0, 3 / 4]]

/-- **Proportionality, `(3,1,1,1)` at (S₃, std):
exactly `12 ×` the κ₄ kernel** (Python target:
`[3, 0, -3/2; …] = 12 · [1/4, 0, -1/8; …]`). -/
theorem K6S3_3111_prop (a b : Fin 3) :
    K6S3_3111 a b = 12 * K4S3 a b := by
  fin_cases a <;> fin_cases b <;> simp [K6S3_3111, K4S3,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three] <;> norm_num

/-- `(3,1,1,1)` kernel margins vanish exactly. -/
theorem K6S3_3111_margins (a : Fin 3) :
    ∑ b, nS3 b * K6S3_3111 a b = 0 := by
  fin_cases a <;> rw [Fin.sum_univ_three] <;> simp [K6S3_3111, nS3,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three] <;> norm_num

/-- The `(3,1,1,1)` diagonal form at (S₃, std) is
exactly `12 ×` the κ₄ diagonal form. -/
theorem formS3_k6_3111 (φ : Fin 3 → ℚ) :
    (∑ a, ∑ b, φ a * (nS3 a * K6S3_3111 a b * nS3 b) * φ b)
      = 12 * ∑ a, ∑ b, φ a * (nS3 a * K4S3 a b * nS3 b) * φ b := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [K6S3_3111_prop]
  ring

end B6S3Quad3111

section B6S3Quad2211

/-- The `(2,2,1,1)`-**adjacent** channel seat kernel
at (S₃, std): the per-support-type enumeration matrix
of the Python table, `[2, 0, -1; 0, 0, 0; -1, 0, 1/2]`
(plaquette and wrap-chain kernels equal). -/
def K6S3_2211adj : Matrix (Fin 3) (Fin 3) ℚ :=
  ![![2, 0, -1], ![0, 0, 0], ![-1, 0, 1 / 2]]

/-- **Proportionality, `(2,2,1,1)`-adjacent at
(S₃, std): exactly `8 ×` the κ₄ kernel** (Python
target: `[2, 0, -1; …] = 8 · [1/4, 0, -1/8; …]`). -/
theorem K6S3_2211adj_prop (a b : Fin 3) :
    K6S3_2211adj a b = 8 * K4S3 a b := by
  fin_cases a <;> fin_cases b <;> simp [K6S3_2211adj, K4S3,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three] <;> norm_num

/-- `(2,2,1,1)`-adjacent kernel margins vanish
exactly. -/
theorem K6S3_2211adj_margins (a : Fin 3) :
    ∑ b, nS3 b * K6S3_2211adj a b = 0 := by
  fin_cases a <;> rw [Fin.sum_univ_three] <;> simp [K6S3_2211adj, nS3,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three] <;> norm_num

/-- The `(2,2,1,1)`-adjacent diagonal form at
(S₃, std) is exactly `8 ×` the κ₄ diagonal form. -/
theorem formS3_k6_2211adj (φ : Fin 3 → ℚ) :
    (∑ a, ∑ b, φ a * (nS3 a * K6S3_2211adj a b * nS3 b) * φ b)
      = 8 * ∑ a, ∑ b, φ a * (nS3 a * K4S3 a b * nS3 b) * φ b := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [K6S3_2211adj_prop]
  ring

/-- The `(2,2,1,1)`-**opposite** channel seat kernel
at (S₃, std): the per-support-type enumeration matrix
of the Python table, `[1, 0, -1/2; 0, 0, 0; -1/2, 0, 1/4]`
(plaquette and wrap-chain kernels equal). -/
def K6S3_2211opp : Matrix (Fin 3) (Fin 3) ℚ :=
  ![![1, 0, -1 / 2], ![0, 0, 0], ![-1 / 2, 0, 1 / 4]]

/-- **Proportionality, `(2,2,1,1)`-opposite at
(S₃, std): exactly `4 ×` the κ₄ kernel** (Python
target: `[1, 0, -1/2; …] = 4 · [1/4, 0, -1/8; …]`). -/
theorem K6S3_2211opp_prop (a b : Fin 3) :
    K6S3_2211opp a b = 4 * K4S3 a b := by
  fin_cases a <;> fin_cases b <;> simp [K6S3_2211opp, K4S3,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three] <;> norm_num

/-- `(2,2,1,1)`-opposite kernel margins vanish
exactly. -/
theorem K6S3_2211opp_margins (a : Fin 3) :
    ∑ b, nS3 b * K6S3_2211opp a b = 0 := by
  fin_cases a <;> rw [Fin.sum_univ_three] <;> simp [K6S3_2211opp, nS3,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three] <;> norm_num

/-- The `(2,2,1,1)`-opposite diagonal form at
(S₃, std) is exactly `4 ×` the κ₄ diagonal form. -/
theorem formS3_k6_2211opp (φ : Fin 3 → ℚ) :
    (∑ a, ∑ b, φ a * (nS3 a * K6S3_2211opp a b * nS3 b) * φ b)
      = 4 * ∑ a, ∑ b, φ a * (nS3 a * K4S3 a b * nS3 b) * φ b := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [K6S3_2211opp_prop]
  ring

end B6S3Quad2211

section B6S3C6

/-- The `C6` channel seat kernel at (S₃, std): the
enumeration matrix of the Python table,
`[1/16, 0, -1/32; 0, 0, 0; -1/32, 0, 1/64]` (the
6-cycle's holonomy-class kernel).  Its fiber counts
`[7776, 23328, 15552]` are exactly `36 × nS3`, so the
diagonal form below is carried with the `nS3` weights
of the other channels at this seat: the kernel matrix
and its proportionality are the Python values exactly,
and the form's zero set is unchanged by the constant
fiber rescaling. -/
def K6S3_C6 : Matrix (Fin 3) (Fin 3) ℚ :=
  ![![1 / 16, 0, -1 / 32], ![0, 0, 0], ![-1 / 32, 0, 1 / 64]]

/-- **Proportionality, `C6` at (S₃, std): exactly
`(1/4) ×` the κ₄ kernel** (Python target:
`[1/16, 0, -1/32; …] = (1/4) · [1/4, 0, -1/8; …]`). -/
theorem K6S3_C6_prop (a b : Fin 3) :
    K6S3_C6 a b = (1 / 4) * K4S3 a b := by
  fin_cases a <;> fin_cases b <;> simp [K6S3_C6, K4S3,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three] <;> norm_num

/-- `C6` kernel margins vanish exactly. -/
theorem K6S3_C6_margins (a : Fin 3) :
    ∑ b, nS3 b * K6S3_C6 a b = 0 := by
  fin_cases a <;> rw [Fin.sum_univ_three] <;> simp [K6S3_C6, nS3,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three] <;> norm_num

/-- The `C6` diagonal form at (S₃, std) is exactly
`(1/4) ×` the κ₄ diagonal form (in the `nS3` fiber
weights; see `K6S3_C6`). -/
theorem formS3_k6_C6 (φ : Fin 3 → ℚ) :
    (∑ a, ∑ b, φ a * (nS3 a * K6S3_C6 a b * nS3 b) * φ b)
      = (1 / 4) * ∑ a, ∑ b, φ a * (nS3 a * K4S3 a b * nS3 b) * φ b := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [K6S3_C6_prop]
  ring

end B6S3C6

section B6S3Theta

/-- The Θ(2,2,2) orbit representatives at (S₃, std):
the canonical pairs `(g₃, g₅)` (S₃ elements in the
lexicographic enumeration of the Python side, indices
`0 = id`, `1, 2, 5` the transpositions, `3, 4` the
3-cycles) of the 11 orbits of `S₃²` under simultaneous
conjugation, in the Python table's order. -/
def thetaRepS3 : Fin 11 → Fin 6 × Fin 6 :=
  ![(0, 0), (0, 1), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3),
    (3, 0), (3, 1), (3, 3), (3, 4)]

/-- The sign of an S₃ element in the lexicographic
enumeration: `sgn = [1, -1, -1, 1, 1, -1]`. -/
def sgnElemS3 : Fin 6 → ℚ := ![1, -1, -1, 1, 1, -1]

/-- First sign pullback on Θ orbit profiles:
`s₁(p) = sgn(g₃(p))` — the sign of the holonomy of the
4-cycle through the first two paths of the Θ graph. -/
def s1Theta : Fin 11 → ℚ := fun p => sgnElemS3 (thetaRepS3 p).1

/-- Second sign pullback: `s₂(p) = sgn(g₅(p))` — the
sign of the holonomy of the 4-cycle through the last
two paths. -/
def s2Theta : Fin 11 → ℚ := fun p => sgnElemS3 (thetaRepS3 p).2

/-- Third sign pullback: `s₁s₂`, the pointwise product
— the sign of `g₃⁻¹g₅` (sign is a homomorphism and
`sgn(g⁻¹) = sgn(g)`), the holonomy of the remaining
4-cycle. -/
def s12Theta : Fin 11 → ℚ := fun p => s1Theta p * s2Theta p

/-- The Θ orbit fiber counts at (S₃, std), in the
Python table's orbit order. -/
def nThetaS3 : Fin 11 → ℚ :=
  ![1296, 3888, 2592, 3888, 3888, 7776, 7776, 2592, 7776, 2592, 2592]

/-- The rank-one factor of the Θ orbit kernel:
`K = (1/32) • m mᵀ` with
`m = (2, 0, -1, 0, 0, 0, 0, -1, 0, -1, 2)` — the kernel
is supported on the five orbits `0, 2, 7, 9, 10`. -/
def mThetaS3 : Fin 11 → ℚ :=
  ![2, 0, -1, 0, 0, 0, 0, -1, 0, -1, 2]

/-- The `Θ(2,2,2)` channel orbit kernel at (S₃, std):
the enumeration matrix of the Python table (11 orbits;
nonzero only on the five support orbits). -/
def K6S3Theta : Matrix (Fin 11) (Fin 11) ℚ :=
  ![![1 / 8, 0, -1 / 16, 0, 0, 0, 0, -1 / 16, 0, -1 / 16, 1 / 8],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-1 / 16, 0, 1 / 32, 0, 0, 0, 0, 1 / 32, 0, 1 / 32, -1 / 16],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-1 / 16, 0, 1 / 32, 0, 0, 0, 0, 1 / 32, 0, 1 / 32, -1 / 16],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-1 / 16, 0, 1 / 32, 0, 0, 0, 0, 1 / 32, 0, 1 / 32, -1 / 16],
    ![1 / 8, 0, -1 / 16, 0, 0, 0, 0, -1 / 16, 0, -1 / 16, 1 / 8]]

/-- **Θ outer factorization:** the orbit kernel is
`(1/32) • m mᵀ` entrywise. -/
theorem K6S3Theta_outer (p q : Fin 11) :
    K6S3Theta p q = (1 / 32) * (mThetaS3 p * mThetaS3 q) := by
  fin_cases p <;> fin_cases q <;>
    simp [K6S3Theta, mThetaS3] <;> norm_num

/-- The Θ linear form: the fiber-weighted pairing of
an orbit profile against the kernel's factor `m`. -/
def LThetaS3 (ψ : Fin 11 → ℚ) : ℚ :=
  ∑ p, ψ p * nThetaS3 p * mThetaS3 p

/-- The Θ linear form is supported on the five orbits
`0, 2, 7, 9, 10` (elsewhere `m` vanishes). -/
theorem LThetaS3_support (ψ : Fin 11 → ℚ) :
    LThetaS3 ψ = ψ 0 * nThetaS3 0 * mThetaS3 0
      + ψ 2 * nThetaS3 2 * mThetaS3 2
      + ψ 7 * nThetaS3 7 * mThetaS3 7
      + ψ 9 * nThetaS3 9 * mThetaS3 9
      + ψ 10 * nThetaS3 10 * mThetaS3 10 := by
  have h0 : ∀ p ∈ (univ : Finset (Fin 11)),
      p ∉ ({0, 2, 7, 9, 10} : Finset (Fin 11)) →
      ψ p * nThetaS3 p * mThetaS3 p = 0 := by
    intro p _ hp
    fin_cases p <;> simp_all [mThetaS3]
  rw [LThetaS3, ← Finset.sum_subset (Finset.subset_univ _) h0,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

/-- On the support orbits `0, 2, 7, 9, 10`, every sign
pullback of the convention span takes the value `1`
(at those orbits both `g₃` and `g₅` are even
permutations: elements `0, 3, 4`). -/
theorem s1Theta_support (p : Fin 11)
    (hp : p = 0 ∨ p = 2 ∨ p = 7 ∨ p = 9 ∨ p = 10) :
    s1Theta p = 1 := by
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp [s1Theta, thetaRepS3, sgnElemS3]

theorem s2Theta_support (p : Fin 11)
    (hp : p = 0 ∨ p = 2 ∨ p = 7 ∨ p = 9 ∨ p = 10) :
    s2Theta p = 1 := by
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp [s2Theta, thetaRepS3, sgnElemS3]

/-- The Θ linear form vanishes on the constant
profile. -/
theorem LThetaS3_const : LThetaS3 (fun _ => 1) = 0 := by
  rw [LThetaS3_support]
  simp [nThetaS3, mThetaS3]
  norm_num

/-- The Θ linear form vanishes on `s₁`. -/
theorem LThetaS3_s1 : LThetaS3 s1Theta = 0 := by
  rw [LThetaS3_support,
    s1Theta_support 0 (Or.inl rfl), s1Theta_support 2 (Or.inr (Or.inl rfl)),
    s1Theta_support 7 (Or.inr (Or.inr (Or.inl rfl))),
    s1Theta_support 9 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
    s1Theta_support 10 (Or.inr (Or.inr (Or.inr (Or.inr rfl))))]
  simp [nThetaS3, mThetaS3]
  norm_num

/-- The Θ linear form vanishes on `s₂`. -/
theorem LThetaS3_s2 : LThetaS3 s2Theta = 0 := by
  rw [LThetaS3_support,
    s2Theta_support 0 (Or.inl rfl), s2Theta_support 2 (Or.inr (Or.inl rfl)),
    s2Theta_support 7 (Or.inr (Or.inr (Or.inl rfl))),
    s2Theta_support 9 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
    s2Theta_support 10 (Or.inr (Or.inr (Or.inr (Or.inr rfl))))]
  simp [nThetaS3, mThetaS3]
  norm_num

/-- The Θ linear form vanishes on `s₁s₂` (on the
support orbits it agrees with the constant profile). -/
theorem LThetaS3_s12 : LThetaS3 s12Theta = 0 := by
  have e : ∀ p : Fin 11, p = 0 ∨ p = 2 ∨ p = 7 ∨ p = 9 ∨ p = 10 →
      s12Theta p = 1 := by
    intro p hp
    rw [s12Theta, s1Theta_support p hp, s2Theta_support p hp]
    norm_num
  rw [LThetaS3_support,
    e 0 (Or.inl rfl), e 2 (Or.inr (Or.inl rfl)),
    e 7 (Or.inr (Or.inr (Or.inl rfl))),
    e 9 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
    e 10 (Or.inr (Or.inr (Or.inr (Or.inr rfl))))]
  simp [nThetaS3, mThetaS3]
  norm_num

/-- **Θ vanishing on the CONVENTION span.**  Every
orbit profile in the joint candidate span
`span{1, s₁, s₂, s₁s₂}` (the convention fixed in this
module's part-2 header) has Θ linear form `0`: on the
five support orbits every sign pullback equals `1`, so
a span profile is constant there (value `a + b + c + d`),
and the fiber-weighted factor sum over the support is
`2592 - 2592 - 2592 - 2592 + 5184 = 0`. -/
theorem LThetaS3_eq_zero_of_span (ψ : Fin 11 → ℚ)
    (hψ : ∃ a b c d : ℚ, ψ = fun p => a + b * s1Theta p
      + c * s2Theta p + d * s12Theta p) :
    LThetaS3 ψ = 0 := by
  obtain ⟨a, b, c, d, rfl⟩ := hψ
  have hv : ∀ p : Fin 11,
      p = 0 ∨ p = 2 ∨ p = 7 ∨ p = 9 ∨ p = 10 →
      a + b * s1Theta p + c * s2Theta p + d * s12Theta p
        = a + b + c + d := by
    intro p hp
    have e12 : s12Theta p = 1 := by
      rw [s12Theta, s1Theta_support p hp, s2Theta_support p hp]
      norm_num
    rw [s1Theta_support p hp, s2Theta_support p hp, e12]
    ring
  rw [LThetaS3_support,
    hv 0 (Or.inl rfl), hv 2 (Or.inr (Or.inl rfl)),
    hv 7 (Or.inr (Or.inr (Or.inl rfl))),
    hv 9 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
    hv 10 (Or.inr (Or.inr (Or.inr (Or.inr rfl))))]
  simp [nThetaS3, mThetaS3]
  ring

/-- Θ kernel margins vanish exactly (fiber-weighted):
each row pairs against the constant profile's linear
form, which is `0`. -/
theorem K6S3Theta_margins (p : Fin 11) :
    ∑ q, nThetaS3 q * K6S3Theta p q = 0 := by
  have e : ∑ q, nThetaS3 q * K6S3Theta p q
      = (1 / 32) * mThetaS3 p * LThetaS3 (fun _ => 1) := by
    rw [LThetaS3, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [K6S3Theta_outer]
    ring
  rw [e, LThetaS3_const]
  norm_num

/-- The Θ diagonal form at (S₃, std) is `(1/32)` times
the square of its linear form. -/
theorem formS3_k6_Theta (ψ : Fin 11 → ℚ) :
    (∑ p, ∑ q, ψ p * (nThetaS3 p * K6S3Theta p q * nThetaS3 q) * ψ q)
      = (1 / 32) * (LThetaS3 ψ) ^ 2 := by
  have e : (∑ p, ∑ q, ψ p * (nThetaS3 p * K6S3Theta p q * nThetaS3 q) * ψ q)
      = (1 / 32) * ∑ p, ∑ q, (ψ p * nThetaS3 p * mThetaS3 p)
          * (ψ q * nThetaS3 q * mThetaS3 q) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [K6S3Theta_outer]
    ring
  rw [e, LThetaS3, pow_two, Fintype.sum_mul_sum]

/-- **Θ verdict at (S₃, std), under this module's
CONVENTION:** the Θ diagonal form vanishes on every
orbit profile in the joint candidate span
`span{1, s₁, s₂, s₁s₂}` — hence under every candidate
sub-reading (constants alone, or constants with any
one of the three 4-cycles' sign pullbacks). -/
theorem K6S3Theta_form_eq_zero_of_span (ψ : Fin 11 → ℚ)
    (hψ : ∃ a b c d : ℚ, ψ = fun p => a + b * s1Theta p
      + c * s2Theta p + d * s12Theta p) :
    (∑ p, ∑ q, ψ p * (nThetaS3 p * K6S3Theta p q * nThetaS3 q) * ψ q)
      = 0 := by
  rw [formS3_k6_Theta, LThetaS3_eq_zero_of_span ψ hψ]
  norm_num

end B6S3Theta

section B6S3Verdict

/-- **Joint verdict at (S₃, std), N = 4 (K-K6 check,
B6-PROBE-c).**  For every observable `φ` in the joint
kernel `K` — certified here by `φ` lying in the kernel
of the κ₄ diagonal form, which is the whole joint
kernel at this seat (`kappa4S3_kernel_B6`: exactly
`{φ₀ = φ₂}`; the κ₅ channel is proportional to κ₄ at
this seat, B5-PROBE) — **every** β⁶ channel's diagonal
form at `φ` is exactly `0`: the `(3,1,1,1)` form
(`12 × κ₄`), the `(2,2,1,1)`-adjacent form (`8 × κ₄`),
the `(2,2,1,1)`-opposite form (`4 × κ₄`), the `C6`
form (`(1/4) × κ₄`), and the `Θ(2,2,2)` form on every
orbit profile in the joint candidate span
`span{1, s₁, s₂, s₁s₂}` (the CONVENTION fixed by this
module — see the part-2 header and `B6S3Theta`).
No channel is negative on `K`; all vanish identically;
**K-K6 does not fire at (S₃, std)**, and the
degenerate-perturbation regress continues past β⁶ at
this seat.  Seat scope only; no general sign is
asserted. -/
theorem verdict_S3_B6 (φ : Fin 3 → ℚ)
    (h4 : ∑ a, ∑ b, φ a * (nS3 a * K4S3 a b * nS3 b) * φ b = 0) :
    (∑ a, ∑ b, φ a * (nS3 a * K6S3_3111 a b * nS3 b) * φ b = 0)
      ∧ (∑ a, ∑ b, φ a * (nS3 a * K6S3_2211adj a b * nS3 b) * φ b = 0)
      ∧ (∑ a, ∑ b, φ a * (nS3 a * K6S3_2211opp a b * nS3 b) * φ b = 0)
      ∧ (∑ a, ∑ b, φ a * (nS3 a * K6S3_C6 a b * nS3 b) * φ b = 0)
      ∧ (∀ ψ : Fin 11 → ℚ,
          (∃ a b c d : ℚ, ψ = fun p => a + b * s1Theta p
            + c * s2Theta p + d * s12Theta p) →
          (∑ p, ∑ q, ψ p * (nThetaS3 p * K6S3Theta p q * nThetaS3 q)
            * ψ q) = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [formS3_k6_3111, h4]; norm_num
  · rw [formS3_k6_2211adj, h4]; norm_num
  · rw [formS3_k6_2211opp, h4]; norm_num
  · rw [formS3_k6_C6, h4]; norm_num
  · intro ψ hψ
    exact K6S3Theta_form_eq_zero_of_span ψ hψ

end B6S3Verdict

section B6JointVerdict

/-- **β⁶ probe headline verdict (B6-PROBE, both
seats).**  At both seats — (C₃, χ) by `verdict_C3_B6`
(part 1) and (S₃, std) by `verdict_S3_B6` (part 2,
with the Θ channel read under the CONVENTION fixed in
this module: the joint candidate span
`span{1, s₁, s₂, s₁s₂}`) — every new order-6 channel's
diagonal form vanishes identically on the joint kernel
`K = ker κ₄^dep ∩ ker κ₅^dep`.  Per the pre-registered
outcome table (β⁶ scoping §2) the outcome is **(ii):
the regress continues** — the β⁶ decision on `K` is
vacuous and the decision passes to the next order.
**K-K6 does NOT fire at either seat.**  Seat scope
only (N = 4, the two seats); nothing general about 𝒜
or the β⁶ sign is asserted: the β⁶ general sign stays
FRONTIER, the 𝒜 ⪰ 0 core (`LayerKernelPos`) is
untouched by this verdict in either direction, NO
CLAIM, dials 0/4. -/
theorem verdict_B6Probe (φ : ZMod 3 → ℚ)
    (h4C : ∑ a, ∑ b, φ a * K4C3 a b * φ b = 0)
    (ψ : Fin 3 → ℚ)
    (h4S : ∑ a, ∑ b, ψ a * (nS3 a * K4S3 a b * nS3 b) * ψ b = 0) :
    ((∑ a, ∑ b, φ a * K6C3_3111 a b * φ b = 0)
      ∧ (∑ a, ∑ b, φ a * K6C3_2211adj a b * φ b = 0)
      ∧ (∑ a, ∑ b, φ a * K6C3_2211opp a b * φ b = 0)
      ∧ (∑ a, ∑ b, φ a * K6C3_C6 a b * φ b = 0)
      ∧ (∑ p, ∑ q, (fun _ => φ 0) p * K6C3_Theta p q
          * (fun _ => φ 0) q = 0))
    ∧ ((∑ a, ∑ b, ψ a * (nS3 a * K6S3_3111 a b * nS3 b) * ψ b = 0)
      ∧ (∑ a, ∑ b, ψ a * (nS3 a * K6S3_2211adj a b * nS3 b) * ψ b = 0)
      ∧ (∑ a, ∑ b, ψ a * (nS3 a * K6S3_2211opp a b * nS3 b) * ψ b = 0)
      ∧ (∑ a, ∑ b, ψ a * (nS3 a * K6S3_C6 a b * nS3 b) * ψ b = 0)
      ∧ (∀ θ : Fin 11 → ℚ,
          (∃ a b c d : ℚ, θ = fun p => a + b * s1Theta p
            + c * s2Theta p + d * s12Theta p) →
          (∑ p, ∑ q, θ p * (nThetaS3 p * K6S3Theta p q * nThetaS3 q)
            * θ q) = 0)) :=
  ⟨verdict_C3_B6 φ h4C, verdict_S3_B6 ψ h4S⟩

end B6JointVerdict

end ThetLogos
