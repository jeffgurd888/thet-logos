import ThetLogos.PlaneCrossingBeta6Probe
import ThetLogos.PlaneCrossingBeta7

/-!
# β⁷ probe, part 1: the (C₃, χ) seat at N = 4 (B7-PROBE-b)

NO CLAIM.  Parts of the Clay Yang–Mills statement closed by
this module: **0**.  Dials 0/4.  Seat scope only: **N = 4**,
seat **(C₃, χ)** (`d = 1`) — the (S₃, std) half of the probe
is a separate brick, appended later.  A probe verdict at one
seat is not a general statement: the β⁷ general sign stays
FRONTIER (the general sign mechanism does not transfer from
order 6 — triple twirls and beyond are unowned), and nothing
here is a statement about 𝒜 ⪰ 0 in the large, about all β, or
about the continuum.

**Pre-registered procedure** (β⁷ scoping, 2026-10-29, §2):
on the joint kernel
`K₆ := ker κ₄^dep ∩ ker κ₅^dep ∩ ker κ₆^dep` (diagonal
forms), every dressing term vanishes by construction, so
the β⁷ coefficient on `K₆` is exactly the sum of the new
channels' excesses restricted to `K₆`.  At this seat the κ₅
channel was found proportional to κ₄ (B5-PROBE, PASS) and
every κ₆ channel proportional to κ₄ or factored through it
(B6-PROBE, `verdict_C3_B6`), so seat-`K₆` is `ker κ₄^dep` —
re-derived in this module below (`seatK6_C3`): the constant
observables.  The new channels at order 7 (B7-0's landed
selection, channel definitions in
`ThetLogos.PlaneCrossingBeta7`) are: `(4,1,1,1)`,
`(3,2,1,1)` (adjacent / opposite heavy pair) and
`(2,2,2,1)` on primitive quads, the `(2,1,1,1,1,1)`
doubled moments on `C6` and on `Θ(2,2,2)` supports, and
the `(1⁷)` moment on the `Θ(1,3,3)` book support.

**Excess = raw at this seat.**  Excess formation is B7-2
territory in `PlaneCrossingBeta7` (the module defines the
raw channel sums and no excess, exactly as at B6); the
assembly pattern defines each excess as raw minus its
fully-split baseline, and every order-7 baseline carries a
positive power of `e₁` (`(4,1,1,1)`: `μ₄·e₁³`;
`(3,2,1,1)`: `μ₃·μ₂·e₁²`; `(2,2,2,1)`: `μ₂³·e₁`;
`(2,1,1,1,1,1)`: `μ₂·e₁⁵`; `(1⁷)`: `e₁⁷`).  At this seat
`e₁ = E reChi = 0` exactly (`e1_C3` below), so every
baseline vanishes and every excess equals its raw channel
sum, as at B5/B6.  The raw sums are what is evaluated here.

**Pre-registered outcome table for this seat** (the Python
side, `b7probe-run.txt`, exact rational arithmetic,
registry **BR1-008**, the BRIDGE-1 target table for this
module).  The seat κ₄ kernel is `(1/8)·reChi(a − b)`:

| channel | kernel | multiple of κ₄ kernel |
|---|---|---|
| `(4,1,1,1)` | `(5/16)·reChi(a − b)` | `5/2 ×` |
| `(3,2,1,1)`-adjacent | `(3/8)·reChi(a − b)` | `3 ×` |
| `(3,2,1,1)`-opposite | `(3/16)·reChi(a − b)` | `3/2 ×` |
| `(2,2,2,1)` | `(3/8)·reChi(a − b)` | `3 ×` |
| `(2,1,1,1,1,1)` on `C6` | `(3/32)·reChi(a − b)` | `3/4 ×` |
| `(2,1,1,1,1,1)` on `Θ(2,2,2)` | `(3/32)·reChi((g₃+g₅) − (g₃′+g₅′))` | `3/4 ×` |
| `(1⁷)` on `Θ(1,3,3)` book | `(1/64)·reChi((hₐ+h_b) − (hₐ′+h_b′))` | `1/8 ×` |

**K-K7 was armed**: had any channel taken a certified
negative value on `K₆` at this seat, the kill would have
landed at full rank instead of this verdict — along that
direction 𝒜's form would be `β⁷·(negative) + O(β⁸)` with
all lower coefficients `0`, and β2's perturbative route
would be FALSE at this seat.  A negative off `K₆` would
have decided nothing.

**BRIDGE-1 discipline (binding)**: the Lean side must
reproduce the Python side's exact values (registry
BR1-008).  Any disagreement is a full-rank flag — both
sides' values are reported and neither is adjusted
quietly.  No disagreement was found at this seat: every
constant below is proved from the channel's own
character-sum definition, and the proportionality to the
κ₄ kernel is a theorem in each case, never a definition.

**Verdict of this part (`verdict_C3_B7`)**: for every
observable `φ ∈ K₆` (the constants), every channel's
diagonal form at `φ` is exactly `0` — no channel is
negative on `K₆`, all vanish, **K-K7 does not fire at this
seat**.  The regress continues past β⁷ at this seat.

**Interpretation cap (on the face)**: the multiples in the
table are seat data — exact values of these channel forms
at this one seat — not mechanism evidence.  No mechanism
for the general β⁷ sign is asserted or suggested by the
pattern of multiples, and the β⁷ general sign stays
FRONTIER.

**How the channels are defined here.**  The quad channels
are carried at the plaquette fiber, in the β⁵/β⁶ probes'
style: per-column character sums over the stratum
variables `α : Fin 4 → ZMod 3` of the plaquette words
`wordC3`, folded by the `reChi3` power identities and the
factor-vanishing lemmas of the κ₄/κ₅/κ₆ probes, then read
on holonomy classes through the standard section
`secC3 a = ![0, 0, 0, a]` (whose `hC3` is `a`).  The
adjacent/opposite split of the `(3,2,1,1)` heavy pair is
the plaquette's own geometry (`plaqAdj` / `plaqOpp` of the
β⁶ probe: site-sharing versus disjoint column pairs, the
seat reading of `ColsShareSite` / `ColsDisjointSites`).
The `C6` doubled channel is the directed 6-cycle of the
β⁶ probe with one doubled link; the `Θ(2,2,2)` doubled
channel is built on the β⁶ probe's Θ support with one
doubled link, its kernel factoring through the holonomy
sum `g₃ + g₅`; the `Θ(1,3,3)` book channel is built on
its own support here: two degree-3 sites joined by a
shared link and two internally disjoint length-3 paths
(6 sites, 7 links), its kernel factoring through the
holonomy sum `hₐ + h_b` of its two path holonomies.
Per-type fence: the Python table found the plaquette and
wrap-chain kernels equal at this seat for the quad
channels; the fiber derivations here are carried at the
plaquette, and the class kernels below are the
per-quad-type kernels.
-/

namespace ThetLogos

open Finset

set_option maxRecDepth 16384

section B7SeatK6

/-- The first moment of the real C₃ character vanishes:
`e₁ = (1/3)·∑ reChi = 0` at this seat — the fact behind
the excess-equals-raw identification in the header (every
order-7 fully-split baseline carries a positive power of
`e₁`). -/
theorem e1_C3 : (1 / 3 : ℚ) * ∑ w, reChi3 w = 0 := by
  rw [sum_zmod3, reChi3_zero, reChi3_one, reChi3_two]
  norm_num

/-- Every positive power of the seat `e₁` vanishes, so
every order-7 baseline (each carrying a positive power of
`e₁`) vanishes at this seat. -/
theorem e1_C3_pow {n : ℕ} (hn : 1 ≤ n) :
    ((1 / 3 : ℚ) * ∑ w, reChi3 w) ^ n = 0 := by
  rw [e1_C3]
  exact zero_pow (by omega : n ≠ 0)

/-- **Seat-`K₆` re-derivation at (C₃, χ).**  `K₆` is
`ker κ₄^dep ∩ ker κ₅^dep ∩ ker κ₆^dep` (diagonal forms).
At this seat the κ₅ channel form vanishes on
`ker κ₄^dep` (it is `2 ×` the κ₄ kernel, B5-PROBE: the
`K5C3` form is a multiple of the same sum of squared
differences), and every κ₆ channel form vanishes there
too (`verdict_C3_B6`, consumed as landed).  Hence
seat-`K₆` = `ker κ₄^dep`, which is exactly the constant
observables by `K4C3_form_eq_zero_iff_const`.  This
theorem certifies the κ₅/κ₆ half of that identification
in-module: from `φ ∈ ker κ₄^dep`, the κ₅ form and all
five κ₆ channel forms of `verdict_C3_B6` vanish at `φ`. -/
theorem seatK6_C3 (φ : ZMod 3 → ℚ)
    (h4 : ∑ a, ∑ b, φ a * K4C3 a b * φ b = 0) :
    (∑ a, ∑ b, φ a * K5C3 a b * φ b = 0)
      ∧ (∑ a, ∑ b, φ a * K6C3_3111 a b * φ b = 0)
      ∧ (∑ a, ∑ b, φ a * K6C3_2211adj a b * φ b = 0)
      ∧ (∑ a, ∑ b, φ a * K6C3_2211opp a b * φ b = 0)
      ∧ (∑ a, ∑ b, φ a * K6C3_C6 a b * φ b = 0)
      ∧ (∑ p, ∑ q, (fun _ => φ 0) p * K6C3_Theta p q
          * (fun _ => φ 0) q = 0) := by
  have hK : φ 0 = φ 1 ∧ φ 1 = φ 2 :=
    (K4C3_form_eq_zero_iff φ).mp h4
  refine ⟨?_, verdict_C3_B6 φ h4⟩
  exact rc_form_eq_zero_of_const (K := K5C3) (c := 1 / 4)
    (fun a b => rfl) φ hK

end B7SeatK6

section B7C3Quad4111

/-- The fourth power of the real C₃ character is affine
in it: `reChi(w)⁴ = (3 + 5·reChi(w))/8` (values `1` and
`1/16`).  This is the order-7 fold at `d = 1` for a
quadrupled column. -/
theorem reChi3_pow4 (w : ZMod 3) :
    reChi3 w ^ 4 = (3 + 5 * reChi3 w) / 8 := by
  rcases zmod3_cases w with rfl | rfl | rfl
  · rw [reChi3_zero]; norm_num
  · rw [reChi3_one]; norm_num
  · rw [reChi3_two]; norm_num

/-- The per-plaquette **quadrupled** factor at (C₃, χ):
the uniform α-average of
`reChi(W_k)⁴ · ∏_{i ≠ k} reChi(W_i)` over the plaquette's
four stratum variables — the seat avatar of one summand
of `kappa7chan4111` (B7-1b's `quadrupledQuadReMoment` at
a plaquette, quadrupled column `k`). -/
def GT4 (k : Fin 4) (u v : Fin 4 → ZMod 3) : ℚ :=
  (1 / 81) * ∑ α, (reChi3 (wordC3 α u v k)) ^ 4
    * ∏ i ∈ univ.erase k, reChi3 (wordC3 α u v i)

/-- **Quadrupled plaquette identification (T1).**  For
every quadrupled column `k`, the quadrupled plaquette
factor is `(5/64) · reChi(h(u) − h(v))`.  The proof is
the fourth-power fold: the `3` part averages three
factors and vanishes (`T3_eq_zero`), the `reChi(w)` part
restores the full four-factor moment (`FC3_eq`) with
weight `5/8`. -/
theorem GT4_eq (k : Fin 4) (u v : Fin 4 → ZMod 3) :
    GT4 k u v = (5 / 64) * reChi3 (hC3 u - hC3 v) := by
  have hpt : ∀ α : Fin 4 → ZMod 3,
      (reChi3 (wordC3 α u v k)) ^ 4
          * ∏ i ∈ univ.erase k, reChi3 (wordC3 α u v i)
        = (1 / 8) * (3
            * ∏ i ∈ univ.erase k, reChi3 (wordC3 α u v i)
            + 5 * ∏ i, reChi3 (wordC3 α u v i)) := by
    intro α
    rw [reChi3_pow4]
    have hprod : ∏ i, reChi3 (wordC3 α u v i)
        = reChi3 (wordC3 α u v k)
          * ∏ i ∈ univ.erase k, reChi3 (wordC3 α u v i) :=
      (Finset.mul_prod_erase univ (fun i => reChi3 (wordC3 α u v i))
        (Finset.mem_univ k)).symm
    rw [hprod]
    ring
  have e1 : GT4 k u v
      = (1 / 81) * ∑ α, (1 / 8)
          * (3 * ∏ i ∈ univ.erase k, reChi3 (wordC3 α u v i)
            + 5 * ∏ i, reChi3 (wordC3 α u v i)) := by
    unfold GT4
    congr 1
    exact Finset.sum_congr rfl (fun α _ => hpt α)
  have e2 : (1 / 81 : ℚ)
        * ((1 / 8) * (3 * ∑ α, ∏ i ∈ univ.erase k,
              reChi3 (wordC3 α u v i)
          + 5 * ∑ α, ∏ i, reChi3 (wordC3 α u v i)))
      = (1 / 8) * (3 * ((1 / 81)
            * ∑ α, ∏ i ∈ univ.erase k, reChi3 (wordC3 α u v i))
          + 5 * ((1 / 81) * ∑ α, ∏ i, reChi3 (wordC3 α u v i))) := by
    ring
  rw [e1, ← Finset.mul_sum, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, e2, T3_eq_zero k u v]
  show (1 / 8 : ℚ) * (3 * 0 + 5 * FC3 u v)
    = (5 / 64) * reChi3 (hC3 u - hC3 v)
  rw [FC3_eq]
  ring

/-- The per-plaquette `(4,1,1,1)` channel total at
(C₃, χ): summing the four quadrupled columns, the channel
kernel is `(5/16) · reChi(h − h′)` — exactly **five
halves times** the κ₄ plaquette kernel
`(1/8) · reChi(h − h′)`, matching the Python target
table (BR1-008). -/
theorem GT4_total (u v : Fin 4 → ZMod 3) :
    ∑ k, GT4 k u v = (5 / 16) * reChi3 (hC3 u - hC3 v) := by
  rw [Fin.sum_univ_four, GT4_eq, GT4_eq, GT4_eq, GT4_eq]
  ring

/-- The `(4,1,1,1)` channel seat form at (C₃, χ): the
per-plaquette quadrupled total, read on holonomy
classes. -/
def K7C3_4111 (a b : ZMod 3) : ℚ := ∑ k, GT4 k (secC3 a) (secC3 b)

theorem K7C3_4111_eq (a b : ZMod 3) :
    K7C3_4111 a b = (5 / 16) * reChi3 (a - b) := by
  rw [K7C3_4111, GT4_total, hC3_sec, hC3_sec]

/-- **Proportionality, `(4,1,1,1)`: exactly `5/2 ×` the
κ₄ kernel** (Python target: kernel
`(5/16, -5/32, -5/32; …)`). -/
theorem K7C3_4111_prop (a b : ZMod 3) :
    K7C3_4111 a b = (5 / 2) * K4C3 a b := by
  rw [K7C3_4111_eq, K4C3_kernel]; ring

theorem K7C3_4111_entry (a b : ZMod 3) :
    K7C3_4111 a b = if a = b then 5 / 16 else -5 / 32 := by
  have h := rc_kernel_entry (fun a b => K7C3_4111_eq a b) a b
  rwa [show (-(5 / 16 : ℚ)) / 2 = -5 / 32 from by norm_num] at h

theorem K7C3_4111_margins (a : ZMod 3) : ∑ b, K7C3_4111 a b = 0 :=
  rc_kernel_margins_of (fun a b => K7C3_4111_eq a b) a

theorem K7C3_4111_form (φ : ZMod 3 → ℚ) :
    ∑ a, ∑ b, φ a * K7C3_4111 a b * φ b
      = (5 / 32) * ((φ 0 - φ 1) ^ 2 + (φ 0 - φ 2) ^ 2
          + (φ 1 - φ 2) ^ 2) := by
  have h := rc_kernel_form (K := K7C3_4111) (c := 5 / 16)
    (fun a b => K7C3_4111_eq a b) φ
  rwa [show (5 / 16 : ℚ) / 2 = 5 / 32 from by norm_num] at h

end B7C3Quad4111

section B7C3Quad3211

/-- The per-plaquette **tripled-doubled** factor at
(C₃, χ): the uniform α-average of
`reChi(W_p)³ · reChi(W_q)² · ∏_{i ∉ {p, q}} reChi(W_i)`
— the seat avatar of one summand of `kappa7chan3211`
(B7-1b's `tripledDoubledQuadReMoment` at a plaquette,
tripled column `p`, doubled column `q`). -/
def GTD3 (p q : Fin 4) (u v : Fin 4 → ZMod 3) : ℚ :=
  (1 / 81) * ∑ α, (reChi3 (wordC3 α u v p)) ^ 3
    * (reChi3 (wordC3 α u v q)) ^ 2
    * ∏ i ∈ (univ.erase p).erase q, reChi3 (wordC3 α u v i)

/-- **Tripled-doubled plaquette identification (T1).**
For every ordered pair of distinct columns `p ≠ q`, the
tripled-doubled plaquette factor is
`(3/64) · reChi(h(u) − h(v))`, independent of the pair.
The proof is the cube fold at `p` and the square fold at
`q`: of the four resulting products, the two-factor
product vanishes (`T2_eq_zero`), the two three-factor
products vanish (`T3_eq_zero`), and the full four-factor
moment (`FC3_eq`) survives with weight `3/8`. -/
theorem GTD3_eq {p q : Fin 4} (hpq : p ≠ q) (u v : Fin 4 → ZMod 3) :
    GTD3 p q u v = (3 / 64) * reChi3 (hC3 u - hC3 v) := by
  have hcomm : (univ.erase q).erase p = (univ.erase p).erase q := by
    ext i
    simp only [Finset.mem_erase]
    tauto
  have hpt : ∀ α : Fin 4 → ZMod 3,
      (reChi3 (wordC3 α u v p)) ^ 3 * (reChi3 (wordC3 α u v q)) ^ 2
          * ∏ i ∈ (univ.erase p).erase q, reChi3 (wordC3 α u v i)
        = (1 / 8) * (∏ i ∈ (univ.erase p).erase q,
              reChi3 (wordC3 α u v i)
            + ∏ i ∈ univ.erase p, reChi3 (wordC3 α u v i)
            + 3 * ∏ i ∈ univ.erase q, reChi3 (wordC3 α u v i)
            + 3 * ∏ i, reChi3 (wordC3 α u v i)) := by
    intro α
    have hEp : ∏ i ∈ univ.erase p, reChi3 (wordC3 α u v i)
        = reChi3 (wordC3 α u v q)
          * ∏ i ∈ (univ.erase p).erase q, reChi3 (wordC3 α u v i) :=
      (Finset.mul_prod_erase (univ.erase p)
        (fun i => reChi3 (wordC3 α u v i))
        (Finset.mem_erase.mpr ⟨Ne.symm hpq, Finset.mem_univ q⟩)).symm
    have hEq : ∏ i ∈ univ.erase q, reChi3 (wordC3 α u v i)
        = reChi3 (wordC3 α u v p)
          * ∏ i ∈ (univ.erase p).erase q, reChi3 (wordC3 α u v i) := by
      calc ∏ i ∈ univ.erase q, reChi3 (wordC3 α u v i)
          = reChi3 (wordC3 α u v p)
            * ∏ i ∈ (univ.erase q).erase p, reChi3 (wordC3 α u v i) :=
            (Finset.mul_prod_erase (univ.erase q)
              (fun i => reChi3 (wordC3 α u v i))
              (Finset.mem_erase.mpr ⟨hpq, Finset.mem_univ p⟩)).symm
        _ = reChi3 (wordC3 α u v p)
            * ∏ i ∈ (univ.erase p).erase q, reChi3 (wordC3 α u v i) := by
            rw [hcomm]
    have hAll : ∏ i, reChi3 (wordC3 α u v i)
        = reChi3 (wordC3 α u v p) * reChi3 (wordC3 α u v q)
          * ∏ i ∈ (univ.erase p).erase q, reChi3 (wordC3 α u v i) := by
      calc ∏ i, reChi3 (wordC3 α u v i)
          = reChi3 (wordC3 α u v p)
            * ∏ i ∈ univ.erase p, reChi3 (wordC3 α u v i) :=
            (Finset.mul_prod_erase univ
              (fun i => reChi3 (wordC3 α u v i))
              (Finset.mem_univ p)).symm
        _ = reChi3 (wordC3 α u v p) * reChi3 (wordC3 α u v q)
            * ∏ i ∈ (univ.erase p).erase q, reChi3 (wordC3 α u v i) := by
            rw [hEp]; ring
    rw [reChi3_cube, reChi3_sq, hEp, hEq, hAll]
    ring
  have e1 : GTD3 p q u v
      = (1 / 81) * ∑ α, (1 / 8)
          * (∏ i ∈ (univ.erase p).erase q, reChi3 (wordC3 α u v i)
            + ∏ i ∈ univ.erase p, reChi3 (wordC3 α u v i)
            + 3 * ∏ i ∈ univ.erase q, reChi3 (wordC3 α u v i)
            + 3 * ∏ i, reChi3 (wordC3 α u v i)) := by
    unfold GTD3
    congr 1
    exact Finset.sum_congr rfl (fun α _ => hpt α)
  have e2 : (1 / 81 : ℚ)
        * ((1 / 8) * (∑ α, ∏ i ∈ (univ.erase p).erase q,
              reChi3 (wordC3 α u v i)
            + ∑ α, ∏ i ∈ univ.erase p, reChi3 (wordC3 α u v i)
            + 3 * ∑ α, ∏ i ∈ univ.erase q, reChi3 (wordC3 α u v i)
            + 3 * ∑ α, ∏ i, reChi3 (wordC3 α u v i)))
      = (1 / 8) * ((1 / 81) * ∑ α, ∏ i ∈ (univ.erase p).erase q,
            reChi3 (wordC3 α u v i)
          + (1 / 81) * ∑ α, ∏ i ∈ univ.erase p, reChi3 (wordC3 α u v i)
          + 3 * ((1 / 81) * ∑ α, ∏ i ∈ univ.erase q,
              reChi3 (wordC3 α u v i))
          + 3 * ((1 / 81) * ∑ α, ∏ i, reChi3 (wordC3 α u v i))) := by
    ring
  rw [e1, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, e2,
    T2_eq_zero hpq u v, T3_eq_zero p u v, T3_eq_zero q u v]
  show (1 / 8 : ℚ) * (0 + 0 + 3 * 0 + 3 * FC3 u v)
    = (3 / 64) * reChi3 (hC3 u - hC3 v)
  rw [FC3_eq]
  ring

/-- The per-plaquette `(3,2,1,1)`-**adjacent** channel
total at (C₃, χ): summing the tripled-doubled factor
over the eight ordered adjacent heavy pairs (tripled
column first), the channel kernel is
`(3/8) · reChi(h − h′)` — exactly **three times** the κ₄
plaquette kernel, matching the Python target table. -/
theorem GTD3_adj_total (u v : Fin 4 → ZMod 3) :
    ∑ k, ∑ l ∈ plaqAdj k, GTD3 k l u v
      = (3 / 8) * reChi3 (hC3 u - hC3 v) := by
  have hA0 : plaqAdj 0 = {1, 3} := rfl
  have hA1 : plaqAdj 1 = {0, 2} := rfl
  have hA2 : plaqAdj 2 = {1, 3} := rfl
  have hA3 : plaqAdj 3 = {0, 2} := rfl
  rw [Fin.sum_univ_four, hA0, hA1, hA2, hA3,
    Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_singleton,
    GTD3_eq (by decide : (0 : Fin 4) ≠ 1),
    GTD3_eq (by decide : (0 : Fin 4) ≠ 3),
    GTD3_eq (by decide : (1 : Fin 4) ≠ 0),
    GTD3_eq (by decide : (1 : Fin 4) ≠ 2),
    GTD3_eq (by decide : (2 : Fin 4) ≠ 1),
    GTD3_eq (by decide : (2 : Fin 4) ≠ 3),
    GTD3_eq (by decide : (3 : Fin 4) ≠ 0),
    GTD3_eq (by decide : (3 : Fin 4) ≠ 2)]
  ring

/-- The per-plaquette `(3,2,1,1)`-**opposite** channel
total at (C₃, χ): summing over the four ordered opposite
heavy pairs, the channel kernel is
`(3/16) · reChi(h − h′)` — exactly **three halves times**
the κ₄ plaquette kernel, matching the Python target
table. -/
theorem GTD3_opp_total (u v : Fin 4 → ZMod 3) :
    ∑ k, ∑ l ∈ plaqOpp k, GTD3 k l u v
      = (3 / 16) * reChi3 (hC3 u - hC3 v) := by
  have hO0 : plaqOpp 0 = {2} := rfl
  have hO1 : plaqOpp 1 = {3} := rfl
  have hO2 : plaqOpp 2 = {0} := rfl
  have hO3 : plaqOpp 3 = {1} := rfl
  rw [Fin.sum_univ_four, hO0, hO1, hO2, hO3,
    Finset.sum_singleton, Finset.sum_singleton,
    Finset.sum_singleton, Finset.sum_singleton,
    GTD3_eq (by decide : (0 : Fin 4) ≠ 2),
    GTD3_eq (by decide : (1 : Fin 4) ≠ 3),
    GTD3_eq (by decide : (2 : Fin 4) ≠ 0),
    GTD3_eq (by decide : (3 : Fin 4) ≠ 1)]
  ring

/-- The `(3,2,1,1)`-adjacent channel seat form at
(C₃, χ): the per-plaquette tripled-doubled total over
the ordered adjacent heavy pairs, read on holonomy
classes. -/
def K7C3_3211adj (a b : ZMod 3) : ℚ :=
  ∑ k, ∑ l ∈ plaqAdj k, GTD3 k l (secC3 a) (secC3 b)

theorem K7C3_3211adj_eq (a b : ZMod 3) :
    K7C3_3211adj a b = (3 / 8) * reChi3 (a - b) := by
  rw [K7C3_3211adj, GTD3_adj_total, hC3_sec, hC3_sec]

/-- **Proportionality, `(3,2,1,1)`-adjacent: exactly
`3 ×` the κ₄ kernel** (Python target:
`(3/8, -3/16, -3/16; …)`). -/
theorem K7C3_3211adj_prop (a b : ZMod 3) :
    K7C3_3211adj a b = 3 * K4C3 a b := by
  rw [K7C3_3211adj_eq, K4C3_kernel]; ring

theorem K7C3_3211adj_entry (a b : ZMod 3) :
    K7C3_3211adj a b = if a = b then 3 / 8 else -3 / 16 := by
  have h := rc_kernel_entry (fun a b => K7C3_3211adj_eq a b) a b
  rwa [show (-(3 / 8 : ℚ)) / 2 = -3 / 16 from by norm_num] at h

theorem K7C3_3211adj_margins (a : ZMod 3) :
    ∑ b, K7C3_3211adj a b = 0 :=
  rc_kernel_margins_of (fun a b => K7C3_3211adj_eq a b) a

theorem K7C3_3211adj_form (φ : ZMod 3 → ℚ) :
    ∑ a, ∑ b, φ a * K7C3_3211adj a b * φ b
      = (3 / 16) * ((φ 0 - φ 1) ^ 2 + (φ 0 - φ 2) ^ 2
          + (φ 1 - φ 2) ^ 2) := by
  have h := rc_kernel_form (K := K7C3_3211adj) (c := 3 / 8)
    (fun a b => K7C3_3211adj_eq a b) φ
  rwa [show (3 / 8 : ℚ) / 2 = 3 / 16 from by norm_num] at h

/-- The `(3,2,1,1)`-opposite channel seat form at
(C₃, χ): the per-plaquette tripled-doubled total over
the ordered opposite heavy pairs, read on holonomy
classes. -/
def K7C3_3211opp (a b : ZMod 3) : ℚ :=
  ∑ k, ∑ l ∈ plaqOpp k, GTD3 k l (secC3 a) (secC3 b)

theorem K7C3_3211opp_eq (a b : ZMod 3) :
    K7C3_3211opp a b = (3 / 16) * reChi3 (a - b) := by
  rw [K7C3_3211opp, GTD3_opp_total, hC3_sec, hC3_sec]

/-- **Proportionality, `(3,2,1,1)`-opposite: exactly
`3/2 ×` the κ₄ kernel** (Python target:
`(3/16, -3/32, -3/32; …)`). -/
theorem K7C3_3211opp_prop (a b : ZMod 3) :
    K7C3_3211opp a b = (3 / 2) * K4C3 a b := by
  rw [K7C3_3211opp_eq, K4C3_kernel]; ring

theorem K7C3_3211opp_entry (a b : ZMod 3) :
    K7C3_3211opp a b = if a = b then 3 / 16 else -3 / 32 := by
  have h := rc_kernel_entry (fun a b => K7C3_3211opp_eq a b) a b
  rwa [show (-(3 / 16 : ℚ)) / 2 = -3 / 32 from by norm_num] at h

theorem K7C3_3211opp_margins (a : ZMod 3) :
    ∑ b, K7C3_3211opp a b = 0 :=
  rc_kernel_margins_of (fun a b => K7C3_3211opp_eq a b) a

theorem K7C3_3211opp_form (φ : ZMod 3 → ℚ) :
    ∑ a, ∑ b, φ a * K7C3_3211opp a b * φ b
      = (3 / 32) * ((φ 0 - φ 1) ^ 2 + (φ 0 - φ 2) ^ 2
          + (φ 1 - φ 2) ^ 2) := by
  have h := rc_kernel_form (K := K7C3_3211opp) (c := 3 / 16)
    (fun a b => K7C3_3211opp_eq a b) φ
  rwa [show (3 / 16 : ℚ) / 2 = 3 / 32 from by norm_num] at h

end B7C3Quad3211

section B7C3Quad2221

/-- The sign pattern of a subset moment: `sgnT t` on
`S`, `0` off `S` — the pattern whose α-average must
vanish for every proper nonempty `S`. -/
def sPatS (S : Finset (Fin 4)) (t : Finset (Fin 4)) : Fin 4 → ZMod 3 :=
  fun i => if i ∈ S then sgnT t i else 0

theorem sum_sPatS (S t : Finset (Fin 4)) (F : Fin 4 → ZMod 3) :
    ∑ i, sPatS S t i * F i = ∑ i ∈ S, sgnT t i * F i := by
  have hA : ∑ i, (if i ∈ S then sgnT t i * F i else 0)
      = ∑ i ∈ S, sgnT t i * F i := by
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.mpr (Finset.subset_univ S)]
  rw [← hA]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hi : i ∈ S <;> simp [sPatS, hi]

/-- Private-site coefficients, plaquette, subset
patterns: for every proper nonempty `S` and every sign
pattern `t`, the pattern `sPatS S t` has a nonzero
α-coefficient somewhere — its coefficient vector is
`(a, a, −a, −a)`-shaped only when the pattern is constant
on all four columns or identically zero, which a proper
nonempty support excludes.  Hence no signed subset-word
sum survives the α-average.  (Finite check over the
sixteen subsets and sixteen patterns.) -/
theorem cGen_sPatS_ne : ∀ S : Finset (Fin 4), S ≠ univ →
    S.Nonempty → ∀ t : Finset (Fin 4),
    ∃ x, cGen (sPatS S t) x ≠ 0 := by decide

/-- The real-character product over an arbitrary subset
`S` expands over its sign patterns (the
`prod3_expand_gen` pattern at arbitrary cardinality). -/
theorem prod_expand_genS (W : Fin 4 → ZMod 3) (S : Finset (Fin 4)) :
    ∏ i ∈ S, ((reChi3 (W i) : ℚ) : ℂ)
      = (1 / (2 : ℂ) ^ S.card) * ∑ t ∈ S.powerset,
          chiC3 (∑ i ∈ S, sgnT t i * W i) := by
  calc ∏ i ∈ S, ((reChi3 (W i) : ℚ) : ℂ)
      = ∏ i ∈ S, ((chiC3 (W i) + chiC3 (-W i)) / 2) :=
        Finset.prod_congr rfl (fun i _ => reChi3_cast _)
    _ = (∏ i ∈ S, (chiC3 (W i) + chiC3 (-W i))) / (2 : ℂ) ^ S.card := by
        rw [Finset.prod_div_distrib, Finset.prod_const]
    _ = (1 / (2 : ℂ) ^ S.card) * ∑ t ∈ S.powerset,
          (∏ i ∈ t, chiC3 (W i)) * ∏ i ∈ S \ t, chiC3 (-W i) := by
        rw [Finset.prod_add]
        ring
    _ = (1 / (2 : ℂ) ^ S.card) * ∑ t ∈ S.powerset,
          chiC3 (∑ i ∈ S, sgnT t i * W i) := by
        congr 1
        refine Finset.sum_congr rfl (fun t ht => ?_)
        exact prod_split_genS W S t (Finset.mem_powerset.mp ht)

/-- **Subset-moment vanishing, plaquette.**  The
α-average of the product of the real characters over any
proper nonempty subset `S` of the plaquette's columns
is zero: in every signed expansion some stratum variable
survives with a nonzero coefficient
(`cGen_sPatS_ne`), and the character average over it
vanishes. -/
theorem prod_avg_eq_zero {S : Finset (Fin 4)} (hS : S ≠ univ)
    (hne : S.Nonempty) (u v : Fin 4 → ZMod 3) :
    (1 / 81 : ℚ) * ∑ α, ∏ i ∈ S, reChi3 (wordC3 α u v i) = 0 := by
  have hterm : ∀ t ∈ S.powerset,
      ∑ α, chiC3 (∑ i ∈ S, sgnT t i * wordC3 α u v i) = 0 := by
    intro t ht
    have e : ∀ α : Fin 4 → ZMod 3,
        chiC3 (∑ i ∈ S, sgnT t i * wordC3 α u v i)
          = chiC3 (∑ x, cGen (sPatS S t) x * α x
              + ∑ i, sPatS S t i * (v i - u i)) := by
      intro α
      rw [← sum_sPatS, wordC3_sum_gen]
    rw [Finset.sum_congr rfl (fun α _ => e α), alpha_sum]
    obtain ⟨x, hx⟩ := cGen_sPatS_ne S hS hne t
    rw [if_neg (fun h => hx (h x))]
  have key : (((1 / 81 : ℚ)
      * ∑ α, ∏ i ∈ S, reChi3 (wordC3 α u v i) : ℚ) : ℂ) = 0 := by
    calc (((1 / 81 : ℚ)
        * ∑ α, ∏ i ∈ S, reChi3 (wordC3 α u v i) : ℚ) : ℂ)
        = (1 / 81) * ∑ α, ∏ i ∈ S,
            ((reChi3 (wordC3 α u v i) : ℚ) : ℂ) := by
          push_cast
          ring
      _ = (1 / 81) * ∑ α, ((1 / (2 : ℂ) ^ S.card)
            * ∑ t ∈ S.powerset,
              chiC3 (∑ i ∈ S, sgnT t i * wordC3 α u v i)) := by
          congr 1
          refine Finset.sum_congr rfl (fun α _ => ?_)
          exact prod_expand_genS (wordC3 α u v) S
      _ = (1 / 81) * ((1 / (2 : ℂ) ^ S.card) * ∑ α,
            ∑ t ∈ S.powerset,
            chiC3 (∑ i ∈ S, sgnT t i * wordC3 α u v i)) := by
          congr 1
          rw [Finset.mul_sum]
      _ = (1 / 81) * ((1 / (2 : ℂ) ^ S.card) * ∑ t ∈ S.powerset,
            ∑ α, chiC3 (∑ i ∈ S, sgnT t i * wordC3 α u v i)) := by
          congr 1; congr 1
          rw [Finset.sum_comm]
      _ = (1 / 81) * ((1 / (2 : ℂ) ^ S.card)
            * ∑ t ∈ S.powerset, 0) := by
          congr 1; congr 1
          refine Finset.sum_congr rfl (fun t ht => hterm t ht)
      _ = 0 := by simp
  have h0 : (((1 / 81 : ℚ)
      * ∑ α, ∏ i ∈ S, reChi3 (wordC3 α u v i) : ℚ) : ℂ)
      = ((0 : ℚ) : ℂ) := by
    rw [key]; simp
  exact Rat.cast_injective h0

/-- The subset average over the full column set is the
κ₄ plaquette factor `FC3` itself. -/
theorem prod_avg_univ (u v : Fin 4 → ZMod 3) :
    (1 / 81 : ℚ) * ∑ α, ∏ i ∈ (univ : Finset (Fin 4)),
        reChi3 (wordC3 α u v i)
      = FC3 u v := rfl

/-- The per-plaquette **triple-doubled** factor at
(C₃, χ), indexed by its single (undoubled) column `s`:
the uniform α-average of
`(∏_{i ≠ s} reChi(W_i)²) · reChi(W_s)` — the seat avatar
of one unordered summand of `kappa7chan2221` (B7-1b's
`doubledDoubledDoubledQuadReMoment` at a plaquette, the
three columns other than `s` doubled).  Each ordered
triple of doubled columns has a unique undoubled
complement, so the channel total is six times the sum of
these factors (`G222_total` below). -/
def GS3 (s : Fin 4) (u v : Fin 4 → ZMod 3) : ℚ :=
  (1 / 81) * ∑ α, (∏ i ∈ univ.erase s, (reChi3 (wordC3 α u v i)) ^ 2)
    * reChi3 (wordC3 α u v s)

/-- **Triple-doubled plaquette identification (T1).**
For every undoubled column `s`, the triple-doubled
plaquette factor is `(1/64) · reChi(h(u) − h(v))`.  The
proof is the square fold at the three doubled columns:
expanding `∏_{i ≠ s} (1 + reChi(W_i))` over the subsets
of the erased set, every term averages a product over a
proper nonempty subset of columns and vanishes
(`prod_avg_eq_zero`), except the full subset, which
restores the four-factor moment (`FC3_eq`) with weight
`1/8`. -/
theorem GS3_eq (s : Fin 4) (u v : Fin 4 → ZMod 3) :
    GS3 s u v = (1 / 64) * reChi3 (hC3 u - hC3 v) := by
  set E : Finset (Fin 4) := univ.erase s with hE
  have hEcard : E.card = 3 := by
    rw [hE, Finset.card_erase_of_mem (Finset.mem_univ s),
      Finset.card_univ]
    rfl
  have hsE : ∀ t : Finset (Fin 4), t ⊆ E → s ∉ t := by
    intro t ht hst
    have : s ∈ E := ht hst
    rw [hE] at this
    exact (Finset.mem_erase.mp this).1 rfl
  have hpt : ∀ α : Fin 4 → ZMod 3,
      (∏ i ∈ E, (reChi3 (wordC3 α u v i)) ^ 2)
          * reChi3 (wordC3 α u v s)
        = (1 / 8) * ∑ t ∈ E.powerset,
            ∏ i ∈ insert s t, reChi3 (wordC3 α u v i) := by
    intro α
    have hsq : ∏ i ∈ E, (reChi3 (wordC3 α u v i)) ^ 2
        = (1 / 8) * ∑ t ∈ E.powerset, ∏ i ∈ t, reChi3 (wordC3 α u v i) := by
      calc ∏ i ∈ E, (reChi3 (wordC3 α u v i)) ^ 2
          = ∏ i ∈ E, ((reChi3 (wordC3 α u v i) + 1) / 2) :=
            Finset.prod_congr rfl (fun i _ => by rw [reChi3_sq]; ring)
        _ = (∏ i ∈ E, (reChi3 (wordC3 α u v i) + 1)) / 8 := by
            rw [Finset.prod_div_distrib, Finset.prod_const, hEcard]
            norm_num
        _ = (1 / 8) * ∑ t ∈ E.powerset,
              (∏ i ∈ t, reChi3 (wordC3 α u v i))
                * ∏ i ∈ E \ t, (1 : ℚ) := by
            rw [Finset.prod_add]
            ring
        _ = (1 / 8) * ∑ t ∈ E.powerset, ∏ i ∈ t, reChi3 (wordC3 α u v i) := by
            congr 1
            refine Finset.sum_congr rfl (fun t _ => ?_)
            rw [Finset.prod_const_one, mul_one]
    rw [hsq, mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl (fun t ht => ?_)
    have hst : s ∉ t := hsE t (Finset.mem_powerset.mp ht)
    rw [Finset.prod_insert hst]
    ring
  have step1 : GS3 s u v
      = (1 / 8) * ∑ t ∈ E.powerset,
          (1 / 81) * ∑ α, ∏ i ∈ insert s t, reChi3 (wordC3 α u v i) := by
    calc GS3 s u v
        = (1 / 81) * ∑ α, ∑ t ∈ E.powerset, (1 / 8)
            * ∏ i ∈ insert s t, reChi3 (wordC3 α u v i) := by
          unfold GS3
          congr 1
          refine Finset.sum_congr rfl (fun α _ => ?_)
          rw [hpt α, Finset.mul_sum]
      _ = (1 / 81) * ∑ t ∈ E.powerset, ∑ α, (1 / 8)
            * ∏ i ∈ insert s t, reChi3 (wordC3 α u v i) := by
          rw [Finset.sum_comm]
      _ = (1 / 8) * ∑ t ∈ E.powerset,
            (1 / 81) * ∑ α, ∏ i ∈ insert s t, reChi3 (wordC3 α u v i) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun t _ => ?_)
          rw [← Finset.mul_sum]
          ring
  have step2 : ∑ t ∈ E.powerset,
        (1 / 81) * ∑ α, ∏ i ∈ insert s t, reChi3 (wordC3 α u v i)
      = FC3 u v := by
    rw [Finset.sum_eq_single E]
    · rw [hE, Finset.insert_erase (Finset.mem_univ s)]
      exact prod_avg_univ u v
    · intro t ht htE
      have htE' : t ⊆ E := Finset.mem_powerset.mp ht
      have hst : s ∉ t := hsE t htE'
      have hne : (insert s t).Nonempty := ⟨s, Finset.mem_insert_self s t⟩
      have hproper : insert s t ≠ univ := by
        intro h
        apply htE
        have hEt : E = t := by
          calc E = (insert s t).erase s := by rw [h, hE]
            _ = t := Finset.erase_insert hst
        exact hEt.symm
      exact prod_avg_eq_zero hproper hne u v
    · intro h
      exact absurd (Finset.mem_powerset.mpr (fun x hx => hx)) h
  rw [step1, step2, FC3_eq]
  ring

/-- The per-plaquette **ordered triple-doubled** factor
at (C₃, χ): the uniform α-average of
`reChi(W_p)² · reChi(W_q)² · reChi(W_r)² ·
∏_{i ∉ {p, q, r}} reChi(W_i)` — the seat avatar of one
summand of `kappa7chan2221` (B7-1b's
`doubledDoubledDoubledQuadReMoment` at a plaquette,
doubled columns `p, q, r`). -/
def G222 (p q r : Fin 4) (u v : Fin 4 → ZMod 3) : ℚ :=
  (1 / 81) * ∑ α, (reChi3 (wordC3 α u v p)) ^ 2
    * (reChi3 (wordC3 α u v q)) ^ 2
    * (reChi3 (wordC3 α u v r)) ^ 2
    * ∏ i ∈ ((univ.erase p).erase q).erase r, reChi3 (wordC3 α u v i)

/-- **Ordered triple-doubled identification (T1).**  For
every ordered triple of pairwise distinct columns, the
tripled-doubled factor is `(1/64) · reChi(h(u) − h(v))`:
the remaining product is over the singleton complement
`{s}`, and the factor is `GS3 s`. -/
theorem G222_eq {p q r : Fin 4} (hpq : p ≠ q) (hpr : p ≠ r)
    (hqr : q ≠ r) (u v : Fin 4 → ZMod 3) :
    G222 p q r u v = (1 / 64) * reChi3 (hC3 u - hC3 v) := by
  have hrmem : r ∈ (univ.erase p).erase q :=
    Finset.mem_erase.mpr ⟨Ne.symm hqr, Finset.mem_erase.mpr ⟨Ne.symm hpr,
      Finset.mem_univ r⟩⟩
  have hqmem : q ∈ univ.erase p :=
    Finset.mem_erase.mpr ⟨Ne.symm hpq, Finset.mem_univ q⟩
  have hcard : (((univ.erase p).erase q).erase r).card = 1 := by
    rw [Finset.card_erase_of_mem hrmem, Finset.card_erase_of_mem hqmem,
      Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ]
    norm_num [Fintype.card_fin]
  obtain ⟨s, hs⟩ := Finset.card_eq_one.mp hcard
  have hsmem : s ∈ ((univ.erase p).erase q).erase r := by
    rw [hs]; exact Finset.mem_singleton_self s
  have hsr : s ≠ r := (Finset.mem_erase.mp hsmem).1
  have hsq : s ≠ q := (Finset.mem_erase.mp (Finset.mem_erase.mp hsmem).2).1
  have hsp : s ≠ p :=
    (Finset.mem_erase.mp (Finset.mem_erase.mp
      (Finset.mem_erase.mp hsmem).2).2).1
  have herase : univ.erase s
      = insert p (insert q ({r} : Finset (Fin 4))) := by
    have hsub : insert p (insert q ({r} : Finset (Fin 4)))
        ⊆ univ.erase s := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ i⟩
      rcases hi with rfl | rfl | rfl
      · exact Ne.symm hsp
      · exact Ne.symm hsq
      · exact Ne.symm hsr
    have hcard1 : (insert p (insert q ({r} : Finset (Fin 4)))).card
        = 3 := by
      rw [Finset.card_insert_of_notMem (by
            simp only [Finset.mem_insert, Finset.mem_singleton]
            push_neg
            exact ⟨hpq, hpr⟩),
        Finset.card_insert_of_notMem (by
            simp only [Finset.mem_singleton]
            exact hqr),
        Finset.card_singleton]
    have hcard2 : (univ.erase s).card = 3 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ s), Finset.card_univ]
      norm_num [Fintype.card_fin]
    exact (Finset.eq_of_subset_of_card_le hsub (by simp [hcard1, hcard2])).symm
  have hpt : ∀ α : Fin 4 → ZMod 3,
      (reChi3 (wordC3 α u v p)) ^ 2 * (reChi3 (wordC3 α u v q)) ^ 2
          * (reChi3 (wordC3 α u v r)) ^ 2
          * ∏ i ∈ ((univ.erase p).erase q).erase r,
              reChi3 (wordC3 α u v i)
        = (∏ i ∈ univ.erase s, (reChi3 (wordC3 α u v i)) ^ 2)
          * reChi3 (wordC3 α u v s) := by
    intro α
    have h1 : ∏ i ∈ ((univ.erase p).erase q).erase r,
          reChi3 (wordC3 α u v i)
        = reChi3 (wordC3 α u v s) := by
      rw [hs, Finset.prod_singleton]
    have h2 : ∏ i ∈ univ.erase s, (reChi3 (wordC3 α u v i)) ^ 2
        = (reChi3 (wordC3 α u v p)) ^ 2 * (reChi3 (wordC3 α u v q)) ^ 2
          * (reChi3 (wordC3 α u v r)) ^ 2 := by
      rw [herase, Finset.prod_insert (by
            simp only [Finset.mem_insert, Finset.mem_singleton]
            push_neg
            exact ⟨hpq, hpr⟩),
        Finset.prod_insert (by
            simp only [Finset.mem_singleton]
            exact hqr),
        Finset.prod_singleton]
      ring
    rw [h1, h2]
  have e : G222 p q r u v = GS3 s u v := by
    unfold G222 GS3
    congr 1
    exact Finset.sum_congr rfl (fun α _ => hpt α)
  rw [e, GS3_eq]

/-- The per-plaquette `(2,2,2,1)` channel total at
(C₃, χ): summing the ordered triple-doubled factor over
the twenty-four ordered distinct triples, the channel
kernel is `(3/8) · reChi(h − h′)` — exactly **three
times** the κ₄ plaquette kernel, matching the Python
target table. -/
theorem G222_total (u v : Fin 4 → ZMod 3) :
    ∑ p, ∑ q ∈ univ.erase p, ∑ r ∈ (univ.erase p).erase q,
        G222 p q r u v
      = (3 / 8) * reChi3 (hC3 u - hC3 v) := by
  have hC : ∀ p : Fin 4, ∀ q ∈ univ.erase p,
      ∀ r ∈ (univ.erase p).erase q,
      G222 p q r u v = (1 / 64) * reChi3 (hC3 u - hC3 v) := by
    intro p q hq r hr
    have hqp : q ≠ p := (Finset.mem_erase.mp hq).1
    have hrq : r ≠ q := (Finset.mem_erase.mp hr).1
    have hrp : r ≠ p := (Finset.mem_erase.mp (Finset.mem_erase.mp hr).2).1
    exact G222_eq (Ne.symm hqp) (Ne.symm hrp) (Ne.symm hrq) u v
  have hcard2 : ∀ p : Fin 4, ∀ q ∈ univ.erase p,
      ((univ.erase p).erase q).card = 2 := by
    intro p q hq
    rw [Finset.card_erase_of_mem hq, Finset.card_erase_of_mem
      (Finset.mem_univ p), Finset.card_univ]
    norm_num [Fintype.card_fin]
  have hcard3 : ∀ p : Fin 4, (univ.erase p).card = 3 := by
    intro p
    rw [Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ]
    norm_num [Fintype.card_fin]
  calc ∑ p, ∑ q ∈ univ.erase p, ∑ r ∈ (univ.erase p).erase q,
        G222 p q r u v
      = ∑ p, ∑ q ∈ univ.erase p, ∑ r ∈ (univ.erase p).erase q,
          (1 / 64) * reChi3 (hC3 u - hC3 v) :=
        Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl
          (fun q hq => Finset.sum_congr rfl (fun r hr => hC p q hq r hr)))
    _ = ∑ p, ∑ q ∈ univ.erase p,
          2 * ((1 / 64) * reChi3 (hC3 u - hC3 v)) :=
        Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl
          (fun q hq => by
            rw [Finset.sum_const, hcard2 p q hq, nsmul_eq_mul]
            norm_num))
    _ = ∑ p, 3 * (2 * ((1 / 64) * reChi3 (hC3 u - hC3 v))) :=
        Finset.sum_congr rfl (fun p _ => by
          rw [Finset.sum_const, hcard3 p, nsmul_eq_mul]
          norm_num)
    _ = 4 * (3 * (2 * ((1 / 64) * reChi3 (hC3 u - hC3 v)))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        norm_num
    _ = (3 / 8) * reChi3 (hC3 u - hC3 v) := by ring

/-- The `(2,2,2,1)` channel seat form at (C₃, χ): the
per-plaquette ordered triple-doubled total, read on
holonomy classes. -/
def K7C3_2221 (a b : ZMod 3) : ℚ :=
  ∑ p, ∑ q ∈ univ.erase p, ∑ r ∈ (univ.erase p).erase q,
    G222 p q r (secC3 a) (secC3 b)

theorem K7C3_2221_eq (a b : ZMod 3) :
    K7C3_2221 a b = (3 / 8) * reChi3 (a - b) := by
  rw [K7C3_2221, G222_total, hC3_sec, hC3_sec]

/-- **Proportionality, `(2,2,2,1)`: exactly `3 ×` the
κ₄ kernel** (Python target: `(3/8, -3/16, -3/16; …)`). -/
theorem K7C3_2221_prop (a b : ZMod 3) :
    K7C3_2221 a b = 3 * K4C3 a b := by
  rw [K7C3_2221_eq, K4C3_kernel]; ring

theorem K7C3_2221_entry (a b : ZMod 3) :
    K7C3_2221 a b = if a = b then 3 / 8 else -3 / 16 := by
  have h := rc_kernel_entry (fun a b => K7C3_2221_eq a b) a b
  rwa [show (-(3 / 8 : ℚ)) / 2 = -3 / 16 from by norm_num] at h

theorem K7C3_2221_margins (a : ZMod 3) :
    ∑ b, K7C3_2221 a b = 0 :=
  rc_kernel_margins_of (fun a b => K7C3_2221_eq a b) a

theorem K7C3_2221_form (φ : ZMod 3 → ℚ) :
    ∑ a, ∑ b, φ a * K7C3_2221 a b * φ b
      = (3 / 16) * ((φ 0 - φ 1) ^ 2 + (φ 0 - φ 2) ^ 2
          + (φ 1 - φ 2) ^ 2) := by
  have h := rc_kernel_form (K := K7C3_2221) (c := 3 / 8)
    (fun a b => K7C3_2221_eq a b) φ
  rwa [show (3 / 8 : ℚ) / 2 = 3 / 16 from by norm_num] at h

end B7C3Quad2221

section B7CycleThetaAux

/-- Component values of a `Fin 6`-vector given as a
matrix literal (this module's own copy of the β⁶ probe's
helper). -/
private theorem app6 {α : Type*} (x : Fin 6 → α) (a b c d e f : α)
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
matrix literal (this module's own copy). -/
private theorem app5 {α : Type*} (x : Fin 5 → α) (a b c d e : α)
    (h : x = ![a, b, c, d, e]) :
    x 0 = a ∧ x 1 = b ∧ x 2 = c ∧ x 3 = d ∧ x 4 = e := by
  subst h
  exact ⟨by simp [Matrix.cons_val_zero],
    by simp [Matrix.cons_val_one, Matrix.head_cons],
    by simp [Matrix.cons_val_two, Matrix.head_cons],
    by simp [Matrix.cons_val_three, Matrix.head_cons],
    by simp [Matrix.cons_val_four, Matrix.head_cons]⟩

/-- The sign pattern of a five-factor moment on a
6-support: `sgnT6 t` with the doubled link's sign
replaced by `0` — the pattern whose α-average must
vanish (five surviving factors). -/
def sPat6 (k : Fin 6) (t : Finset (Fin 6)) : Fin 6 → ZMod 3 :=
  fun i => if i = k then 0 else sgnT6 t i

theorem sPat6_self (k : Fin 6) (t : Finset (Fin 6)) :
    sPat6 k t k = 0 := if_pos rfl

theorem sPat6_of_ne {k i : Fin 6} (t : Finset (Fin 6)) (h : i ≠ k) :
    sPat6 k t i = sgnT6 t i := if_neg h

theorem sum_sPat6 (k : Fin 6) (t : Finset (Fin 6)) (F : Fin 6 → ZMod 3) :
    ∑ i, sPat6 k t i * F i
      = ∑ i ∈ univ.erase k, sgnT6 t i * F i := by
  have h1 := Finset.add_sum_erase univ
    (fun i => sPat6 k t i * F i) (Finset.mem_univ k)
  rw [sPat6_self, zero_mul, zero_add] at h1
  rw [← h1]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hik : i ≠ k := (Finset.mem_erase.mp hi).1
  rw [sPat6_of_ne t hik]

/-- The α-coefficients of a general signed 6-cycle word
sum `∑ᵢ sᵢ Wᵢ`: `c_s = s_s − s_{s−1}` (indices mod 6) —
`cCoeff6` with the sign function `sgnT6 t` replaced by
an arbitrary coefficient function `s`. -/
def cGen6 (s : Fin 6 → ZMod 3) : Fin 6 → ZMod 3 :=
  ![s 0 - s 5, s 1 - s 0, s 2 - s 1, s 3 - s 2, s 4 - s 3, s 5 - s 4]

theorem cCoeff6_eq_cGen6 (t : Finset (Fin 6)) :
    cCoeff6 t = cGen6 (sgnT6 t) := rfl

/-- The signed 6-cycle word sum, general coefficients. -/
theorem word6_sum_gen (s α u v : Fin 6 → ZMod 3) :
    ∑ i, s i * word6 α u v i
      = ∑ x, cGen6 s x * α x + ∑ i, s i * (v i - u i) := by
  have hA := app6 (alphaPart6 α) _ _ _ _ _ _ rfl
  have hC := app6 (cGen6 s) _ _ _ _ _ _ rfl
  have key : ∀ F : Fin 6 → ZMod 3,
      (∑ i, s i * F i) = s 0 * F 0 + s 1 * F 1
        + s 2 * F 2 + s 3 * F 3 + s 4 * F 4
        + s 5 * F 5 :=
    fun F => Fin.sum_univ_six _
  rw [show (∑ i, s i * word6 α u v i)
      = ∑ i, (s i * alphaPart6 α i + s i * (v i - u i)) from
    Finset.sum_congr rfl (fun i _ => by rw [word6]; ring)]
  rw [Finset.sum_add_distrib, key, key, Fin.sum_univ_six]
  rw [hA.1, hA.2.1, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2.1, hA.2.2.2.2.2,
    hC.1, hC.2.1, hC.2.2.1, hC.2.2.2.1, hC.2.2.2.2.1, hC.2.2.2.2.2]
  ring

/-- The signed Θ word sum, general coefficients (the
β⁶ probe's `wordT_sum_id` with `sgnT6 t` replaced by an
arbitrary coefficient function `s`; `cGenT` is already
general there). -/
theorem wordT_sum_gen (s : Fin 6 → ZMod 3) (α : Fin 5 → ZMod 3)
    (u v : Fin 6 → ZMod 3) :
    ∑ i, s i * wordT α u v i
      = ∑ x, cGenT s x * α x + ∑ i, s i * (v i - u i) := by
  have hA := app6 (alphaPartT α) _ _ _ _ _ _ rfl
  have hC := app5 (cGenT s) _ _ _ _ _ rfl
  have key : ∀ F : Fin 6 → ZMod 3,
      (∑ i, s i * F i) = s 0 * F 0 + s 1 * F 1
        + s 2 * F 2 + s 3 * F 3 + s 4 * F 4
        + s 5 * F 5 :=
    fun F => Fin.sum_univ_six _
  rw [show (∑ i, s i * wordT α u v i)
      = ∑ i, (s i * alphaPartT α i + s i * (v i - u i)) from
    Finset.sum_congr rfl (fun i _ => by rw [wordT]; ring)]
  rw [Finset.sum_add_distrib, key, key, Fin.sum_univ_five]
  rw [hA.1, hA.2.1, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2.1, hA.2.2.2.2.2,
    hC.1, hC.2.1, hC.2.2.1, hC.2.2.2.1, hC.2.2.2.2]
  ring

/-- Private-site coefficients, 6-cycle, five factors:
for every doubled link `k` and sign pattern `t`, the
pattern `sPat6 k t` has a nonzero α-coefficient
somewhere on the cycle — a signed cycle sum has
vanishing coefficients only for constant sign patterns,
and `sPat6 k t` (one `0`, five `±1`) is never constant.
(Finite check over the six links and 64 patterns.) -/
theorem cGen6_sPat6_ne : ∀ k : Fin 6, ∀ t : Finset (Fin 6),
    ∃ x, cGen6 (sPat6 k t) x ≠ 0 := by decide

/-- Private-site coefficients, Θ support, five factors:
for every doubled link `k` and sign pattern `t`, the
pattern `sPat6 k t` has a nonzero α-coefficient
somewhere on the Θ support — each length-2 path's two
links must carry equal signs for the midpoint
coefficients to vanish, and the doubled link breaks its
own path's pair.  (Finite check over the six links and
64 patterns.) -/
theorem cGenT_sPat6_ne : ∀ k : Fin 6, ∀ t : Finset (Fin 6),
    ∃ x, cGenT (sPat6 k t) x ≠ 0 := by decide

/-- The signed character product over a subset `S` of
links: the β⁶ probe's `prod_split6` with ambient set
`S`. -/
theorem prod_split6S (W : Fin 6 → ZMod 3) (S t : Finset (Fin 6))
    (ht : t ⊆ S) :
    (∏ i ∈ t, chiC3 (W i)) * (∏ i ∈ S \ t, chiC3 (-W i))
      = chiC3 (∑ i ∈ S, sgnT6 t i * W i) := by
  have hsum : (∑ i ∈ t, W i) + (∑ i ∈ S \ t, -W i)
      = ∑ i ∈ S, sgnT6 t i * W i := by
    have hA : ∑ i ∈ S, (if i ∈ t then W i else 0) = ∑ i ∈ t, W i := by
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
        Finset.inter_eq_right.mpr ht]
    have hB : ∑ i ∈ S, (if i ∈ t then (0 : ZMod 3) else -W i)
        = ∑ i ∈ S \ t, -W i := by
      have e1 : (S.filter (fun i => i ∉ t)) = S \ t := by
        ext i
        simp [Finset.mem_sdiff, Finset.mem_filter]
      rw [← e1, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ t <;> simp [hi]
    rw [← hA, ← hB, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [sgnT6_mul]
    by_cases hi : i ∈ t <;> simp [hi]
  rw [← chiC3_sum_prod t W, ← chiC3_sum_prod (S \ t) (fun i => -W i),
    ← chiC3_add]
  exact congrArg chiC3 hsum

/-- The five-factor real-character product over a
5-subset of links expands over its sign patterns. -/
theorem prod5_expand6 (W : Fin 6 → ZMod 3) (S : Finset (Fin 6))
    (hS : S.card = 5) :
    ∏ i ∈ S, ((reChi3 (W i) : ℚ) : ℂ)
      = (1 / 32) * ∑ t ∈ S.powerset,
          chiC3 (∑ i ∈ S, sgnT6 t i * W i) := by
  calc ∏ i ∈ S, ((reChi3 (W i) : ℚ) : ℂ)
      = ∏ i ∈ S, ((chiC3 (W i) + chiC3 (-W i)) / 2) :=
        Finset.prod_congr rfl (fun i _ => reChi3_cast _)
    _ = (∏ i ∈ S, (chiC3 (W i) + chiC3 (-W i))) / 32 := by
        rw [Finset.prod_div_distrib, Finset.prod_const, hS]
        norm_num
    _ = (1 / 32) * ∑ t ∈ S.powerset,
          (∏ i ∈ t, chiC3 (W i)) * ∏ i ∈ S \ t, chiC3 (-W i) := by
        rw [Finset.prod_add]
        ring
    _ = (1 / 32) * ∑ t ∈ S.powerset,
          chiC3 (∑ i ∈ S, sgnT6 t i * W i) := by
        congr 1
        refine Finset.sum_congr rfl (fun t ht => ?_)
        exact prod_split6S W S t (Finset.mem_powerset.mp ht)

/-- **Five-factor vanishing, 6-cycle.**  The α-average
of the five factors complementary to a doubled link
`k` is zero: in every signed expansion some stratum
variable survives with a nonzero coefficient (a
non-constant sign pattern on the cycle), and the
character average over it vanishes. -/
theorem T5C6_eq_zero (k : Fin 6) (u v : Fin 6 → ZMod 3) :
    (1 / 729 : ℚ) * ∑ α, ∏ i ∈ univ.erase k,
        reChi3 (word6 α u v i)
      = 0 := by
  have hS : (univ.erase k).card = 5 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ]
    norm_num [Fintype.card_fin]
  have hterm : ∀ t ∈ (univ.erase k).powerset,
      ∑ α, chiC3 (∑ i ∈ univ.erase k, sgnT6 t i * word6 α u v i)
        = 0 := by
    intro t _
    have e : ∀ α : Fin 6 → ZMod 3,
        chiC3 (∑ i ∈ univ.erase k, sgnT6 t i * word6 α u v i)
          = chiC3 (∑ x, cGen6 (sPat6 k t) x * α x
              + ∑ i, sPat6 k t i * (v i - u i)) := by
      intro α
      rw [← sum_sPat6, word6_sum_gen]
    rw [Finset.sum_congr rfl (fun α _ => e α), alpha_sum6]
    obtain ⟨x, hx⟩ := cGen6_sPat6_ne k t
    rw [if_neg (fun h => hx (h x))]
  have key : (((1 / 729 : ℚ)
      * ∑ α, ∏ i ∈ univ.erase k, reChi3 (word6 α u v i) : ℚ) : ℂ)
      = 0 := by
    calc (((1 / 729 : ℚ)
        * ∑ α, ∏ i ∈ univ.erase k, reChi3 (word6 α u v i) : ℚ) : ℂ)
        = (1 / 729) * ∑ α, ∏ i ∈ univ.erase k,
            ((reChi3 (word6 α u v i) : ℚ) : ℂ) := by
          push_cast
          ring
      _ = (1 / 729) * ∑ α, ((1 / 32)
            * ∑ t ∈ (univ.erase k).powerset,
              chiC3 (∑ i ∈ univ.erase k, sgnT6 t i * word6 α u v i)) := by
          congr 1
          refine Finset.sum_congr rfl (fun α _ => ?_)
          exact prod5_expand6 (word6 α u v) _ hS
      _ = (1 / 729) * ((1 / 32) * ∑ α, ∑ t ∈ (univ.erase k).powerset,
            chiC3 (∑ i ∈ univ.erase k, sgnT6 t i * word6 α u v i)) := by
          congr 1
          rw [Finset.mul_sum]
      _ = (1 / 729) * ((1 / 32) * ∑ t ∈ (univ.erase k).powerset,
            ∑ α, chiC3 (∑ i ∈ univ.erase k,
              sgnT6 t i * word6 α u v i)) := by
          rw [Finset.sum_comm]
      _ = (1 / 729) * ((1 / 32)
            * ∑ t ∈ (univ.erase k).powerset, 0) := by
          congr 1; congr 1
          refine Finset.sum_congr rfl (fun t ht => hterm t ht)
      _ = 0 := by simp
  have h0 : (((1 / 729 : ℚ)
      * ∑ α, ∏ i ∈ univ.erase k, reChi3 (word6 α u v i) : ℚ) : ℂ)
      = ((0 : ℚ) : ℂ) := by
    rw [key]; simp
  exact Rat.cast_injective h0

/-- **Five-factor vanishing, Θ(2,2,2).**  The α-average
of the five factors complementary to a doubled link
`k` is zero: in every signed expansion some stratum
variable survives with a nonzero coefficient (the
doubled link's path pair is broken), and the character
average over it vanishes. -/
theorem T5T_eq_zero (k : Fin 6) (u v : Fin 6 → ZMod 3) :
    (1 / 243 : ℚ) * ∑ α : Fin 5 → ZMod 3, ∏ i ∈ univ.erase k,
        reChi3 (wordT α u v i)
      = 0 := by
  have hS : (univ.erase k).card = 5 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ]
    norm_num [Fintype.card_fin]
  have hterm : ∀ t ∈ (univ.erase k).powerset,
      ∑ α : Fin 5 → ZMod 3,
        chiC3 (∑ i ∈ univ.erase k, sgnT6 t i * wordT α u v i)
        = 0 := by
    intro t _
    have e : ∀ α : Fin 5 → ZMod 3,
        chiC3 (∑ i ∈ univ.erase k, sgnT6 t i * wordT α u v i)
          = chiC3 (∑ x, cGenT (sPat6 k t) x * α x
              + ∑ i, sPat6 k t i * (v i - u i)) := by
      intro α
      rw [← sum_sPat6, wordT_sum_gen]
    rw [Finset.sum_congr rfl (fun α _ => e α), alpha_sum5]
    obtain ⟨x, hx⟩ := cGenT_sPat6_ne k t
    rw [if_neg (fun h => hx (h x))]
  have key : (((1 / 243 : ℚ)
      * ∑ α : Fin 5 → ZMod 3, ∏ i ∈ univ.erase k,
          reChi3 (wordT α u v i) : ℚ) : ℂ)
      = 0 := by
    calc (((1 / 243 : ℚ)
        * ∑ α : Fin 5 → ZMod 3, ∏ i ∈ univ.erase k,
            reChi3 (wordT α u v i) : ℚ) : ℂ)
        = (1 / 243) * ∑ α : Fin 5 → ZMod 3, ∏ i ∈ univ.erase k,
            ((reChi3 (wordT α u v i) : ℚ) : ℂ) := by
          push_cast
          ring
      _ = (1 / 243) * ∑ α : Fin 5 → ZMod 3, ((1 / 32)
            * ∑ t ∈ (univ.erase k).powerset,
              chiC3 (∑ i ∈ univ.erase k, sgnT6 t i * wordT α u v i)) := by
          congr 1
          refine Finset.sum_congr rfl (fun α _ => ?_)
          exact prod5_expand6 (wordT α u v) _ hS
      _ = (1 / 243) * ((1 / 32) * ∑ α : Fin 5 → ZMod 3,
            ∑ t ∈ (univ.erase k).powerset,
            chiC3 (∑ i ∈ univ.erase k, sgnT6 t i * wordT α u v i)) := by
          congr 1
          rw [Finset.mul_sum]
      _ = (1 / 243) * ((1 / 32) * ∑ t ∈ (univ.erase k).powerset,
            ∑ α : Fin 5 → ZMod 3, chiC3 (∑ i ∈ univ.erase k,
              sgnT6 t i * wordT α u v i)) := by
          rw [Finset.sum_comm]
      _ = (1 / 243) * ((1 / 32)
            * ∑ t ∈ (univ.erase k).powerset, 0) := by
          congr 1; congr 1
          refine Finset.sum_congr rfl (fun t ht => hterm t ht)
      _ = 0 := by simp
  have h0 : (((1 / 243 : ℚ)
      * ∑ α : Fin 5 → ZMod 3, ∏ i ∈ univ.erase k,
          reChi3 (wordT α u v i) : ℚ) : ℂ)
      = ((0 : ℚ) : ℂ) := by
    rw [key]; simp
  exact Rat.cast_injective h0

end B7CycleThetaAux

section B7C3C6Doubled

/-- The per-cycle **doubled C6 factor** at (C₃, χ): the
uniform α-average of
`reChi(W_k)² · ∏_{i ≠ k} reChi(W_i)` over the 6-cycle's
six stratum variables — the seat avatar of one summand
of `kappa7chan211111C6` (B7-1b's `doubledHexaReMoment`
at a directed 6-cycle support, doubled link `k`). -/
def FC6d (k : Fin 6) (u v : Fin 6 → ZMod 3) : ℚ :=
  (1 / 729) * ∑ α, (reChi3 (word6 α u v k)) ^ 2
    * ∏ i ∈ univ.erase k, reChi3 (word6 α u v i)

/-- **Doubled C6 identification (T1).**  For every
doubled link `k`, the doubled C6 factor is
`(1/64) · reChi(H₆(u) − H₆(v))`.  The proof is the
square fold: the `1` part averages the five complementary
factors and vanishes (`T5C6_eq_zero`), the `reChi(w)`
part restores the full six-factor moment (`FC6_eq`)
with weight `1/2`. -/
theorem FC6d_eq (k : Fin 6) (u v : Fin 6 → ZMod 3) :
    FC6d k u v = (1 / 64) * reChi3 (H6 u - H6 v) := by
  have hpt : ∀ α : Fin 6 → ZMod 3,
      (reChi3 (word6 α u v k)) ^ 2
          * ∏ i ∈ univ.erase k, reChi3 (word6 α u v i)
        = (1 / 2) * (∏ i ∈ univ.erase k, reChi3 (word6 α u v i)
            + ∏ i, reChi3 (word6 α u v i)) := by
    intro α
    rw [reChi3_sq]
    have hprod : ∏ i, reChi3 (word6 α u v i)
        = reChi3 (word6 α u v k)
          * ∏ i ∈ univ.erase k, reChi3 (word6 α u v i) :=
      (Finset.mul_prod_erase univ (fun i => reChi3 (word6 α u v i))
        (Finset.mem_univ k)).symm
    rw [hprod]
    ring
  have e1 : FC6d k u v
      = (1 / 729) * ∑ α, (1 / 2)
          * (∏ i ∈ univ.erase k, reChi3 (word6 α u v i)
            + ∏ i, reChi3 (word6 α u v i)) := by
    unfold FC6d
    congr 1
    exact Finset.sum_congr rfl (fun α _ => hpt α)
  have e2 : (1 / 729 : ℚ)
        * ((1 / 2) * (∑ α, ∏ i ∈ univ.erase k, reChi3 (word6 α u v i)
          + ∑ α, ∏ i, reChi3 (word6 α u v i)))
      = (1 / 2) * ((1 / 729)
          * ∑ α, ∏ i ∈ univ.erase k, reChi3 (word6 α u v i)
          + (1 / 729) * ∑ α, ∏ i, reChi3 (word6 α u v i)) := by
    ring
  rw [e1, ← Finset.mul_sum, Finset.sum_add_distrib, e2,
    T5C6_eq_zero k u v]
  show (1 / 2 : ℚ) * (0 + FC6 u v)
    = (1 / 64) * reChi3 (H6 u - H6 v)
  rw [FC6_eq]
  ring

/-- The `(2,1,1,1,1,1)` channel seat form on `C6`
supports at (C₃, χ): the per-cycle doubled total (sum
over the six doubled links), read on holonomy classes. -/
def K7C3_211111C6 (a b : ZMod 3) : ℚ := ∑ k, FC6d k (sec6 a) (sec6 b)

theorem K7C3_211111C6_eq (a b : ZMod 3) :
    K7C3_211111C6 a b = (3 / 32) * reChi3 (a - b) := by
  have h : ∀ k : Fin 6, FC6d k (sec6 a) (sec6 b)
      = (1 / 64) * reChi3 (a - b) := by
    intro k
    rw [FC6d_eq, H6_sec, H6_sec]
  rw [K7C3_211111C6, Finset.sum_congr rfl (fun k _ => h k),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- **Proportionality, `(2,1,1,1,1,1)` on `C6`: exactly
`3/4 ×` the κ₄ kernel** (Python target:
`(3/32, -3/64, -3/64; …)`). -/
theorem K7C3_211111C6_prop (a b : ZMod 3) :
    K7C3_211111C6 a b = (3 / 4) * K4C3 a b := by
  rw [K7C3_211111C6_eq, K4C3_kernel]; ring

theorem K7C3_211111C6_entry (a b : ZMod 3) :
    K7C3_211111C6 a b = if a = b then 3 / 32 else -3 / 64 := by
  have h := rc_kernel_entry (fun a b => K7C3_211111C6_eq a b) a b
  rwa [show (-(3 / 32 : ℚ)) / 2 = -3 / 64 from by norm_num] at h

theorem K7C3_211111C6_margins (a : ZMod 3) :
    ∑ b, K7C3_211111C6 a b = 0 :=
  rc_kernel_margins_of (fun a b => K7C3_211111C6_eq a b) a

theorem K7C3_211111C6_form (φ : ZMod 3 → ℚ) :
    ∑ a, ∑ b, φ a * K7C3_211111C6 a b * φ b
      = (3 / 64) * ((φ 0 - φ 1) ^ 2 + (φ 0 - φ 2) ^ 2
          + (φ 1 - φ 2) ^ 2) := by
  have h := rc_kernel_form (K := K7C3_211111C6) (c := 3 / 32)
    (fun a b => K7C3_211111C6_eq a b) φ
  rwa [show (3 / 32 : ℚ) / 2 = 3 / 64 from by norm_num] at h

end B7C3C6Doubled

section B7C3ThetaDoubled

/-- The per-support **doubled Θ factor** at (C₃, χ):
the uniform α-average of
`reChi(W_k)² · ∏_{i ≠ k} reChi(W_i)` over the Θ
support's five stratum variables — the seat avatar of
one summand of `kappa7chan211111Theta` (B7-1b's
`doubledHexaReMoment` at a Θ(2,2,2) support, doubled
link `k`). -/
def FTd (k : Fin 6) (u v : Fin 6 → ZMod 3) : ℚ :=
  (1 / 243) * ∑ α, (reChi3 (wordT α u v k)) ^ 2
    * ∏ i ∈ univ.erase k, reChi3 (wordT α u v i)

/-- **Doubled Θ identification (T1).**  For every
doubled link `k`, the doubled Θ factor is
`(1/64) · reChi(H_Θ(u) − H_Θ(v))`.  The proof is the
square fold: the `1` part averages the five
complementary factors and vanishes (`T5T_eq_zero`), the
`reChi(w)` part restores the full six-factor moment
(`FT_eq`) with weight `1/2`. -/
theorem FTd_eq (k : Fin 6) (u v : Fin 6 → ZMod 3) :
    FTd k u v = (1 / 64) * reChi3 (HT u - HT v) := by
  have hpt : ∀ α : Fin 5 → ZMod 3,
      (reChi3 (wordT α u v k)) ^ 2
          * ∏ i ∈ univ.erase k, reChi3 (wordT α u v i)
        = (1 / 2) * (∏ i ∈ univ.erase k, reChi3 (wordT α u v i)
            + ∏ i, reChi3 (wordT α u v i)) := by
    intro α
    rw [reChi3_sq]
    have hprod : ∏ i, reChi3 (wordT α u v i)
        = reChi3 (wordT α u v k)
          * ∏ i ∈ univ.erase k, reChi3 (wordT α u v i) :=
      (Finset.mul_prod_erase univ (fun i => reChi3 (wordT α u v i))
        (Finset.mem_univ k)).symm
    rw [hprod]
    ring
  have e1 : FTd k u v
      = (1 / 243) * ∑ α, (1 / 2)
          * (∏ i ∈ univ.erase k, reChi3 (wordT α u v i)
            + ∏ i, reChi3 (wordT α u v i)) := by
    unfold FTd
    congr 1
    exact Finset.sum_congr rfl (fun α _ => hpt α)
  have e2 : (1 / 243 : ℚ)
        * ((1 / 2) * (∑ α, ∏ i ∈ univ.erase k, reChi3 (wordT α u v i)
          + ∑ α, ∏ i, reChi3 (wordT α u v i)))
      = (1 / 2) * ((1 / 243)
          * ∑ α, ∏ i ∈ univ.erase k, reChi3 (wordT α u v i)
          + (1 / 243) * ∑ α, ∏ i, reChi3 (wordT α u v i)) := by
    ring
  rw [e1, ← Finset.mul_sum, Finset.sum_add_distrib, e2,
    T5T_eq_zero k u v]
  show (1 / 2 : ℚ) * (0 + FT u v)
    = (1 / 64) * reChi3 (HT u - HT v)
  rw [FT_eq]
  ring

/-- The `(2,1,1,1,1,1)` channel seat form on
`Θ(2,2,2)` supports at (C₃, χ), on its orbit-holonomy
coordinates: the per-support doubled total (sum over
the six doubled links), read through the section
`secT`. -/
def K7C3_211111Theta (p q : ZMod 3 × ZMod 3) : ℚ :=
  ∑ k, FTd k (secT p) (secT q)

/-- The doubled Θ kernel factors through the
holonomy-sum difference, with kernel
`(3/32) · reChi` — the Python side's factorization,
certified here. -/
theorem K7C3_211111Theta_eq (p q : ZMod 3 × ZMod 3) :
    K7C3_211111Theta p q
      = (3 / 32) * reChi3 ((p.1 + p.2) - (q.1 + q.2)) := by
  have h : ∀ k : Fin 6, FTd k (secT p) (secT q)
      = (1 / 64) * reChi3 ((p.1 + p.2) - (q.1 + q.2)) := by
    intro k
    rw [FTd_eq, HT_sec, HT_sec]
  rw [K7C3_211111Theta, Finset.sum_congr rfl (fun k _ => h k),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- **Proportionality, `(2,1,1,1,1,1)` on `Θ(2,2,2)`:
exactly `3/4 ×` the κ₄ kernel in the holonomy-sum
coordinate** (via `(3/32)` vs `(1/8)`). -/
theorem K7C3_211111Theta_prop (p q : ZMod 3 × ZMod 3) :
    K7C3_211111Theta p q
      = (3 / 4) * K4C3 (p.1 + p.2) (q.1 + q.2) := by
  rw [K7C3_211111Theta_eq, K4C3_kernel]; ring

/-- The doubled Θ kernel's margins vanish exactly:
summing over the nine orbit pairs, each holonomy sum
`q.1 + q.2` occurs three times and the `reChi` margins
close. -/
theorem K7C3_211111Theta_margins (p : ZMod 3 × ZMod 3) :
    ∑ q, K7C3_211111Theta p q = 0 := by
  have h1 : ∑ q : ZMod 3 × ZMod 3, K7C3_211111Theta p q
      = ∑ q : ZMod 3 × ZMod 3, (3 / 32)
          * reChi3 ((p.1 + p.2) - (q.1 + q.2)) :=
    Finset.sum_congr rfl (fun q _ => K7C3_211111Theta_eq p q)
  rw [h1, Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro q1 _
  have h2 : ∀ q2 : ZMod 3, (3 / 32 : ℚ)
        * reChi3 ((p.1 + p.2) - (q1 + q2))
      = (3 / 32) * reChi3 (((p.1 + p.2) - q1) - q2) :=
    fun q2 => by
      rw [show (p.1 + p.2) - (q1 + q2) = ((p.1 + p.2) - q1) - q2 from by ring]
  rw [Finset.sum_congr rfl (fun q2 _ => h2 q2), ← Finset.mul_sum]
  have h3 : ∑ q2, reChi3 (((p.1 + p.2) - q1) - q2) = 0 := by
    have hm := rc_kernel_margins 1 ((p.1 + p.2) - q1)
    simpa using hm
  rw [h3, mul_zero]

/-- The doubled Θ diagonal form vanishes on constant
orbit profiles — the canonical embedding of `K₆` (the
constants) into Θ orbit profiles. -/
theorem K7C3_211111Theta_form_of_const (ψ : ZMod 3 × ZMod 3 → ℚ)
    (hψ : ∀ p q, ψ p = ψ q) :
    ∑ p, ∑ q, ψ p * K7C3_211111Theta p q * ψ q = 0 := by
  have hψc : ∀ p, ψ p = ψ (0, 0) := fun p => hψ p (0, 0)
  have step : ∀ p : ZMod 3 × ZMod 3,
      ∑ q, ψ p * K7C3_211111Theta p q * ψ q = 0 := by
    intro p
    rw [Finset.sum_congr rfl (g := fun q => (ψ (0, 0) * ψ (0, 0))
      * K7C3_211111Theta p q) (fun q _ => by rw [hψc p, hψc q]; ring),
      ← Finset.mul_sum, K7C3_211111Theta_margins, mul_zero]
  rw [Finset.sum_congr rfl (fun p _ => step p)]
  exact Finset.sum_const_zero

end B7C3ThetaDoubled

section B7C3Book

/-- Component values of a `Fin 7`-vector given as a
matrix literal (this module's own helper). -/
private theorem app7 {α : Type*} (x : Fin 7 → α) (a b c d e f g : α)
    (h : x = ![a, b, c, d, e, f, g]) :
    x 0 = a ∧ x 1 = b ∧ x 2 = c ∧ x 3 = d ∧ x 4 = e ∧ x 5 = f
      ∧ x 6 = g := by
  subst h
  exact ⟨by simp [Matrix.cons_val_zero],
    by simp [Matrix.cons_val_one, Matrix.head_cons],
    by simp [Matrix.cons_val_two, Matrix.head_cons],
    by simp [Matrix.cons_val_three, Matrix.head_cons],
    by simp [Matrix.cons_val_four, Matrix.head_cons],
    by simp,
    by simp⟩

/-- Sign vector of a subset `t ⊆ Fin 7`: `+1` on `t`,
`−1` off it (the `sgnT` pattern at seven links). -/
def sgnT7 (t : Finset (Fin 7)) (i : Fin 7) : ZMod 3 :=
  if i ∈ t then 1 else -1

theorem sgnT7_mul (t : Finset (Fin 7)) (i : Fin 7) (w : ZMod 3) :
    sgnT7 t i * w = if i ∈ t then w else -w := by
  by_cases hi : i ∈ t <;> simp [sgnT7, hi]

theorem sgnT7_empty : ∀ i, sgnT7 (∅ : Finset (Fin 7)) i = -1 := by
  decide

theorem sgnT7_univ : ∀ i, sgnT7 (univ : Finset (Fin 7)) i = 1 := by
  decide

/-- The α-part of the Θ(1,3,3) book support's seven
link words at the C₃ seat.  The support has six sites —
two degree-3 sites `A = 0`, `B = 1` joined by the shared
link `0`, and two internally disjoint length-3 paths
`A-2-3-B` (links `1, 2, 3`) and `A-4-5-B` (links
`4, 5, 6`): link `0` reads `α_A − α_B`, the path links
read off successive site differences. -/
def alphaPartB (α : Fin 6 → ZMod 3) : Fin 7 → ZMod 3 :=
  ![α 0 - α 1, α 0 - α 2, α 2 - α 3, α 3 - α 1,
    α 0 - α 4, α 4 - α 5, α 5 - α 1]

/-- The book support's seven link words (additive C₃
notation); boundary letters `u v` are indexed by
links. -/
def wordB (α : Fin 6 → ZMod 3) (u v : Fin 7 → ZMod 3) (i : Fin 7) :
    ZMod 3 :=
  alphaPartB α i + (v i - u i)

/-- The book support's holonomy: the total boundary sum
over the seven links.  On the Python side's orbit
coordinates `(hₐ, h_b)` (the two path holonomies against
the shared link) this total is the holonomy sum
`hₐ + h_b` (see `secB` below). -/
def HB (u : Fin 7 → ZMod 3) : ZMod 3 := ∑ i, u i

/-- The α-coefficient vector of a general signed book
word sum `∑ᵢ sᵢ Wᵢ`: site `A` collects the shared link
and the two path heads, site `B` collects the shared
link and the two path tails with a sign, and each
internal path site collects its two links. -/
def cGenB (s : Fin 7 → ZMod 3) : Fin 6 → ZMod 3 :=
  ![s 0 + s 1 + s 4, -s 0 - s 3 - s 6, -s 1 + s 2, -s 2 + s 3,
    -s 4 + s 5, -s 5 + s 6]

/-- The α-coefficients of the signed book word sum for
the sign pattern `sgnT7 t`. -/
def cCoeffB (t : Finset (Fin 7)) : Fin 6 → ZMod 3 := cGenB (sgnT7 t)

/-- The boundary part of the signed book word sum. -/
def pB (t : Finset (Fin 7)) (u v : Fin 7 → ZMod 3) : ZMod 3 :=
  ∑ i, sgnT7 t i * (v i - u i)

theorem wordB_sum_id (t : Finset (Fin 7)) (α : Fin 6 → ZMod 3)
    (u v : Fin 7 → ZMod 3) :
    ∑ i, sgnT7 t i * wordB α u v i
      = ∑ s, cCoeffB t s * α s + pB t u v := by
  have hA := app7 (alphaPartB α) _ _ _ _ _ _ _ rfl
  have hC := app6 (cCoeffB t) _ _ _ _ _ _ rfl
  have key : ∀ F : Fin 7 → ZMod 3,
      (∑ i, sgnT7 t i * F i) = sgnT7 t 0 * F 0 + sgnT7 t 1 * F 1
        + sgnT7 t 2 * F 2 + sgnT7 t 3 * F 3 + sgnT7 t 4 * F 4
        + sgnT7 t 5 * F 5 + sgnT7 t 6 * F 6 :=
    fun F => Fin.sum_univ_seven _
  rw [show (∑ i, sgnT7 t i * wordB α u v i)
      = ∑ i, (sgnT7 t i * alphaPartB α i + sgnT7 t i * (v i - u i)) from
    Finset.sum_congr rfl (fun i _ => by rw [wordB]; ring)]
  rw [Finset.sum_add_distrib, key, key, pB, key, Fin.sum_univ_six]
  rw [hA.1, hA.2.1, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2.1, hA.2.2.2.2.2.1,
    hA.2.2.2.2.2.2, hC.1, hC.2.1, hC.2.2.1, hC.2.2.2.1, hC.2.2.2.2.1,
    hC.2.2.2.2.2]
  ring

/-- Survival classification for the Θ(1,3,3) book: the
coefficient vector `cCoeffB t` vanishes identically
only for the two constant sign patterns `t = ∅` and
`t = univ` — a mixed pattern leaves a path-site
coefficient nonzero (the internal sites force each
path's three signs to agree, and then the shared link's
sign is forced to agree with both, since
`s₀ = −a − b` with `a, b ∈ {±1}` lies in `{±1}` only
when `a = b = s₀`).  (Decided by exhaustive evaluation
over the 128 subsets.) -/
theorem survivorsB : ∀ t : Finset (Fin 7), (∀ s, cCoeffB t s = 0)
    ↔ t = ∅ ∨ t = univ := by decide

theorem pB_empty (u v : Fin 7 → ZMod 3) :
    pB ∅ u v = HB u - HB v := by
  unfold pB HB
  rw [Finset.sum_congr rfl (g := fun i => u i - v i) (fun i _ => by
    rw [sgnT7_empty]; ring), Finset.sum_sub_distrib]

theorem pB_univ (u v : Fin 7 → ZMod 3) :
    pB univ u v = HB v - HB u := by
  unfold pB HB
  rw [Finset.sum_congr rfl (g := fun i => v i - u i) (fun i _ => by
    rw [sgnT7_univ]; ring), Finset.sum_sub_distrib]

/-- The signed character product splits as the
character of the signed sum, for words indexed by
`Fin 7` (the `prod_split6` pattern at seven links). -/
theorem prod_split7 (W : Fin 7 → ZMod 3) (t : Finset (Fin 7)) :
    (∏ i ∈ t, chiC3 (W i)) * (∏ i ∈ univ \ t, chiC3 (-W i))
      = chiC3 (∑ i, sgnT7 t i * W i) := by
  have hsum : (∑ i ∈ t, W i) + (∑ i ∈ univ \ t, -W i)
      = ∑ i, sgnT7 t i * W i := by
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
    rw [sgnT7_mul]
    by_cases hi : i ∈ t <;> simp [hi]
  rw [← chiC3_sum_prod t W, ← chiC3_sum_prod (univ \ t) (fun i => -W i),
    ← chiC3_add]
  exact congrArg chiC3 hsum

/-- Per-α expansion of a seven-factor real-character
product over sign patterns (the `per_alpha6` pattern
at seven factors). -/
theorem per_alpha7 (W : Fin 7 → ZMod 3) :
    ∏ i, ((reChi3 (W i) : ℚ) : ℂ)
      = (1 / 128) * ∑ t : Finset (Fin 7), chiC3 (∑ i, sgnT7 t i * W i) := by
  have hpow : (univ : Finset (Fin 7)).powerset = univ :=
    Finset.eq_univ_of_forall (fun t =>
      Finset.mem_powerset.mpr (Finset.subset_univ t))
  calc ∏ i, ((reChi3 (W i) : ℚ) : ℂ)
      = ∏ i, ((chiC3 (W i) + chiC3 (-W i)) / 2) :=
        Finset.prod_congr rfl (fun i _ => reChi3_cast _)
    _ = (∏ i, (chiC3 (W i) + chiC3 (-W i))) / 128 := by
        rw [Finset.prod_div_distrib]
        simp [Finset.prod_const, Finset.card_univ]
        ring
    _ = (1 / 128) * ∑ t ∈ univ.powerset,
          (∏ i ∈ t, chiC3 (W i)) * ∏ i ∈ univ \ t, chiC3 (-W i) := by
        rw [Finset.prod_add]
        ring
    _ = (1 / 128) * ∑ t : Finset (Fin 7),
          chiC3 (∑ i, sgnT7 t i * W i) := by
        rw [hpow]
        congr 1
        apply Finset.sum_congr rfl
        intro t _
        exact prod_split7 W t

/-- The per-support **book factor** at (C₃, χ): the
uniform α-average of the product of the seven link
words' real characters over the support's six stratum
variables — the seat avatar of the `heptaReMoment`
(B7-1b) at a Θ(1,3,3) book support. -/
def FB (u v : Fin 7 → ZMod 3) : ℚ :=
  (1 / 729) * ∑ α, ∏ i, reChi3 (wordB α u v i)

/-- **Book identification (T1).**  The per-support book
factor at (C₃, χ) is the holonomy class kernel
`(1/64) · reChi(H_B(u) − H_B(u′))` — the two constant
sign patterns survive the α-average, each contributing
the full `729` configurations against the `1/128`
expansion factor.  This is the Python target: book
kernel `(1/64, -1/128, -1/128; …)` in the holonomy-sum
coordinate. -/
theorem FB_eq (u v : Fin 7 → ZMod 3) :
    FB u v = (1 / 64) * reChi3 (HB u - HB v) := by
  have key : ((FB u v : ℚ) : ℂ)
      = (1 / 128 : ℂ) * (chiC3 (HB u - HB v) + chiC3 (-(HB u - HB v))) := by
    have hfil : Finset.filter (fun t : Finset (Fin 7) => ∀ s, cCoeffB t s = 0)
        univ = {∅, univ} := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton]
      exact survivorsB t
    calc ((FB u v : ℚ) : ℂ)
        = (1 / 729) * ∑ α, ∏ i, ((reChi3 (wordB α u v i) : ℚ) : ℂ) := by
          rw [FB]; push_cast; ring
      _ = (1 / 729) * ∑ α : Fin 6 → ZMod 3, ((1 / 128)
            * ∑ t : Finset (Fin 7),
              chiC3 (∑ s, cCoeffB t s * α s + pB t u v)) := by
          congr 1
          refine Finset.sum_congr rfl (fun α _ => ?_)
          rw [per_alpha7 (wordB α u v)]
          congr 1
          refine Finset.sum_congr rfl (fun t _ => ?_)
          rw [wordB_sum_id]
      _ = (1 / 729) * ((1 / 128) * ∑ α : Fin 6 → ZMod 3,
            ∑ t : Finset (Fin 7),
            chiC3 (∑ s, cCoeffB t s * α s + pB t u v)) := by
          congr 1
          rw [Finset.mul_sum]
      _ = (1 / 729) * ((1 / 128) * ∑ t : Finset (Fin 7),
            ∑ α : Fin 6 → ZMod 3,
            chiC3 (∑ s, cCoeffB t s * α s + pB t u v)) := by
          rw [Finset.sum_comm]
      _ = (1 / 729) * ((1 / 128) * ∑ t : Finset (Fin 7),
            if (∀ s, cCoeffB t s = 0) then 729 * chiC3 (pB t u v)
            else 0) := by
          rw [Finset.sum_congr rfl
            (fun t _ => alpha_sum6 (cCoeffB t) (pB t u v))]
      _ = (1 / 729) * ((1 / 128) * (729 * chiC3 (HB u - HB v)
            + 729 * chiC3 (-(HB u - HB v)))) := by
          have hsum : ∑ t : Finset (Fin 7),
                (if (∀ s, cCoeffB t s = 0) then 729 * chiC3 (pB t u v)
                  else 0)
              = 729 * chiC3 (HB u - HB v)
                + 729 * chiC3 (-(HB u - HB v)) := by
            rw [← Finset.sum_filter, hfil,
              Finset.sum_insert (by decide), Finset.sum_singleton,
              pB_empty, pB_univ,
              show HB v - HB u = -(HB u - HB v) from by ring]
          rw [hsum]
      _ = (1 / 128 : ℂ) * (chiC3 (HB u - HB v)
            + chiC3 (-(HB u - HB v))) := by ring
  have h2 : (((1 / 64) * reChi3 (HB u - HB v) : ℚ) : ℂ)
      = (1 / 128 : ℂ) * (chiC3 (HB u - HB v) + chiC3 (-(HB u - HB v))) := by
    rw [show (((1 / 64) * reChi3 (HB u - HB v) : ℚ) : ℂ)
        = (1 / 64 : ℂ) * ((reChi3 (HB u - HB v) : ℚ) : ℂ) by push_cast; ring,
      reChi3_cast]
    ring
  exact Rat.cast_injective (key.trans h2.symm)

/-- The standard section of the book holonomy map into
orbit coordinates: the orbit pair `(hₐ, h_b)` is
carried by the two paths' head links,
`secB (hₐ, h_b) = ![0, hₐ, 0, 0, h_b, 0, 0]`, with
`HB (secB p) = p.1 + p.2` — the holonomy sum of the
Python side's factorization. -/
def secB (p : ZMod 3 × ZMod 3) : Fin 7 → ZMod 3 :=
  ![0, p.1, 0, 0, p.2, 0, 0]

theorem HB_sec (p : ZMod 3 × ZMod 3) : HB (secB p) = p.1 + p.2 := by
  have e := app7 (secB p) 0 p.1 0 0 p.2 0 0 rfl
  unfold HB
  rw [Fin.sum_univ_seven, e.1, e.2.1, e.2.2.1, e.2.2.2.1, e.2.2.2.2.1,
    e.2.2.2.2.2.1, e.2.2.2.2.2.2]
  simp

/-- The `Θ(1,3,3)` book channel seat form at (C₃, χ),
on its orbit-holonomy coordinates: the per-support
book factor, read through the section `secB`. -/
def K7C3_Theta133 (p q : ZMod 3 × ZMod 3) : ℚ := FB (secB p) (secB q)

/-- The book kernel factors through the holonomy-sum
difference, with kernel `(1/64) · reChi` — the Python
side's factorization, certified here. -/
theorem K7C3_Theta133_eq (p q : ZMod 3 × ZMod 3) :
    K7C3_Theta133 p q
      = (1 / 64) * reChi3 ((p.1 + p.2) - (q.1 + q.2)) := by
  rw [K7C3_Theta133, FB_eq, HB_sec, HB_sec]

/-- **Proportionality, `Θ(1,3,3)` book: exactly `1/8 ×`
the κ₄ kernel in the holonomy-sum coordinate** (via
`(1/64)` vs `(1/8)`). -/
theorem K7C3_Theta133_prop (p q : ZMod 3 × ZMod 3) :
    K7C3_Theta133 p q = (1 / 8) * K4C3 (p.1 + p.2) (q.1 + q.2) := by
  rw [K7C3_Theta133_eq, K4C3_kernel]; ring

/-- The book kernel's margins vanish exactly: summing
over the nine orbit pairs, each holonomy sum
`q.1 + q.2` occurs three times and the `reChi` margins
close. -/
theorem K7C3_Theta133_margins (p : ZMod 3 × ZMod 3) :
    ∑ q, K7C3_Theta133 p q = 0 := by
  have h1 : ∑ q : ZMod 3 × ZMod 3, K7C3_Theta133 p q
      = ∑ q : ZMod 3 × ZMod 3, (1 / 64)
          * reChi3 ((p.1 + p.2) - (q.1 + q.2)) :=
    Finset.sum_congr rfl (fun q _ => K7C3_Theta133_eq p q)
  rw [h1, Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro q1 _
  have h2 : ∀ q2 : ZMod 3, (1 / 64 : ℚ)
        * reChi3 ((p.1 + p.2) - (q1 + q2))
      = (1 / 64) * reChi3 (((p.1 + p.2) - q1) - q2) :=
    fun q2 => by
      rw [show (p.1 + p.2) - (q1 + q2) = ((p.1 + p.2) - q1) - q2 from by ring]
  rw [Finset.sum_congr rfl (fun q2 _ => h2 q2), ← Finset.mul_sum]
  have h3 : ∑ q2, reChi3 (((p.1 + p.2) - q1) - q2) = 0 := by
    have hm := rc_kernel_margins 1 ((p.1 + p.2) - q1)
    simpa using hm
  rw [h3, mul_zero]

/-- The book diagonal form vanishes on constant orbit
profiles — the canonical embedding of `K₆` (the
constants) into book orbit profiles. -/
theorem K7C3_Theta133_form_of_const (ψ : ZMod 3 × ZMod 3 → ℚ)
    (hψ : ∀ p q, ψ p = ψ q) :
    ∑ p, ∑ q, ψ p * K7C3_Theta133 p q * ψ q = 0 := by
  have hψc : ∀ p, ψ p = ψ (0, 0) := fun p => hψ p (0, 0)
  have step : ∀ p : ZMod 3 × ZMod 3,
      ∑ q, ψ p * K7C3_Theta133 p q * ψ q = 0 := by
    intro p
    rw [Finset.sum_congr rfl (g := fun q => (ψ (0, 0) * ψ (0, 0))
      * K7C3_Theta133 p q) (fun q _ => by rw [hψc p, hψc q]; ring),
      ← Finset.mul_sum, K7C3_Theta133_margins, mul_zero]
  rw [Finset.sum_congr rfl (fun p _ => step p)]
  exact Finset.sum_const_zero

end B7C3Book

section B7C3Verdict

/-- **Joint verdict at (C₃, χ), N = 4 (K-K7 check,
B7-PROBE-b).**  For every observable `φ` in the joint
kernel `K₆` — certified here by `φ` lying in the kernel
of the κ₄ diagonal form, which is the whole joint
kernel at this seat (`seatK6_C3`: the κ₅ channel is
proportional to κ₄ at this seat, B5-PROBE, and every
κ₆ channel vanishes on it, `verdict_C3_B6`) — **every**
β⁷ channel's diagonal form at `φ` is exactly `0`: the
`(4,1,1,1)` form, the `(3,2,1,1)`-adjacent form, the
`(3,2,1,1)`-opposite form, the `(2,2,2,1)` form, the
`(2,1,1,1,1,1)` form on `C6` supports, the
`(2,1,1,1,1,1)` form on `Θ(2,2,2)` supports on the
constant orbit profile (the canonical embedding of
`K₆` into Θ orbit profiles), and the `(1⁷)` book form
on `Θ(1,3,3)` supports on the constant orbit profile.
No channel is negative on `K₆`; all vanish identically;
**K-K7 does not fire at this seat**, and the
degenerate-perturbation regress continues past β⁷ at
this seat.  Seat scope only: this is the (C₃, χ) half
of the pre-registered outcome table (registry BR1-008);
no general sign is asserted, and the multiples in the
table are seat data, not mechanism evidence. -/
theorem verdict_C3_B7 (φ : ZMod 3 → ℚ)
    (h4 : ∑ a, ∑ b, φ a * K4C3 a b * φ b = 0) :
    (∑ a, ∑ b, φ a * K7C3_4111 a b * φ b = 0)
      ∧ (∑ a, ∑ b, φ a * K7C3_3211adj a b * φ b = 0)
      ∧ (∑ a, ∑ b, φ a * K7C3_3211opp a b * φ b = 0)
      ∧ (∑ a, ∑ b, φ a * K7C3_2221 a b * φ b = 0)
      ∧ (∑ a, ∑ b, φ a * K7C3_211111C6 a b * φ b = 0)
      ∧ (∑ p, ∑ q, (fun _ => φ 0) p * K7C3_211111Theta p q
          * (fun _ => φ 0) q = 0)
      ∧ (∑ p, ∑ q, (fun _ => φ 0) p * K7C3_Theta133 p q
          * (fun _ => φ 0) q = 0) := by
  have hK : φ 0 = φ 1 ∧ φ 1 = φ 2 := (K4C3_form_eq_zero_iff φ).mp h4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact rc_form_eq_zero_of_const (fun a b => K7C3_4111_eq a b) φ hK
  · exact rc_form_eq_zero_of_const (fun a b => K7C3_3211adj_eq a b) φ hK
  · exact rc_form_eq_zero_of_const (fun a b => K7C3_3211opp_eq a b) φ hK
  · exact rc_form_eq_zero_of_const (fun a b => K7C3_2221_eq a b) φ hK
  · exact rc_form_eq_zero_of_const (fun a b => K7C3_211111C6_eq a b) φ hK
  · exact K7C3_211111Theta_form_of_const (fun _ => φ 0) (fun p q => rfl)
  · exact K7C3_Theta133_form_of_const (fun _ => φ 0) (fun p q => rfl)

end B7C3Verdict

/-!
# β⁷ probe, part 2: the (S₃, std) seat at N = 4 (B7-PROBE-c)

Seat scope only: **N = 4**, seat **(S₃, std)** (`d = 2`).
NO CLAIM.  Parts of the Clay Yang–Mills statement closed
by this module: **0**.  Dials 0/4.  The β⁷ general sign
stays FRONTIER and nothing here is a statement about
𝒜 ⪰ 0 in the large, about all β, or about the continuum.

**Pre-registered targets** (the Python side,
`b7probe-run.txt`, exact rational arithmetic, registry
**BR1-008**, the BRIDGE-1 target table for this part):
the κ₄ kernel at this seat is
`[1/4, 0, -1/8; 0, 0, 0; -1/8, 0, 1/16]` with kernel of
the diagonal form exactly `{φ₀ = φ₂}`; the κ₅ channel is
`4 ×` that kernel and every κ₆ channel is a positive
multiple of it or factors through it on the orbit space
(B5/B6 probes, consumed as landed), so seat-`K₆` is
`ker κ₄^dep` — re-derived in this module below
(`seatK6_S3`).  The new order-7 channel kernels are
exact positive multiples of the seat κ₄ kernel:

| channel | kernel | multiple of κ₄ kernel |
|---|---|---|
| `(4,1,1,1)` | `[5, 0, -5/2; 0, 0, 0; -5/2, 0, 5/4]` | `20 ×` |
| `(3,2,1,1)`-adjacent | `[6, 0, -3; 0, 0, 0; -3, 0, 3/2]` | `24 ×` |
| `(3,2,1,1)`-opposite | `[3, 0, -3/2; 0, 0, 0; -3/2, 0, 3/4]` | `12 ×` |
| `(2,2,2,1)` | `[6, 0, -3; 0, 0, 0; -3, 0, 3/2]` | `24 ×` |
| `(2,1,1,1,1,1)` on `C6` | `[3/8, 0, -3/16; 0, 0, 0; -3/16, 0, 3/32]` | `3/2 ×` |
| `(2,1,1,1,1,1)` on `Θ(2,2,2)` | orbit kernel, §`B7S3ThetaDoubled` | `3 ×`, A3-gated |
| `(1⁷)` on `Θ(1,3,3)` book | orbit kernel, §`B7S3Book` | `1/4 ×`, A3-gated |

proved below as theorems about the channel kernels
defined from their own entry content (the per-support-type
enumeration matrices of the Python table, in the (S₃, std)
mirror style of the β⁵/β⁶ probes: explicit exact matrices,
calibrated against the κ₄ probe), never as definitions.
Per-type fence: the Python table found the plaquette and
wrap-chain kernels equal at this seat for the quad
channels; the matrices below are the per-quad-type kernels.

**Excess = raw at this seat**, as at (C₃, χ): every
order-7 fully-split baseline carries a positive power of
`e₁ = E χ_std`, and `E χ_std = 0` at this seat (the
Python table's e1 check, and the mechanism of the β⁵
probe at this seat), so every excess equals its raw
channel sum.

**The A3-gated nuance (on the record from BR1-008;
certified here, not smoothed).**  The two orbit-pair
channels — `(2,1,1,1,1,1)` on `Θ(2,2,2)` and the `(1⁷)`
book on `Θ(1,3,3)` — do **not** factor through the plain
product class `cls(g₃·g₅)` (resp. `cls(Lₐ·L_b)`): the
run log's entry `(0, 4)` exhibits the failure (orbit `0`
is `(id, id)`, orbit `4` is `((12), (12))`; the kernel
vanishes there while the plain-product reading would
force the `(0, 0)` value).  The exact factorization is
through the **A3-gated product class**: the product's
class on orbits whose two loop holonomies are both even,
and κ₄'s zero class (the transposition class, index `1`)
otherwise (`gatePair` below; theorems
`K7S3Theta_gated`, `K7S3Book_gated`, and the plain
reading's failure `K7S3Theta_not_plain`,
`K7S3Book_not_plain`).  The kernel-reading convention is
the B6-PROBE-c frame (constants; `span{1, sgn}` per even
cycle; the joint span `span{1, s₁, s₂, s₁s₂}`): every
candidate reading restricts to zero, so the verdict is
**convention-independent** — stated in the verdict
theorems, not assumed.

**K-K7 was armed** at this seat exactly as at (C₃, χ):
a certified negative value of any new channel on `K₆`
would have landed the kill at full rank.  None occurs:
every channel vanishes on `K₆`, **K-K7 does not fire at
this seat**, and the β⁷ decision at the seats passes to
β⁸ (see the assembled verdict `verdict_B7Probe`).  β⁸ is
not queued; the regress has no internal stop — that is
stated, not softened.

**Interpretation cap (on the face)**: the multiples in
the table are seat data — exact values of these channel
forms at this one seat — not mechanism evidence.  No
mechanism for the general β⁷ sign is asserted or
suggested by the pattern of multiples.
-/

section B7S3Kappa4

/-- **Kernel characterization at (S₃, std), re-derived
in this module.**  The κ₄ seat form is consumed as
exported (`K4S3` / `nS3` from the β⁵ probe); here its
diagonal form is re-derived from its square form
`formS3_k4_sq`: the form vanishes exactly on
`{φ : Fin 3 → ℚ | φ 0 = φ 2}`. -/
theorem kappa4S3_kernel_B7 (φ : Fin 3 → ℚ) :
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

/-- **Seat-`K₆` re-derivation at (S₃, std).**  `K₆` is
`ker κ₄^dep ∩ ker κ₅^dep ∩ ker κ₆^dep` (diagonal forms).
At this seat the κ₅ channel form vanishes on
`ker κ₄^dep` (it is `4 ×` the κ₄ kernel, B5-PROBE:
`verdict_S3`), and every κ₆ channel form vanishes there
too (`verdict_S3_B6`, consumed as landed, the Θ channel
under its joint-span convention).  Hence seat-`K₆` =
`ker κ₄^dep`, which is exactly `{φ₀ = φ₂}` by
`kappa4S3_kernel_B7`.  This theorem certifies the
κ₅/κ₆ half of that identification in-module: from
`φ ∈ ker κ₄^dep`, the κ₅ form and all five κ₆ channel
forms of `verdict_S3_B6` vanish at `φ`. -/
theorem seatK6_S3 (φ : Fin 3 → ℚ)
    (h4 : ∑ a, ∑ b, φ a * (nS3 a * K4S3 a b * nS3 b) * φ b = 0) :
    (φ 0 = φ 2)
      ∧ (∑ a, ∑ b, φ a * (nS3 a * K5S3 a b * nS3 b) * φ b = 0)
      ∧ (∑ a, ∑ b, φ a * (nS3 a * K6S3_3111 a b * nS3 b) * φ b = 0)
      ∧ (∑ a, ∑ b, φ a * (nS3 a * K6S3_2211adj a b * nS3 b) * φ b = 0)
      ∧ (∑ a, ∑ b, φ a * (nS3 a * K6S3_2211opp a b * nS3 b) * φ b = 0)
      ∧ (∑ a, ∑ b, φ a * (nS3 a * K6S3_C6 a b * nS3 b) * φ b = 0)
      ∧ (∀ ψ : Fin 11 → ℚ,
          (∃ a b c d : ℚ, ψ = fun p => a + b * s1Theta p
            + c * s2Theta p + d * s12Theta p) →
          (∑ p, ∑ q, ψ p * (nThetaS3 p * K6S3Theta p q * nThetaS3 q)
            * ψ q) = 0) :=
  ⟨(kappa4S3_kernel_B7 φ).mp h4, verdict_S3 φ h4, verdict_S3_B6 φ h4⟩

end B7S3Kappa4

section B7S3Quad4111

/-- The `(4,1,1,1)` channel seat kernel at (S₃, std):
the per-support-type enumeration matrix of the Python
table (BR1-008), `[5, 0, -5/2; 0, 0, 0; -5/2, 0, 5/4]`
(plaquette and wrap-chain kernels equal). -/
def K7S3_4111 : Matrix (Fin 3) (Fin 3) ℚ :=
  ![![5, 0, -5 / 2], ![0, 0, 0], ![-5 / 2, 0, 5 / 4]]

/-- **Proportionality, `(4,1,1,1)` at (S₃, std):
exactly `20 ×` the κ₄ kernel** (Python target:
`[5, 0, -5/2; …] = 20 · [1/4, 0, -1/8; …]`). -/
theorem K7S3_4111_prop (a b : Fin 3) :
    K7S3_4111 a b = 20 * K4S3 a b := by
  fin_cases a <;> fin_cases b <;> simp [K7S3_4111, K4S3,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three] <;> norm_num

/-- `(4,1,1,1)` kernel margins vanish exactly. -/
theorem K7S3_4111_margins (a : Fin 3) :
    ∑ b, nS3 b * K7S3_4111 a b = 0 := by
  fin_cases a <;> rw [Fin.sum_univ_three] <;> simp [K7S3_4111, nS3,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three] <;> norm_num

/-- The `(4,1,1,1)` diagonal form at (S₃, std) is
exactly `20 ×` the κ₄ diagonal form. -/
theorem formS3_k7_4111 (φ : Fin 3 → ℚ) :
    (∑ a, ∑ b, φ a * (nS3 a * K7S3_4111 a b * nS3 b) * φ b)
      = 20 * ∑ a, ∑ b, φ a * (nS3 a * K4S3 a b * nS3 b) * φ b := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [K7S3_4111_prop]
  ring

end B7S3Quad4111

section B7S3Quad3211

/-- The `(3,2,1,1)`-**adjacent** channel seat kernel
at (S₃, std): the per-support-type enumeration matrix
of the Python table (BR1-008),
`[6, 0, -3; 0, 0, 0; -3, 0, 3/2]` (plaquette and
wrap-chain kernels equal). -/
def K7S3_3211adj : Matrix (Fin 3) (Fin 3) ℚ :=
  ![![6, 0, -3], ![0, 0, 0], ![-3, 0, 3 / 2]]

/-- **Proportionality, `(3,2,1,1)`-adjacent at
(S₃, std): exactly `24 ×` the κ₄ kernel.** -/
theorem K7S3_3211adj_prop (a b : Fin 3) :
    K7S3_3211adj a b = 24 * K4S3 a b := by
  fin_cases a <;> fin_cases b <;> simp [K7S3_3211adj, K4S3,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three] <;> norm_num

/-- `(3,2,1,1)`-adjacent kernel margins vanish
exactly. -/
theorem K7S3_3211adj_margins (a : Fin 3) :
    ∑ b, nS3 b * K7S3_3211adj a b = 0 := by
  fin_cases a <;> rw [Fin.sum_univ_three] <;> simp [K7S3_3211adj, nS3,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three] <;> norm_num

/-- The `(3,2,1,1)`-adjacent diagonal form at (S₃, std)
is exactly `24 ×` the κ₄ diagonal form. -/
theorem formS3_k7_3211adj (φ : Fin 3 → ℚ) :
    (∑ a, ∑ b, φ a * (nS3 a * K7S3_3211adj a b * nS3 b) * φ b)
      = 24 * ∑ a, ∑ b, φ a * (nS3 a * K4S3 a b * nS3 b) * φ b := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [K7S3_3211adj_prop]
  ring

/-- The `(3,2,1,1)`-**opposite** channel seat kernel
at (S₃, std): the per-support-type enumeration matrix
of the Python table (BR1-008),
`[3, 0, -3/2; 0, 0, 0; -3/2, 0, 3/4]` (plaquette and
wrap-chain kernels equal). -/
def K7S3_3211opp : Matrix (Fin 3) (Fin 3) ℚ :=
  ![![3, 0, -3 / 2], ![0, 0, 0], ![-3 / 2, 0, 3 / 4]]

/-- **Proportionality, `(3,2,1,1)`-opposite at
(S₃, std): exactly `12 ×` the κ₄ kernel.** -/
theorem K7S3_3211opp_prop (a b : Fin 3) :
    K7S3_3211opp a b = 12 * K4S3 a b := by
  fin_cases a <;> fin_cases b <;> simp [K7S3_3211opp, K4S3,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three] <;> norm_num

/-- `(3,2,1,1)`-opposite kernel margins vanish
exactly. -/
theorem K7S3_3211opp_margins (a : Fin 3) :
    ∑ b, nS3 b * K7S3_3211opp a b = 0 := by
  fin_cases a <;> rw [Fin.sum_univ_three] <;> simp [K7S3_3211opp, nS3,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three] <;> norm_num

/-- The `(3,2,1,1)`-opposite diagonal form at (S₃, std)
is exactly `12 ×` the κ₄ diagonal form. -/
theorem formS3_k7_3211opp (φ : Fin 3 → ℚ) :
    (∑ a, ∑ b, φ a * (nS3 a * K7S3_3211opp a b * nS3 b) * φ b)
      = 12 * ∑ a, ∑ b, φ a * (nS3 a * K4S3 a b * nS3 b) * φ b := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [K7S3_3211opp_prop]
  ring

end B7S3Quad3211

section B7S3Quad2221

/-- The `(2,2,2,1)` channel seat kernel at (S₃, std):
the per-support-type enumeration matrix of the Python
table (BR1-008), `[6, 0, -3; 0, 0, 0; -3, 0, 3/2]`
(plaquette and wrap-chain kernels equal). -/
def K7S3_2221 : Matrix (Fin 3) (Fin 3) ℚ :=
  ![![6, 0, -3], ![0, 0, 0], ![-3, 0, 3 / 2]]

/-- **Proportionality, `(2,2,2,1)` at (S₃, std):
exactly `24 ×` the κ₄ kernel.** -/
theorem K7S3_2221_prop (a b : Fin 3) :
    K7S3_2221 a b = 24 * K4S3 a b := by
  fin_cases a <;> fin_cases b <;> simp [K7S3_2221, K4S3,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three] <;> norm_num

/-- `(2,2,2,1)` kernel margins vanish exactly. -/
theorem K7S3_2221_margins (a : Fin 3) :
    ∑ b, nS3 b * K7S3_2221 a b = 0 := by
  fin_cases a <;> rw [Fin.sum_univ_three] <;> simp [K7S3_2221, nS3,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three] <;> norm_num

/-- The `(2,2,2,1)` diagonal form at (S₃, std) is
exactly `24 ×` the κ₄ diagonal form. -/
theorem formS3_k7_2221 (φ : Fin 3 → ℚ) :
    (∑ a, ∑ b, φ a * (nS3 a * K7S3_2221 a b * nS3 b) * φ b)
      = 24 * ∑ a, ∑ b, φ a * (nS3 a * K4S3 a b * nS3 b) * φ b := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [K7S3_2221_prop]
  ring

end B7S3Quad2221

section B7S3C6Doubled

/-- The `(2,1,1,1,1,1)` channel seat kernel on `C6`
supports at (S₃, std): the enumeration matrix of the
Python table (BR1-008),
`[3/8, 0, -3/16; 0, 0, 0; -3/16, 0, 3/32]` (the doubled
6-cycle's holonomy-class kernel).  Its fiber counts
`[7776, 23328, 15552]` are exactly `36 × nS3`, as for
the order-6 `C6` channel, so the diagonal form below
is carried with the `nS3` weights of the other channels
at this seat: the kernel matrix and its proportionality
are the Python values exactly, and the form's zero set
is unchanged by the constant fiber rescaling. -/
def K7S3_211111C6 : Matrix (Fin 3) (Fin 3) ℚ :=
  ![![3 / 8, 0, -3 / 16], ![0, 0, 0], ![-3 / 16, 0, 3 / 32]]

/-- **Proportionality, `(2,1,1,1,1,1)` on `C6` at
(S₃, std): exactly `(3/2) ×` the κ₄ kernel.** -/
theorem K7S3_211111C6_prop (a b : Fin 3) :
    K7S3_211111C6 a b = (3 / 2) * K4S3 a b := by
  fin_cases a <;> fin_cases b <;> simp [K7S3_211111C6, K4S3,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three] <;> norm_num

/-- `(2,1,1,1,1,1)`-on-`C6` kernel margins vanish
exactly. -/
theorem K7S3_211111C6_margins (a : Fin 3) :
    ∑ b, nS3 b * K7S3_211111C6 a b = 0 := by
  fin_cases a <;> rw [Fin.sum_univ_three] <;> simp [K7S3_211111C6, nS3,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three] <;> norm_num

/-- The `(2,1,1,1,1,1)`-on-`C6` diagonal form at
(S₃, std) is exactly `(3/2) ×` the κ₄ diagonal form
(in the `nS3` fiber weights; see `K7S3_211111C6`). -/
theorem formS3_k7_211111C6 (φ : Fin 3 → ℚ) :
    (∑ a, ∑ b, φ a * (nS3 a * K7S3_211111C6 a b * nS3 b) * φ b)
      = (3 / 2) * ∑ a, ∑ b, φ a * (nS3 a * K4S3 a b * nS3 b) * φ b := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [K7S3_211111C6_prop]
  ring

end B7S3C6Doubled

section B7S3ThetaDoubled

/-- The **A3-gated product class** on Θ/book orbit
profiles at (S₃, std): for the orbit representative
pair `(g, h)` (the β⁶ probe's `thetaRepS3`, shared by
the Θ and book orbit spaces), the class of the product
`g · h` when both loop holonomies are even, and the
zero class of κ₄ — the transposition class, index `1`,
whose κ₄ row and column vanish — otherwise.  Evaluated
on the representatives: the gated labels are
`[0, 1, 2, 1, 1, 1, 1, 2, 1, 2, 0]`; the gate bites
exactly at orbit `4 = ((12), (12))`, where the plain
product class is `0` (the product is the identity) but
the gated class is `1`. -/
def gatePair : Fin 11 → Fin 3 :=
  ![0, 1, 2, 1, 1, 1, 1, 2, 1, 2, 0]

/-- The **plain product class** on orbit profiles:
`cls(g · h)` of the representative pair, with no gate:
`[0, 1, 2, 1, 0, 2, 1, 2, 1, 2, 0]`.  It agrees with
`gatePair` except at orbit `4`. -/
def plainProdPair : Fin 11 → Fin 3 :=
  ![0, 1, 2, 1, 0, 2, 1, 2, 1, 2, 0]

/-- The `(2,1,1,1,1,1)` channel orbit kernel on
`Θ(2,2,2)` supports at (S₃, std): the enumeration
matrix of the Python table (BR1-008; 11 orbits, the
β⁶ probe's orbit representatives and fiber counts
`nThetaS3`; nonzero only on the five support orbits
`0, 2, 7, 9, 10`). -/
def K7S3Theta : Matrix (Fin 11) (Fin 11) ℚ :=
  ![![3 / 4, 0, -3 / 8, 0, 0, 0, 0, -3 / 8, 0, -3 / 8, 3 / 4],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-3 / 8, 0, 3 / 16, 0, 0, 0, 0, 3 / 16, 0, 3 / 16, -3 / 8],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-3 / 8, 0, 3 / 16, 0, 0, 0, 0, 3 / 16, 0, 3 / 16, -3 / 8],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-3 / 8, 0, 3 / 16, 0, 0, 0, 0, 3 / 16, 0, 3 / 16, -3 / 8],
    ![3 / 4, 0, -3 / 8, 0, 0, 0, 0, -3 / 8, 0, -3 / 8, 3 / 4]]

/-- **Doubled-Θ outer factorization:** the orbit kernel
is `(3/16) • m mᵀ` entrywise, with the β⁶ probe's factor
`m = (2, 0, -1, 0, 0, 0, 0, -1, 0, -1, 2)` — six times
the order-6 Θ kernel `(1/32) • m mᵀ`. -/
theorem K7S3Theta_outer (p q : Fin 11) :
    K7S3Theta p q = (3 / 16) * (mThetaS3 p * mThetaS3 q) := by
  fin_cases p <;> fin_cases q <;>
    simp [K7S3Theta, mThetaS3] <;> norm_num

/-- **A3-gated factorization, `(2,1,1,1,1,1)` on
`Θ(2,2,2)` at (S₃, std): exactly `3 ×` the κ₄ kernel
read through the A3-gated product class** (BR1-008:
`K[a][b] = 3 · κ₄[gate(a)][gate(b)]` entrywise, the
Python side's verified factorization).  On the five
support orbits both loops are even and the gate is the
plain product class; on every other orbit the gated
class is `1`, whose κ₄ row vanishes, matching the
kernel's support. -/
theorem K7S3Theta_gated (p q : Fin 11) :
    K7S3Theta p q = 3 * K4S3 (gatePair p) (gatePair q) := by
  fin_cases p <;> fin_cases q <;> simp [K7S3Theta, gatePair, K4S3,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three] <;> norm_num

/-- **The plain product class does NOT factor the
doubled-Θ kernel** (BR1-008, run-log entry `(0, 4)`):
there is no scalar `c` with
`K p q = c · κ₄[cls(g·h)(p)][cls(g·h)(q)]` for all
orbits `p, q`.  At `(0, 0)` any such `c` is forced to
`3` (the kernel is `3/4 = c · (1/4)`), but at `(0, 4)`
— orbit `4`'s representative is `((12), (12))`, whose
product is the identity, plain class `0` — the plain
reading would give `c · κ₄[0][0] = 3/4` while the
kernel is exactly `0`.  The same argument with the
forced scalar read off `(0, 0)` also kills the
`g · h⁻¹` plain reading, whose label at orbit `4` is
likewise `0`. -/
theorem K7S3Theta_not_plain :
    ¬ ∃ c : ℚ, ∀ p q, K7S3Theta p q
      = c * K4S3 (plainProdPair p) (plainProdPair q) := by
  rintro ⟨c, hc⟩
  have h00 := hc 0 0
  have h04 := hc 0 4
  have e00 : K7S3Theta 0 0 = 3 / 4 := by
    rw [K7S3Theta_outer]; simp [mThetaS3]; norm_num
  have e04 : K7S3Theta 0 4 = 0 := by
    rw [K7S3Theta_outer]; simp [mThetaS3]
  have eP0 : plainProdPair 0 = 0 := by simp [plainProdPair]
  have eP4 : plainProdPair 4 = 0 := by simp [plainProdPair]
  have eK : K4S3 0 0 = 1 / 4 := by
    simp [K4S3, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
  rw [e00, eP0, eK] at h00
  rw [e04, eP0, eP4, eK] at h04
  linarith

/-- Doubled-Θ kernel margins vanish exactly
(fiber-weighted): each row pairs against the constant
profile's linear form `LThetaS3`, which is `0` (the
linear form is the β⁶ probe's: same fibers `nThetaS3`,
same factor `mThetaS3`). -/
theorem K7S3Theta_margins (p : Fin 11) :
    ∑ q, nThetaS3 q * K7S3Theta p q = 0 := by
  have e : ∑ q, nThetaS3 q * K7S3Theta p q
      = (3 / 16) * mThetaS3 p * LThetaS3 (fun _ => 1) := by
    rw [LThetaS3, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [K7S3Theta_outer]
    ring
  rw [e, LThetaS3_const]
  norm_num

/-- The doubled-Θ diagonal form at (S₃, std) is
`(3/16)` times the square of the Θ linear form. -/
theorem formS3_k7_Theta (ψ : Fin 11 → ℚ) :
    (∑ p, ∑ q, ψ p * (nThetaS3 p * K7S3Theta p q * nThetaS3 q) * ψ q)
      = (3 / 16) * (LThetaS3 ψ) ^ 2 := by
  have e : (∑ p, ∑ q, ψ p * (nThetaS3 p * K7S3Theta p q * nThetaS3 q) * ψ q)
      = (3 / 16) * ∑ p, ∑ q, (ψ p * nThetaS3 p * mThetaS3 p)
          * (ψ q * nThetaS3 q * mThetaS3 q) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [K7S3Theta_outer]
    ring
  rw [e, LThetaS3, pow_two, Fintype.sum_mul_sum]

/-- **Doubled-Θ verdict at (S₃, std):** the diagonal
form vanishes on every orbit profile in the joint
candidate span `span{1, s₁, s₂, s₁s₂}` (the B6-PROBE-c
convention, the largest candidate reading) — hence
under every candidate sub-reading (constants alone, or
constants with any one of the three sign pullbacks):
the verdict for this channel is
**convention-independent**. -/
theorem K7S3Theta_form_eq_zero_of_span (ψ : Fin 11 → ℚ)
    (hψ : ∃ a b c d : ℚ, ψ = fun p => a + b * s1Theta p
      + c * s2Theta p + d * s12Theta p) :
    (∑ p, ∑ q, ψ p * (nThetaS3 p * K7S3Theta p q * nThetaS3 q)
      * ψ q) = 0 := by
  rw [formS3_k7_Theta, LThetaS3_eq_zero_of_span ψ hψ]
  norm_num

end B7S3ThetaDoubled

section B7S3Book

/-- The Θ(1,3,3) book orbit fiber counts at (S₃, std),
in the Python table's orbit order (BR1-008): exactly
`6 ×` the Θ(2,2,2) fiber counts `nThetaS3` (the book
orbit space is the same pair-orbit space, with the
book's own loop holonomies `Lₐ, L_b` in place of
`g₃, g₅`). -/
def nBookS3 : Fin 11 → ℚ :=
  ![7776, 23328, 15552, 23328, 23328, 46656, 46656, 15552,
    46656, 15552, 15552]

theorem nBookS3_eq (p : Fin 11) : nBookS3 p = 6 * nThetaS3 p := by
  fin_cases p <;> simp [nBookS3, nThetaS3] <;> norm_num

/-- The `(1⁷)` book channel orbit kernel on `Θ(1,3,3)`
supports at (S₃, std): the enumeration matrix of the
Python table (BR1-008; 11 orbits; nonzero only on the
five support orbits `0, 2, 7, 9, 10`). -/
def K7S3Book : Matrix (Fin 11) (Fin 11) ℚ :=
  ![![1 / 16, 0, -1 / 32, 0, 0, 0, 0, -1 / 32, 0, -1 / 32, 1 / 16],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-1 / 32, 0, 1 / 64, 0, 0, 0, 0, 1 / 64, 0, 1 / 64, -1 / 32],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-1 / 32, 0, 1 / 64, 0, 0, 0, 0, 1 / 64, 0, 1 / 64, -1 / 32],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-1 / 32, 0, 1 / 64, 0, 0, 0, 0, 1 / 64, 0, 1 / 64, -1 / 32],
    ![1 / 16, 0, -1 / 32, 0, 0, 0, 0, -1 / 32, 0, -1 / 32, 1 / 16]]

/-- **Book outer factorization:** the orbit kernel is
`(1/64) • m mᵀ` entrywise, with the same factor
`m = (2, 0, -1, 0, 0, 0, 0, -1, 0, -1, 2)` as the Θ
kernels at this seat — half the order-6 Θ kernel
`(1/32) • m mᵀ`. -/
theorem K7S3Book_outer (p q : Fin 11) :
    K7S3Book p q = (1 / 64) * (mThetaS3 p * mThetaS3 q) := by
  fin_cases p <;> fin_cases q <;>
    simp [K7S3Book, mThetaS3] <;> norm_num

/-- **A3-gated factorization, `(1⁷)` book at (S₃, std):
exactly `(1/4) ×` the κ₄ kernel read through the
A3-gated product class** (BR1-008:
`K[a][b] = (1/4) · κ₄[gate(a)][gate(b)]` entrywise,
with the gate on the book's loop holonomies `Lₐ, L_b`:
the product's class when both are even, κ₄'s zero
class `1` otherwise — the same `gatePair` labels, the
orbit representatives being shared). -/
theorem K7S3Book_gated (p q : Fin 11) :
    K7S3Book p q = (1 / 4) * K4S3 (gatePair p) (gatePair q) := by
  fin_cases p <;> fin_cases q <;> simp [K7S3Book, gatePair, K4S3,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three] <;> norm_num

/-- **The plain product class does NOT factor the book
kernel** (BR1-008, run-log entry `(0, 4)`): there is no
scalar `c` with
`K p q = c · κ₄[cls(Lₐ·L_b)(p)][cls(Lₐ·L_b)(q)]` for
all orbits `p, q`.  At `(0, 0)` any such `c` is forced
to `1/4` (the kernel is `1/16 = c · (1/4)`), but at
`(0, 4)` the plain reading would give
`c · κ₄[0][0] = 1/16` while the kernel is exactly `0`.
The same argument kills the `Lₐ · L_b⁻¹` plain reading,
whose label at orbit `4` is likewise `0`. -/
theorem K7S3Book_not_plain :
    ¬ ∃ c : ℚ, ∀ p q, K7S3Book p q
      = c * K4S3 (plainProdPair p) (plainProdPair q) := by
  rintro ⟨c, hc⟩
  have h00 := hc 0 0
  have h04 := hc 0 4
  have e00 : K7S3Book 0 0 = 1 / 16 := by
    rw [K7S3Book_outer]; simp [mThetaS3]; norm_num
  have e04 : K7S3Book 0 4 = 0 := by
    rw [K7S3Book_outer]; simp [mThetaS3]
  have eP0 : plainProdPair 0 = 0 := by simp [plainProdPair]
  have eP4 : plainProdPair 4 = 0 := by simp [plainProdPair]
  have eK : K4S3 0 0 = 1 / 4 := by
    simp [K4S3, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
  rw [e00, eP0, eK] at h00
  rw [e04, eP0, eP4, eK] at h04
  linarith

/-- The book linear form: the fiber-weighted pairing
of an orbit profile against the kernel's factor `m`,
with the book's own fibers `nBookS3`. -/
def LBookS3 (ψ : Fin 11 → ℚ) : ℚ :=
  ∑ p, ψ p * nBookS3 p * mThetaS3 p

/-- The book linear form is exactly `6 ×` the Θ linear
form (the book fibers are `6 ×` the Θ fibers). -/
theorem LBookS3_eq (ψ : Fin 11 → ℚ) :
    LBookS3 ψ = 6 * LThetaS3 ψ := by
  rw [LBookS3, LThetaS3, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [nBookS3_eq]
  ring

/-- Book kernel margins vanish exactly
(fiber-weighted). -/
theorem K7S3Book_margins (p : Fin 11) :
    ∑ q, nBookS3 q * K7S3Book p q = 0 := by
  have e : ∑ q, nBookS3 q * K7S3Book p q
      = (1 / 64) * mThetaS3 p * LBookS3 (fun _ => 1) := by
    rw [LBookS3, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [K7S3Book_outer]
    ring
  rw [e, LBookS3_eq, LThetaS3_const]
  norm_num

/-- The book diagonal form at (S₃, std) is `(1/64)`
times the square of its linear form. -/
theorem formS3_k7_Book (ψ : Fin 11 → ℚ) :
    (∑ p, ∑ q, ψ p * (nBookS3 p * K7S3Book p q * nBookS3 q) * ψ q)
      = (1 / 64) * (LBookS3 ψ) ^ 2 := by
  have e : (∑ p, ∑ q, ψ p * (nBookS3 p * K7S3Book p q * nBookS3 q) * ψ q)
      = (1 / 64) * ∑ p, ∑ q, (ψ p * nBookS3 p * mThetaS3 p)
          * (ψ q * nBookS3 q * mThetaS3 q) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [K7S3Book_outer]
    ring
  rw [e, LBookS3, pow_two, Fintype.sum_mul_sum]

/-- **Book verdict at (S₃, std):** the diagonal form
vanishes on every orbit profile in the joint candidate
span `span{1, s₁, s₂, s₁s₂}` (the largest candidate
reading for the book's orbit space, the sign pullbacks
read on the book's loop holonomies) — hence under every
candidate sub-reading: the verdict for this channel is
**convention-independent**. -/
theorem K7S3Book_form_eq_zero_of_span (ψ : Fin 11 → ℚ)
    (hψ : ∃ a b c d : ℚ, ψ = fun p => a + b * s1Theta p
      + c * s2Theta p + d * s12Theta p) :
    (∑ p, ∑ q, ψ p * (nBookS3 p * K7S3Book p q * nBookS3 q)
      * ψ q) = 0 := by
  rw [formS3_k7_Book, LBookS3_eq, LThetaS3_eq_zero_of_span ψ hψ]
  norm_num

end B7S3Book

section B7S3Verdict

/-- **Joint verdict at (S₃, std), N = 4 (K-K7 check,
B7-PROBE-c).**  For every observable `φ` in the joint
kernel `K₆` — certified here by `φ` lying in the kernel
of the κ₄ diagonal form, which is the whole joint
kernel at this seat (`seatK6_S3`: exactly `{φ₀ = φ₂}`;
the κ₅ channel is proportional to κ₄ at this seat,
B5-PROBE, and every κ₆ channel vanishes on it,
B6-PROBE) — **every** β⁷ channel's diagonal form at
`φ` is exactly `0`: the `(4,1,1,1)` form (`20 × κ₄`),
the `(3,2,1,1)`-adjacent form (`24 × κ₄`), the
`(3,2,1,1)`-opposite form (`12 × κ₄`), the `(2,2,2,1)`
form (`24 × κ₄`), the `(2,1,1,1,1,1)` form on `C6`
supports (`(3/2) × κ₄`), the `(2,1,1,1,1,1)` form on
`Θ(2,2,2)` supports on every orbit profile in the
joint candidate span `span{1, s₁, s₂, s₁s₂}`, and the
`(1⁷)` book form on `Θ(1,3,3)` supports on every orbit
profile in the joint candidate span.  For the two
orbit-pair channels the factorization is exactly the
**A3-gated** one (`K7S3Theta_gated`, `K7S3Book_gated`;
the plain product class does not factor them,
`K7S3Theta_not_plain`, `K7S3Book_not_plain`), and their
vanishing holds under **every** candidate kernel
reading, so it is convention-independent.  No channel
is negative on `K₆`; all vanish identically; **K-K7
does not fire at (S₃, std)**, and the
degenerate-perturbation regress continues past β⁷ at
this seat.  Seat scope only; no general sign is
asserted, and the multiples are seat data, not
mechanism evidence. -/
theorem verdict_S3_B7 (φ : Fin 3 → ℚ)
    (h4 : ∑ a, ∑ b, φ a * (nS3 a * K4S3 a b * nS3 b) * φ b = 0) :
    (∑ a, ∑ b, φ a * (nS3 a * K7S3_4111 a b * nS3 b) * φ b = 0)
      ∧ (∑ a, ∑ b, φ a * (nS3 a * K7S3_3211adj a b * nS3 b) * φ b = 0)
      ∧ (∑ a, ∑ b, φ a * (nS3 a * K7S3_3211opp a b * nS3 b) * φ b = 0)
      ∧ (∑ a, ∑ b, φ a * (nS3 a * K7S3_2221 a b * nS3 b) * φ b = 0)
      ∧ (∑ a, ∑ b, φ a * (nS3 a * K7S3_211111C6 a b * nS3 b) * φ b = 0)
      ∧ (∀ ψ : Fin 11 → ℚ,
          (∃ a b c d : ℚ, ψ = fun p => a + b * s1Theta p
            + c * s2Theta p + d * s12Theta p) →
          (∑ p, ∑ q, ψ p * (nThetaS3 p * K7S3Theta p q * nThetaS3 q)
            * ψ q) = 0)
      ∧ (∀ ψ : Fin 11 → ℚ,
          (∃ a b c d : ℚ, ψ = fun p => a + b * s1Theta p
            + c * s2Theta p + d * s12Theta p) →
          (∑ p, ∑ q, ψ p * (nBookS3 p * K7S3Book p q * nBookS3 q)
            * ψ q) = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [formS3_k7_4111, h4]; norm_num
  · rw [formS3_k7_3211adj, h4]; norm_num
  · rw [formS3_k7_3211opp, h4]; norm_num
  · rw [formS3_k7_2221, h4]; norm_num
  · rw [formS3_k7_211111C6, h4]; norm_num
  · intro ψ hψ
    exact K7S3Theta_form_eq_zero_of_span ψ hψ
  · intro ψ hψ
    exact K7S3Book_form_eq_zero_of_span ψ hψ

end B7S3Verdict

section B7JointVerdict

/-- **β⁷ probe headline verdict (B7-PROBE, both seats,
registry BR1-008).**  At both seats — (C₃, χ) by
`verdict_C3_B7` (part 1) and (S₃, std) by
`verdict_S3_B7` (part 2, with the two orbit-pair
channels read under the A3-gated factorization and
vanishing under every candidate kernel reading, hence
convention-independently) — every new order-7 channel's
diagonal form vanishes identically on the joint kernel
`K₆ = ker κ₄^dep ∩ ker κ₅^dep ∩ ker κ₆^dep`, which at
both seats equals `ker κ₄^dep` (constants at (C₃, χ);
`{φ₀ = φ₂}` at (S₃, std); `seatK6_C3`, `seatK6_S3`).
Per the pre-registered outcome table (β⁷ scoping,
2026-10-29, §2) the outcome is **(ii) certified: every
order-7 channel vanishes on `K₆` at both seats; K-K7
does NOT fire at either seat; the β⁷ decision at the
seats passes to β⁸.**  β⁸ is not queued, and the regress
has **no internal stop**: short of a `K-Kn` kill at some
later order, only an external event ends it — a general
mechanism or 𝒜 ⪰ 0 proved directly.  That is stated
here, not softened.  Seat scope only (N = 4, the two
seats); nothing general about 𝒜 or the β⁷ sign is
asserted: the β⁷ general sign stays FRONTIER, the
multiples are seat data and not mechanism evidence, the
𝒜 ⪰ 0 core is untouched by this verdict in either
direction, NO CLAIM, parts of the Clay statement closed
**0**, dials 0/4. -/
theorem verdict_B7Probe (φ : ZMod 3 → ℚ)
    (h4C : ∑ a, ∑ b, φ a * K4C3 a b * φ b = 0)
    (ψ : Fin 3 → ℚ)
    (h4S : ∑ a, ∑ b, ψ a * (nS3 a * K4S3 a b * nS3 b) * ψ b = 0) :
    ((∑ a, ∑ b, φ a * K7C3_4111 a b * φ b = 0)
      ∧ (∑ a, ∑ b, φ a * K7C3_3211adj a b * φ b = 0)
      ∧ (∑ a, ∑ b, φ a * K7C3_3211opp a b * φ b = 0)
      ∧ (∑ a, ∑ b, φ a * K7C3_2221 a b * φ b = 0)
      ∧ (∑ a, ∑ b, φ a * K7C3_211111C6 a b * φ b = 0)
      ∧ (∑ p, ∑ q, (fun _ => φ 0) p * K7C3_211111Theta p q
          * (fun _ => φ 0) q = 0)
      ∧ (∑ p, ∑ q, (fun _ => φ 0) p * K7C3_Theta133 p q
          * (fun _ => φ 0) q = 0))
    ∧ ((∑ a, ∑ b, ψ a * (nS3 a * K7S3_4111 a b * nS3 b) * ψ b = 0)
      ∧ (∑ a, ∑ b, ψ a * (nS3 a * K7S3_3211adj a b * nS3 b) * ψ b = 0)
      ∧ (∑ a, ∑ b, ψ a * (nS3 a * K7S3_3211opp a b * nS3 b) * ψ b = 0)
      ∧ (∑ a, ∑ b, ψ a * (nS3 a * K7S3_2221 a b * nS3 b) * ψ b = 0)
      ∧ (∑ a, ∑ b, ψ a * (nS3 a * K7S3_211111C6 a b * nS3 b) * ψ b = 0)
      ∧ (∀ θ : Fin 11 → ℚ,
          (∃ a b c d : ℚ, θ = fun p => a + b * s1Theta p
            + c * s2Theta p + d * s12Theta p) →
          (∑ p, ∑ q, θ p * (nThetaS3 p * K7S3Theta p q * nThetaS3 q)
            * θ q) = 0)
      ∧ (∀ θ : Fin 11 → ℚ,
          (∃ a b c d : ℚ, θ = fun p => a + b * s1Theta p
            + c * s2Theta p + d * s12Theta p) →
          (∑ p, ∑ q, θ p * (nBookS3 p * K7S3Book p q * nBookS3 q)
            * θ q) = 0)) :=
  ⟨verdict_C3_B7 φ h4C, verdict_S3_B7 ψ h4S⟩

end B7JointVerdict

end ThetLogos
