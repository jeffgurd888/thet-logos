# BR1-029 (candidate) — K-CLS-1a conjugation-route commutant probe (Dial-1 lane)

Date: 2026-11-02. Registration: CLS-1a/1b scoping memo
(`routeb-general-scratch/scoping-cls1ab-2026-11-02.md` §1.5 — binding).
Pack: `routeb-general-scratch/pack-br1-029-probe.md`.
Script: `br1029-probe.py`; output: `br1029-probe-out.txt`
(python3, `Fraction` / Gaussian-rational arithmetic only — **no floats**;
no Lean files touched, no builds).

**Registry entry (BR1-028 form).** BR1-029 (candidate) — the K-CLS-1a
conjugation route (scoping §1.5): commutant of {gammaF, D_nu, D_e, D_u,
D_d, J-intertwining} computed EXACTLY at **generic Yukawa values**
(channel coefficient matrices extracted from the landed `DF_oneGen`).
Commutant dimension **80** over ℂ for (a)∧(c) (gammaF + four channels),
**40** with J-intertwining adjoined as the linear generator `UJ`
([X, UJ] = 0). Seat-mixing support is identical in both: all ordered
pairs inside one channel group and one γ-sign class, nothing else.
The named candidate pair **(8, 9) / (9, 8) is NOT mixable** — it is
zero-forced already by (a)∧(c) (seats 8, 9 lie in different channel
groups). BUT the route is **LIVE**: an explicit rational orthogonal
(unitary) U in the full commutant, satisfying the true piOp
intertwining identity (μ = 1, verified below), mixes seats **2 ↔ 28**
and **4 ↔ 26** (V₊, lifted weights 1 vs 4) and the V₋ analogues, and
the lifted product of π_U = U π₁ U⁻¹ along (3, −1) has entry
(2, 28) = (12/25)·(x⁴ − x) as a Laurent polynomial in x = e^{it},
equal to **(12/25)(1 − i) ≠ 0 at t = π/2**. K-CLS-1a is therefore
fireable by construction **in its registered base form**
(`DialOneBase`); the strengthened-form variant is NOT addressed
(see Fences). Controls: colour mixing (2 ↔ 4, equal weights) lies in
the full commutant and cannot fire; the seat-swap S₈₉ mixes (8, 9),
is unitary, and lies OUTSIDE the commutant ([S₈₉, D_nu] ≠ 0,
[S₈₉, D_e] ≠ 0, [S₈₉, UJ] ≠ 0) — the detector sees (8, 9) mixing and
the commutant excludes it.

**NO CLAIM at T1. Dial 1: 0.** This is exact-arithmetic probe grade;
K-CLS-1a fires only when the follow-on Lean brick lands.

---

## 1. Question (registered, §1.5)

For fixed unitary U, π_U := U π₁(·) U⁻¹ stays in `DialOneBase` if U
(a) commutes with gammaF, (b) intertwines piOp
(`piOp (U M U⁻¹) = U (piOp M) U⁻¹` for all M), and (c) commutes with
each Yukawa-channel Dirac matrix D_ν, D_e, D_u, D_d **separately**
(the ∀ Ynu Ye Yu Yd quantification in clause 9). The route fires
K-CLS-1a iff this commutant contains a unitary whose conjugation
makes `liftedProd π_U` non-diagonal at a same-γ-sign seat pair of
different π₁ lifted weight (`commonWeightVector`). Named candidate
pair: (8, 9), weights 0 vs −6 (T1 `weights_eight_nine`).

## 2. Extraction (landed definitions; generic Y — NOT seated values)

Transcribed literally from the tree (`thet-logos/lean/ThetLogos/`):

- `gammaF` — `Scaffold32.lean`, `def gammaF`: diag(+1⁸, −1⁸, −1⁸, +1⁸)
  on seat blocks 0–7 / 8–15 / 16–23 / 24–31.
- `partner` — `Scaffold32.lean`: i ↦ i+16 (i<16), i−16 (i≥16);
  `UJ i j = 1 iff j = partner i`.
- `piOp` — `FiniteSpectralTriple.lean`, `def piOp`:
  `piOp M = UJ * Mᵀ * UJ`, i.e. `piOp M i j = M (partner j) (partner i)`.
- `DF_oneGen` — `FiniteSpectralTriple.lean`, `def DF_oneGen` +
  `def buildDirac`: A = diag(Ynu, Ye, Yu, Yd, Yu, Yd, Yu, Yd) (Block8),
  B = Ā, C = E = 0. Nonzero entries, for slot k = 0..7 with channel
  ch(k) = (ν, e, u, d, u, d, u, d): (k, 8+k), (8+k, k), (16+k, 24+k),
  (24+k, 16+k), each with coefficient Y_{ch(k)}.
- Weights — `commonWeightVector i = W i + W (partner i)`,
  `DialOneClassificationPin.lean`, with `W = pi1WVal`
  (`Track1RouteB.lean`). Transcription machine-checked in the script
  against T1: seats 8, 9 ↦ 0, −6 (`weights_eight_nine`); colour seats
  2, 4, 6 ↦ 1, 1, 1 (`weights_colour_equal`). Full vector:
  [−3,−3,1,1,1,1,1,1, 0,−6,4,−2,4,−2,4,−2,
   −3,−3,1,1,1,1,1,1, 0,−6,4,−2,4,−2,4,−2].

**Genericity.** DF is linear in each Y separately (no products of
Y's occur: A's diagonal entries are single Y's, B = Ā with Y real).
The script verifies exactly: DF(0) = 0, DF(unit vector of channel
ch) = D_ch for each ch, and DF(Y) = Σ_ch Y_ch·D_ch at two distinct
rational tuples. **The verdict below is at generic Yukawa values;
no seated table values were used.**

## 3. Method — exact commutant, and the form of condition (b)

All generators are monomial (entries in {−1, 0, 1}: gammaF diagonal,
each D_ch a partial involution, UJ a permutation). Hence every
commutation equation [X, G] = 0 is, entrywise, of the form X_a = X_b
or X_a = 0. The commutant is computed **exactly** by union-find over
the 1024 entry variables; dimension = number of surviving equivalence
classes. Every class-indicator basis matrix is then verified by
direct sparse `Fraction` matrix multiplication to commute with every
generator (script, asserted).

Condition (b) in its true form is the quadric
Uᵀ·UJ·U = μ·UJ (μ ≠ 0) — derived from
`piOp (U M U⁻¹) = U (piOp M) U⁻¹ ∀M` by the standard A·N·B = C·N·D
argument, and sufficient by the same algebra (μ = 1 used here). It is
therefore reported in two layers: (i) the linear commutant with
J-intertwining adjoined as the generator UJ ([X, UJ] = 0 — the
*-algebra layer, pack step 3); (ii) the exhibited unitary is verified
to satisfy the **true** ∀M identity, not merely the linear proxy:
the script checks exactly `piOp(U) = U⁻¹` and `Uᵀ UJ U = UJ`, and
`piOp(U) = U⁻¹` implies the ∀M identity via anti-multiplicativity
(T1 `piOp_mul_rev`: piOp(U M U⁻¹) = piOp(U⁻¹)·piOp(M)·piOp(U)
= U·piOp(M)·U⁻¹); two full Gaussian-rational spot checks on explicit
test matrices M are also run and pass.

## 4. Results

### 4.1 Dimensions and structure

- (a)∧(c) commutant {gammaF, D_ν, D_e, D_u, D_d}: **dimension 80**.
  Structure: seats split into the four channel groups
  ν {0,24 | 8,16}, e {1,25 | 9,17},
  u {2,4,6,26,28,30 | 10,12,14,18,20,22},
  d {3,5,7,27,29,31 | 11,13,15,19,21,23}
  (V₊ seats | V₋ seats). Per group, the V₊ block A_g is a free matrix
  (sizes 2, 2, 6, 6) and the V₋ block equals A_g read in the
  D-correspondence seat order (the channel matching is the identity
  in these orders). Dimension = 2² + 2² + 6² + 6² = 80. No cross-sign
  and no cross-group entries survive.
- With (b) as the linear generator UJ: **dimension 40**
  (per group A_g = [[P,Q],[Q,P]] in the half-split; 2 + 2 + 18 + 18).
  The seat-mixing **support pattern is unchanged**.

### 4.2 The (8, 9) answer — first, as registered

**(8, 9) and (9, 8) carry no entry of any commutant element** — in
either commutant above. Seats 8 (ν group) and 9 (e group) are
separated by clause (c) alone: commuting with D_ν and D_e separately
confines each to its own group. The named candidate pair is dead for
this route. (This is a statement about the pair, not about the route.)

### 4.3 Different-weight within-sign mixing — abundant

80 ordered off-diagonal pairs (s, s′), γ_s = γ_{s′}, w_s ≠ w_{s′},
occur in the commutant support: per group, the two halves carry
different weights (ν: −3 vs 0; e: −3 vs −6; u: 1 vs 4; d: 1 vs −2),
and every cross-half pair inside a group and sign class occurs.
First pairs: (0,24), (1,25), (2,26), (2,28), (2,30), (3,27), …,
(8,16), (9,17), (10,18), … (full list in `br1029-probe-out.txt`).
48 ordered equal-weight within-sign pairs also occur (control mass,
§5).

### 4.4 The exhibited unitary (route witness)

U = identity outside the u group. On the u seats, in both sign
blocks (orders [2,4,6,26,28,30] and [10,12,14,18,20,22]):

A_u = [[P, Q], [Q, P]],  P = diag(3/5, 3/5, 1),
Q = [[0, 4/5, 0], [−4/5, 0, 0], [0, 0, 0]],  (3/5)² + (4/5)² = 1.

Verified exactly in the script: UᵀU = I (real orthogonal, entries in
ℚ); [U, gammaF] = [U, D_ν] = [U, D_e] = [U, D_u] = [U, D_d] =
[U, UJ] = 0; piOp(U) = U⁻¹; Uᵀ·UJ·U = UJ (μ = 1). U's off-diagonal
support: (2,28), (4,26), (26,4), (28,2) in V₊ and (10,20), (12,18),
(18,12), (20,10) in V₋ — genuine rotations (entries ±3/5, ±4/5), not
permutations. U₈₉ = U₉₈ = 0, as §4.2 forces.

Lift: `liftedProd π_U (3,−1) t = U·diag(x^{w_s})·U⁻¹`, x = e^{it}.
Off-diagonal entries nonzero **as Laurent polynomials**: exactly the
8 pairs of U's support pattern, e.g.

  entry (2, 28) = (12/25)(x⁴ − x¹),   entry (28, 2) the same,
  entry (8, 9) = entry (9, 8) = 0 (identically).

At t = π/2 (x = i, Gaussian-rational evaluation):
entry (2, 28) = **(12/25)(1 − i) ≠ 0**. Seats 2, 28 are both in V₊
(γ = +1) with weights 1 ≠ 4. The only primitive det-1 directions for
π_U are (3, −1) and (−3, 1) (det π₁(g_{αβ} t) = exp(it(−4α − 12β))
by T1 `sum_A`, `sum_B`; conjugation preserves det), and along
(−3, 1) the (2, 28) entry is (12/25)(x⁻⁴ − x⁻¹) by the substitution
x ↦ x⁻¹ — also nonzero at x = i. Hence π_U satisfies the
K-CLS-1a witness condition in base form: every primitive det-1
direction has a t and a same-sign pair with liftedProd ≠ 0.

## 5. Controls

- **Colour control (registered).** The full colour swap within the
  u group (seats 2↔4, 6 fixed, mirrors included) lies in the full
  commutant including UJ, and mixes the colour seats 2, 4, 6 freely —
  all at lifted weight 1 (T1 `weights_colour_equal`). Equal weights:
  this mixing is real and **cannot** fire K-CLS-1a, exactly as
  registered. Reported as control data only.
- **Negative control.** S₈₉ (seat swap 8↔9; unitary, mixes (8, 9) by
  construction, commutes with gammaF) lies **outside** the commutant:
  [S₈₉, D_ν] ≠ 0, [S₈₉, D_e] ≠ 0, [S₈₉, UJ] ≠ 0. The detector sees
  (8, 9) mixing; clause (c) is exactly what excludes it.

## 6. Verdict

**ROUTE LIVE.** The conjugation route fires K-CLS-1a by construction
(base form): the commutant contains a unitary (exhibited, exact
rational entries) satisfying (a), (b) in its true ∀M form, and (c) at
generic Yukawas, whose conjugate π_U has non-diagonal lifted product
at the same-sign, different-weight pair (2, 28) (weights 1 vs 4) —
and at 7 further pairs. The named pair (8, 9) is NOT the firing
pair; it is provably (at probe grade) unmixable in this commutant.
K-CLS-1a's registered statement quantifies over some same-sign pair,
so the substitution of (2, 28) for the candidate (8, 9) is within
the registration.

**Follow-on Lean brick — price M** (flagged risk: L if the 32×32
entrywise discharge fights back). Contents: define U as the explicit
sparse matrix (support on 12 seats, entries in {0, ±1, ±3/5, ±4/5}
cast to ℂ); prove U⋆U = 1, [U, gammaF] = 0, [U, DF_oneGen Y…] = 0
for all Y (channel-wise), piOp(U) = U⁻¹ and the intertwining
transport; assemble `DialOneBase π_U` from π₁'s landed base clauses
(clause transport under (a)–(c), §1.5's clause-check made T1);
compute `liftedProd π_U 3 (−1) (π/2)` entry (2, 28) ≠ 0 via
exp(i·w·π/2) = i^w evaluations; close K-CLS-1a (base form) with the
direction-uniqueness step from `sum_A` / `sum_B`. Cost driver:
entrywise matrix identities at size 32 — mitigated by U's sparse
block support (identity outside the u group).

## 7. Fences

- **Base form only.** π_U is certified (at probe grade) for
  `DialOneBase`. The strengthened set is NOT transported: the colour
  projectors `colProj c` do not commute with U (U mixes colours
  1↔2 across the half-split), so C3col-type clauses are not
  inherited by cyclicity. Strengthened-form K-CLS-1a remains open
  and is not claimed either way.
- **Route scope.** This verdict is about the conjugation route only,
  per §1.5. It fires the pre-registered kill K-CLS-1a (pending the
  Lean brick); it says nothing about CLS-1a over non-conjugate base
  representations, and nothing in it is evidence FOR CLS-1a.
- **(8, 9) fence.** Any future write-up must not say the kill fires
  "at (8, 9)": that pair is unmixable in this commutant. The firing
  pair is (2, 28) (with (4, 26) and the V₋ mirrors).
- Exact arithmetic throughout; no float was used at any step.

**NO CLAIM. Dial 1: 0 (all dials 0/4) until the follow-on brick lands.**
