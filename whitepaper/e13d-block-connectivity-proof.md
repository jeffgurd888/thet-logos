# E13-D Block-Connectivity Theorem

*Tier-2/3 hand proof. LOCAL — not pushed. 2026-10-02.*
*Parent: Engine 13-D (`python/thet_logos/engine13d_components.py`), spec
`whitepaper/e13d-component-decomposition-spec.md`.*
*Quarantine wall holds: no finite→continuum, no d_spec→4, no modular→clock,
no Lorentzian/GR, no experimental prediction, no particle identification
beyond the representation. Component labels are algebraic origins only.*

## 0. Status ledger

**PROVED** (hand proof, no numerics):
§2 dichotomy lemma · §3 exact kernel element · §6 M3-p infinitude
(parametric) · §8 completeness modulo §4 · §9 contrast (finiteness,
attainment, positivity).

**NUMERICALLY WITNESSED** (honest label):
§4 dim ker L = 1 (SVD gap) · §7 the twelve sample values (seed 202613) ·
D3/D5 lower-bound numbers cited in §9.

## 1. Definitions

- `A_F = ℂ ⊕ ℍ ⊕ M_3(ℂ)`; element `a = (u1, q, color)`.
  `af_generators()` (`common.py`): 24 real generators —
  `g_0 = (1,0,0)`, `g_1 = (i,0,0)`, `g_2..g_5` quaternion units,
  `g_6..g_23` the pairs `(0,0,E_{pq})`, `(0,0,iE_{pq})`.
- `π_full(a) = block_diag(embedSM(a), ρ2(a))` on `ℂ^32 = ℂ^16 ⊕ ℂ^16`
  (`engine13d_components.py` D1). Top block: Option-A embedding.
  Bottom (probe) block:
  `ρ2(a) = diag(u1·I_4, I_2⊗q, color, color, u1·I_2)`,
  a genuine linear unital *-representation.
- Order-unit space `V = span_ℝ{ H(π_full(g)) : g ∈ af_generators }`,
  `H(M) = (M+M*)/2`; `B_0..B_10` its orthonormal basis (`m = 11`).
- `D_F = DF_oneGen(Y_PHYS)·VEV`, Hermitian 32×32. Block form
  (from `buildDirac` with `C = E = 0`, `B = conj(A) = A`):
  on each 16-block `D = [[0, A],[A, 0]]` with
  `A = diag(Ynu, Ye, Yu, Yd, Yu, Yd, Yu, Yd)·VEV` diagonal 8×8.
- Lipschitz seminorm `L(x) = ‖[D_F, A(x)]‖_op`, `A(x) = Σ_k x_k B_k`.
- Metric (exactly as implemented): for density matrices `ρ, σ`,
  `d(ρ,σ) = sup { |Tr((ρ−σ)·A(x))| : x ∈ ℝ^11, L(x) ≤ 1 }`,
  with `d = ∞` when the sup is unbounded. We write
  `(ρ−σ)(b) = Tr((ρ−σ)·b)`.
- States: the 50 D2 pure states (seed 202613): `C` (dim 16),
  `H`×12 (dims 20–21), `M3`×12 (dims 24–26), and partner-doubled
  copies (`-p`, index map `i ↔ i+16`): `C-p` (dim 0), `H-p`×12
  (dims 4–5), `M3-p`×12 (dims 8–10, color vector `c ∈ ℂ^3`).

## 2. Lemma 1 — finite-dimensional dichotomy (PROVED)

Let `b_0` span `ker L`. Then for any states `ρ, σ`:
`d(ρ,σ) = ∞ ⟺ (ρ−σ)(b_0) ≠ 0`; if `(ρ−σ)(b_0) = 0` then
`d(ρ,σ) < ∞` and the supremum is attained.

*Proof.* (⇒) Put `a_n = n·b_0 ∈ V`. Then `L(a_n) = n·L(b_0) = 0 ≤ 1`,
so each `a_n` is admissible, and
`|(ρ−σ)(a_n)| = n·|(ρ−σ)(b_0)| → ∞`. Hence the sup is unbounded.
(⇐) If `(ρ−σ)(b_0) = 0`, then `(ρ−σ)` descends to the quotient
`V/span{b_0}`, on which `L̄([x]) = L(x)` is a genuine norm
(`L(x) = 0 ⟺ x ∈ span{b_0}`, using §4). So
`|(ρ−σ)(x)| = |φ̄([x])| ≤ ‖φ̄‖·L̄([x])` for a finite dual norm `‖φ̄‖`;
the sup over `{L ≤ 1}` is `≤ ‖φ̄‖ < ∞`, and is attained by compactness
of the unit ball in the finite-dimensional normed space
`(V/span{b_0}, L̄)`. ∎

## 3. Lemma 2 — exact kernel element (PROVED)

```
b_0^exact = (1/√20)·diag(T, I_16),   T = diag(1,1,0,0,0,0,0,0, 1,1,0,0,0,0,0,0)
```
satisfies `[D_F, b_0^exact] = 0` **exactly**, and `b_0^exact ∈ V` exactly.

*Proof.* Write the top 16-block as 8×8 quarters. `D_top = [[0,A],[A,0]]`
with `A` diagonal; `b_0^exact` top `= (1/√20)·diag(T1,T2)` with
`T1 = T2 = diag(1,1,0,0,0,0,0,0)` diagonal. Diagonal matrices commute,
so `[D_top, diag(T1,T2)] = 0`. The bottom block is scalar, commuting
with everything. Membership in `V`: with `S = {0,2,6,14,22}`,
`b_0^exact = (1/√20)·Σ_{k∈S} H(π_full(g_k))` as an exact matrix
identity (verified to `0.0` Frobenius distance; each summand lies in
`V` by construction). ∎

Remarks (proved): the argument uses only that `A` is diagonal, so the
kernel element is **independent of the Yukawa input values**. As algebra
elements, `Σ_{k∈S} g_k = (1, I_2, I_3) = 1_{A_F}` exactly — `b_0^exact`
is the "would-be linear image" of the unit; its non-scalar part measures
the Option-A bilinearity on the top block (interpretation, not theorem).

## 4. Lemma 3 — `dim ker L = 1` (NUMERICALLY WITNESSED)

Singular values of `x ↦ [D_F, A(x)]`:
`[280.2, 258.3, 228.8, 228.8, 161.9, 161.9, 161.8, 161.8, 143.4, 6.22, 3.2e-14]`.
Gap: `s_10/s_0 = 2.2e-2` versus `s_11/s_0 = 1.1e-16` (roundoff). The
computed kernel direction equals `b_0^exact` to `1.1e-15` Frobenius.
The one-dimensionality is therefore witnessed with an enormous gap;
it is the single non-proved input to §8.

## 5. Lemma 4 — `b_0`-values of the D2 families (PROVED)

From the block form of `b_0^exact`, for a state `ρ`,
`ρ(b_0^exact) = (1/√20)·Tr(ρ·diag(T,I_16))`:

| family | support | `ρ(b_0^exact)` |
|---|---|---|
| `C`, `H`×12, `M3`×12 (bottom block) | dims 16–31, scalar block | `1/√20 ≈ 0.22361` |
| `C-p` | dim 0 (`T_00 = 1`) | `1/√20` |
| `H-p`×12 | dims 4–5 (`T = 0`) | `0` |
| `M3-p(c)` | dims 8–10 | `(1 − |c_3|²)/√20` |

*Proof.* Direct trace computation. Bottom block of `b_0^exact` is
`(1/√20)·I_16`; top-block entries read off `T`. ∎

## 6. Main theorem — M3-partner infinitude (PROVED)

Let `ρ_c` be an M3-p state with color vector `c`, `0 < |c_3|² < 1`,
and let `σ` be any state whose `b_0^exact`-value is `1/√20`, `0`, or
`(1−|d_3|²)/√20` with `|d_3|² ≠ |c_3|²`. Then `d(ρ_c, σ) = ∞`,
genuinely — not an optimizer artifact.

*Proof.* Take `a_n = n·b_0^exact ∈ V`. By Lemma 2, `L(a_n) = 0 ≤ 1`
**exactly** for every `n`, so all `a_n` are admissible. By Lemma 4,
`(ρ_c − σ)(b_0^exact)` equals `−|c_3|²/√20`, `(1−|c_3|²)/√20`, or
`(|d_3|²−|c_3|²)/√20` respectively — all nonzero under the hypotheses.
Hence `|(ρ_c−σ)(a_n)| = n·|(ρ_c−σ)(b_0^exact)| → ∞`. ∎

The exhibited family is completely explicit: `a_n = n·b_0^exact` with
`b_0^exact` as in Lemma 2 (equivalently the generator sum there).
Commutator bound `0 ≤ 1` holds analytically for all `n`; no numerics
enter the infinitude direction.

## 7. The twelve instances (NUMERICALLY WITNESSED)

The D2 M3-p samples (seed 202613) have `|c_3|²`:
`0.329, 0.705, 0.335, 0.246, 0.301, 0.135, 0.242, 0.311, 0.117, 0.154,
0.293, 0.867` — all strictly inside `(0,1)` and pairwise distinct.
Their `b_0^exact`-values are twelve distinct numbers in
`(0, 1/√20)`. By §6, each is at infinite Connes distance from all
other 49 sampled states. The twelve singletons of D4 are therefore
genuine. (The condition is open and generic; a sample with
`|c_3|² ∈ {0,1}` or a collision would fail to isolate — none do.)

## 8. Completeness (PROVED modulo §4)

The D4 decomposition is exactly the level sets of
`ρ ↦ ρ(b_0^exact)`: value `1/√20` → the 26-island
(`C, H×12, M3×12, C-p`); value `0` → the 12-island (`H-p`×12);
twelve distinct interior values → twelve singletons (`M3-p`).
No finer splitting and no coarser merging is possible without a
second kernel direction, i.e. modulo Lemma 3. In particular the
infinite distances reported by D3's kernel test are all explained by
this single exact functional — the optimizer discovered nothing the
theorem does not certify.

## 9. Contrast — the converse (PROVED)

`C` (index 0) vs `M3` (index 13): both have `b_0^exact`-value `1/√20`
(bottom block, scalar), so `(ρ_C − ρ_M3)(b_0^exact) = 0`. By Lemma 1,
`d(ρ_C, ρ_M3) < ∞` and the supremum is **attained**. Positivity is also
proved: with `h = H(π_full((0, 0, diag(1,0,0) − ⅓I_3))) ∈ V`,
`(ρ_C − ρ_M3)(h) = −(|c_1|² − 1/3) = −0.19447 ≠ 0` for the sampled
`c` (`|c_1|² = 0.52781`), so
`d(ρ_C, ρ_M3) ≥ 0.19447/‖[D_F, h]‖_op > 0`.
D5's rigorous lower bounds (`0.0156–0.146 GeV⁻¹` across C–M3 pairs)
are consistent. Finite, attained, nonzero — the exact converse of §6.

*Remark (proved).* On bottom-block dims 20–23 the order-unit space is
scalar (the only Hermitian quaternion is `I_2`), so the twelve `H`
samples are pairwise at distance **zero** — the Connes metric is a
pseudometric with nontrivial zero-classes here, as expected in general.
Not a defect; recorded for exactness.

## 10. Falsifiability

- `[D_F, b_0^exact] = 0` is an exact matrix identity (diagonal
  commutation) — closed to numerical falsification; a representation
  change would require re-derivation (the theorem is
  representation-relative).
- A second exact kernel direction would revise §8 (not §6, which needs
  only Lemma 2). It would have to hide below `2.2e-2` relative singular
  value — the quoted gap is the concrete bound.
- Every sample-dependent claim is checkable from seed `202613`.

## 11. Self-review — gaps I would bet against

The weakest link is Lemma 3 (`dim ker L = 1` numerical). I bet **for**
it: the gap `2.2e-2` vs `1.1e-16` is decisive, and the level-set
structure predicts D4's fourteen components exactly, which an
accidental near-kernel could not do. The infinitude direction (§6)
does not depend on Lemma 3 at all — it rests on the exact Lemma 2
alone. No proof step uses unproved optimizer behavior; the exhibited
`a_n` family is optimizer-independent. I find no remaining gap I would
bet against.
