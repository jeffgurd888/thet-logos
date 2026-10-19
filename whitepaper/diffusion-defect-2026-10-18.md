# Diffusion Defect — Jeff's `z² = X² + y² + t`, proved for a finite random walk

**Date:** 2026-10-18
**Module:** `lean/ThetLogos/DiffusionDefect.lean` (builds green; 12 T1 theorems, 3 definitions, zero sorry/admit, no new axioms)
**Origin:** Jeff's notation, proposed in chat 2026-10-18 ~21:26 EDT, commissioned with "build it" ~21:28 EDT.

## The notation

Jeff wrote:

```
X² + t + y² + t = z² + t
```

One `t` cancels, giving the net form:

```
z² = X² + y² + t
```

— time as the *Pythagorean defect*: exactly how much the squared diagonal overshoots the flat right-triangle closure `X² + y²`. The gauntlet run on this notation (same evening) returned GO as an emblem and named the price of making it a statement: a coefficient for `t` with honest units, and a clock for `t` that is measured independently of the equation. This brick pays both, in the smallest model that carries the shape: the simple symmetric random walk on `ℤ²`, where the physical shadow Jeff pointed at — diffusion, mean-square radius growing linearly in time — is a theorem.

## What was built

The model: steps `stepVec : Fin 4 → ℤ × ℤ` are the four unit vectors `(1, 0)`, `(−1, 0)`, `(0, 1)`, `(0, −1)`. A path of length `n` is `p : Fin n → Fin 4`; its displacement is `disp p = ∑ i, stepVec (p i)`; `normSq (a, b) = a² + b² ∈ ℤ`. All sums run over all `4ⁿ` paths (uniform counting measure; expectation = sum / `4ⁿ`).

Theorems (all T1, in module order):

| Name | Statement |
|---|---|
| `normSq_add` | `normSq (u + v) = normSq u + 2·(u₁v₁ + u₂v₂) + normSq v` — the expansion every later step uses. |
| `normSq_stepVec` | Every step has squared length 1. |
| `sum_stepVec` | **Lemma A (mean):** `∑ s, stepVec s = 0` — the four steps cancel exactly. |
| `sum_normSq_stepVec` | **Lemma A (energy):** `∑ s, normSq (stepVec s) = 4`. |
| `sum_stepVec_fst`, `sum_stepVec_snd` | The step vectors cancel componentwise. |
| `disp_cons` | Displacement splits as first step + tail displacement. |
| `sum_paths_succ` | Sums over paths of length `n+1` split over first step and tail (via the cons bijection). |
| `sum_disp` | **Lemma B (mean):** `∑ p, disp p = 0` for all `n` — no drift. Recurrence `D (n+1) = 4 • D n`. |
| `sum_normSq_disp` | **Lemma C (second moment):** `∑ p, normSq (disp p) = 4ⁿ · n`. Recurrence `Q (n+1) = 4·Q n + 4ⁿ⁺¹`; cross terms vanish by Lemma A. |
| `sum_normSq_add_disp` | **Headline:** for every start `(x, y)` and every `n`, `∑ p, normSq ((x, y) + disp p) = 4ⁿ · (x² + y² + n)`. |
| `expected_normSq` | **Corollary (expectation, in ℚ):** `(4ⁿ)⁻¹ · ∑ p, normSq ((x, y) + disp p) = x² + y² + n`. |

The corollary is the equation itself: `z² = X² + y² + t` with `t := n` the step count and `z²` read as the expected squared distance from the start.

## Fences

- **Finite combinatorial model.** Nothing here is a continuum limit; no limit is taken or claimed.
- **`t` is the step count**, an integer clock internal to the model. It becomes physical clock time only when a physical clock *and* a physical diffusivity are supplied from outside.
- **The coefficient 1 in front of `t` is the walk's normalization** — unit steps, four directions equally likely. It is the diffusivity *of this model*: chosen, not derived. A physical diffusion law carries its coefficient (units: area per time); this model sets it to 1 by construction.
- **The `+` sign is the model's Euclidean signature**: chosen, not derived. In this house signature is input data (cf. `EdgeSignature.signature_not_determined`, which proves structure alone cannot fix it).
- The theorem is about the expected squared displacement of this walk. **No spacetime claim, no Navier–Stokes claim.**

## Verdict

The notation's diffusion shadow is now **T1 at finite level, in step units, with the coefficient pinned as model normalization**. Jeff's sentence "time adds area" is, for this walk, a proved theorem with the cross terms cancelled by the same symmetry that makes the walk drift-free.

What it is **not**: not a spacetime identity; not a derivation of signature (the plus sign is an input, as always); not a statement about physical time — `t` is a step count until a physical clock and a diffusivity are supplied. The continuum diffusion equation, the heat kernel, and any physical clock remain outside this brick, unclaimed.
