# R1 — LayerKernelPos at the abelian seat family (all N) — landing dossier

- **Brick:** R1, fired from the Stage 3c re-scope's priced menu
  (§5 of `~/workspace/your_files/pitch4-stage3c-rescope-2026-11-05.md`)
  by Jeff's tap, 2026-11-05 07:32 EST.
- **Lane:** single-lane 𝒜 ⪰ 0 core-chain work, worktree
  `~/workspace/thet-logos-r1lkp`, branch `r1-lkp-abelian-family`,
  base `5baceb3` (census 13,513/504, fence 545/545).
- **Module:** `lean/ThetLogos/LayerKernelPosAbelianFamily.lean`
  (one new module; no existing file edited; module name and all
  declaration names collision-scanned against the tree: zero hits).
- **Verdict:** FULL at the contracted scope — `LayerKernelPos` at
  the abelian seat for **every** `N` and every `β ≥ 0`.
  **K-LKP-AB did not fire. K-LKP-SEAT did not fire.**
  (Build/axiom verification: §6 — targeted elaboration PASS,
  warning-clean; axioms exactly the fence trio.)

## 1. The exact statement proved

Headline `layerKernelPos_abelian_family`:

```
theorem layerKernelPos_abelian_family {N : ℕ} [NeZero N] {β : ℝ}
    (hβ : 0 ≤ β) :
    LayerKernelPos (N := N) seatμ seatρ β
```

with the seat of LK-P0: `G = Multiplicative (ZMod 2)`,
`ρ = seatρ` (the sign representation), `μ = seatμ` (the uniform
probability measure) — all imported unchanged from
`LayerKernelPosSeatProbe`. No `hρcont` hypothesis (the seat's
continuity is the discrete one, `seatρ_cont` precedent). This
strictly generalizes `layerKernelPos_seat` (the `N = 2` case).

Closed form (for `N ≥ 2`), `layerKernel_abelian`: with
`a = (1 + e^{−2β})/2`, `b = (1 − e^{−2β})/2`,
`L = Fintype.card (LayerColumn N)` (kept symbolic),

```
layerKernel seatμ seatρ β u u'
  = ↑( Σ_{S ∈ univ.filter famEven} a^(L−|S|) · b^|S| · Φ_S(u) · Φ_S(u') )
```

and the pairing is exhibited as `Σ_S w_S ‖Z_S‖²` with
`w_S = a^(L−|S|) b^|S| ≥ 0` for `β ≥ 0` and
`Z_S = Σ_u Φ_S(u) F(u)` (`layerKernelPos_abelian_ge`).

## 2. Proof shape (LK-P0's, lifted)

1. **Sign factorization** — `famColSign P α u u'
   = famStratumSign P α · (famConfigSign P u' · famConfigSign P u)`
   (`fam_colSign_factor`).
2. **Per-column Boltzmann factor** — `exp(−β·dens) = a + b·χ(word)`
   (`fam_exp_colDensC`, via `fam_colDensC_seat`).
3. **Stratum character as a monomial** — `∏_{P∈S} famStratumSign P α
   = ∏_c χ(α c)^{famColMult S c}`, fiberwise over base sites and
   shifted sites (`fam_stratumSign_prod`).
4. **The parity filter** — the stratum average of the character is
   `1` if `S` is even (every site multiplicity even) and `0`
   otherwise; the site sum `∑_g χ(g)^m` is `2`/`0` by parity and
   the `2^(#sites)` cancels the stratum configuration count, kept
   symbolic as `(Fintype.card (LayerSite N → G) : ℝ)⁻¹`
   (`fam_stratum_average`).
5. **Expansion** — product over columns → sum over the powerset
   (`Finset.prod_add`) → the filter leaves exactly the even
   families (`fam_kernel_expand`); the kernel unfolds by `rfl`
   and integrates by `seatIntegralPi` (`layerKernel_abelian`).
6. **Gram assembly** — the pairing separates over the finite
   configuration sums as `Σ w_S ‖Z_S‖²` times two positive seat
   factors (`layerKernelPos_abelian_ge`).

## 3. The one genuine case split (a finding, recorded at full rank)

The contracted proof shape routes through the corpus's column
decomposition `layerDensSum_eq_sum_columns`, whose `Even N`
hypothesis is spent in exactly one place — `layerConfig_up`,
where it is used only via `two_le_of_even` to obtain `2 ≤ N`
(for `(1 : ZMod N).val = 1`). The word identity therefore holds
for **every `N ≥ 2`**. §1 of the module re-proves the three-link
chain at `2 ≤ N` in the module's own names
(`layerConfig_up_fam`, `plaquette_layerConfig_fam`,
`plaquetteDensity_layerConfig_word_fam`,
`layerDensSum_eq_sum_columns_fam`); no landed file is edited.

At `N = 1` the word identity is **false**, not merely unproved:
`(x 0).val = 1` is impossible in `ZMod 1`, the "up" read never
fires, and every plaquette word of the layer configuration is a
commutator `α c · u ℓ · (α c)⁻¹ · (u ℓ)⁻¹` (both stratum reads
are the same site, both spatial reads the same link), whose
seat sign is `+1`. Hence every density is `0`, the action
vanishes, and the kernel is the constant `1`
(`plaquette_seatSign_one`, `layerKernel_one`), and
`LayerKernelPos` at `N = 1` follows by the `β = 0` separation
(`layerKernelPos_one`). The headline case-splits `N = 1 ∨ 2 ≤ N`.

## 4. The early gate (T2, run before the deep proof work)

Harness: `~/workspace/your_files/r1-lkp-gate-2026-11-05/r1_gate.py`
(python/numpy; geometry built from the tree's definitions;
`w_c = t_c = U[c]·U′[c]` since a column and its link are indexed
identically). Direct side computed from the definition only.
Closed side: the even-family sum. β grid {0.25, 0.7, 1.3};
instances `u = u′ = 1` and seeded-random (seed 20261105).

- **N = 2 — PASS, five engines** (full α-enumeration, bucket
  elimination, even-family enumeration by GF(2) masks, subset DP,
  Fourier-dual): agreement ≤ ~4e-22 on every instance; the LK-P0
  landmark `K(1,1) ≥ a²⁴ + a²²b²` re-verified at all three β
  (β=1.3: 0.007812510602169 ≥ 0.000000579731643).
- **N = 3 — PASS, four engines** (full α-enumeration over
  2⁸¹ strata, subset DP, dual, bucket): agreement ≤ ~4e-23
  (β=0.7, (1,1): K = 1.4992880e-8 by all four).
- **N = 4 — PASS, two engines**: bucket elimination (direct
  kernel, exact, min-fill order, max factor scope 25) vs the
  Fourier-dual closed form: agreement ≤ 1e-32 absolute (values
  ~1e-17; e.g. β=0.25, (1,1): K = 1.0996135393036367e-17) on all
  six instances. The subset DP exceeded its 2.5M-state guard at
  N=4 (reported, not silently dropped; it was decisive at
  N = 2, 3 where it completed). The reverse-lex bucket order was
  dropped at N=4 after it OOM-killed the harness twice (factor
  scope > 33 ⇒ > 2³³·8 B) — a harness resource failure, not a
  mismatch; min-fill bucket on the same instances completed in
  ~3 s at ~0.7 GB.
- **N = 1 — divergence confirmed as predicted**: true kernel
  `= 1`; column formula `= e^{−2βm}` for the drawn instance
  (`m` = #{columns with `t_c = −1`}) — at β=1.3 the draw gives
  0.005516564420761 ≠ 1. (At β=0.7 the draw had `m = 0` and the
  formula coincidentally also gives 1; the formula is not
  identically 1 at `N = 1`, which is the point: the column
  identity fails there while LKP holds trivially.)

No mismatch anywhere ⇒ **K-LKP-AB did not fire**; every computed
kernel value is a positive sum ⇒ no negative pairing witness ⇒
**K-LKP-SEAT did not fire**.

## 5. Census and price band

Module contents: **21 strict** (`theorem` at column 0) + 7
definition-level items (4 plain defs, 2 noncomputable defs, 1
noncomputable Decidable instance: famColSign,
famStratumSign, famConfigSign, famConfigProd, famColMult,
famEven, the Decidable instance — 7 items — plus no others).

Contracted band **M: 15–35 strict. Landed 21 — inside the band,
no deviation to declare.** (The `2 ≤ N` word chain and the
`N = 1` degenerate case were not in the scoping sketch's
shorthand; they were needed and are inside the band.)

Theorem list: `layerConfig_up_fam`, `plaquette_layerConfig_fam`,
`plaquetteDensity_layerConfig_word_fam`,
`layerDensSum_eq_sum_columns_fam`, `fam_colSign_factor`,
`fam_colDensC_seat`, `fam_exp_colDensC`, `fam_stratumSign_prod`,
`fam_stratum_average`, `fam_exp_neg_layerAction`,
`fam_kernel_expand`, `layerKernel_abelian`,
`layerKernelPos_abelian_ge`, `torusShift_eq_self_one`,
`layerShift_eq_self_one`, `layerConfig_up_one`,
`plaquette_seatSign_one`, `plaquetteDensity_layerConfig_one`,
`layerKernel_one`, `layerKernelPos_one`,
`layerKernelPos_abelian_family`.

## 6. Verification

- **Targeted build: PASS.** The module was elaborated with the
  toolchain `lean` against the worktree's environment
  (`lake env` LEAN_PATH with the overlay of the environment note
  below): **exit code 0, zero diagnostics** — no errors, no
  warnings (final clean run 3063 s wall; the wall time is the
  shared box's IO saturation, not elaboration cost: IO pressure
  "full" ran ~46–53% throughout with the WB-3 smoke build
  compiling concurrently, and the import closure pulls the full
  Mathlib environment through gateway `import Mathlib` modules).
  Two defects were found and fixed across the verification runs:
  an `nlinarith` closer whose ring normalization rebuilt the
  dependent atom `layerLinkOf c ν hν` with a metavariable proof
  argument (replaced by an abstract-reals identity + fully
  explicit rewrite arguments — a bare `rw` leaves `hν`, which
  occurs only on the lemmas' right-hand sides, as an unsolved
  side goal), and a `haveI` linter warning (replaced by
  `classical`).
- **Axioms: exactly the fence trio on every headline checked.**
  `#print axioms` output (verbatim):
  `'ThetLogos.layerKernelPos_abelian_family' depends on axioms:
  [propext, Classical.choice, Quot.sound]` — and identically for
  `layerKernelPos_abelian_ge`, `layerKernelPos_one`,
  `layerKernel_abelian`, and `fam_stratum_average`. No `sorryAx`.
- **Zero sorrys, no `native_decide`**: token scan of the module
  is clean, and the empty diagnostic stream confirms no
  sorry-warnings.
- Environment note: the main tree's `.lake` is missing exactly
  one olean in this brick's import closure — `Span3SeatSchur`
  (its `.olean.hash` `e7d5d5198aad51ca` and `.ilean.hash`
  `7f3ff5f8b37e95c7` survive; the payload files do not). The
  smokegate basis holds a byte-identical artifact (same source
  md5 `f0df1072e1198908f9596b5753ce0685`, same recorded hashes);
  lane verification used it through a read-only LEAN_PATH
  overlay (symlink forest + the four hash-verified files), and
  the lane did not run `lake build` in the worktree because
  that would first rebuild `Span3SeatSchur` into the *shared*
  `.lake`. Integration must either rebuild `Span3SeatSchur`
  from source (658 lines; a from-source rebuild attempt in this
  lane was still incomplete after 51 min of wall time under the
  IO saturation above) or transplant the hash-verified olean
  deliberately. No file in the main tree was modified by this
  lane.

## 7. Honesty

Qualitative-core content at one seat family. This brick does
**not** claim the margin floor or any uniform gap — at this
very seat family the floor is **false** (re-scope §3.6: margins
`B′(β)^(link count)`). It advances no continuum statement.
**Moves no dial. NO CLAIM; dials 0/4.**
