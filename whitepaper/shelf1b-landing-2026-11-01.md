# SHELF-1b — LANDED FULL: Lumer–Phillips AND the contraction case of Hille–Yosida — above the map's named acceptable PARTIAL

**Verdict: SHELF-1b FULL. Both generation theorems land in `SemigroupGeneration.lean`, built against SHELF-1a's landed `C0Semigroup` core: `lumer_phillips` (a densely defined, dissipative operator with the range condition at one λ₀ > 0 generates a contraction C₀-semigroup whose generator is exactly A) and `hille_yosida_contraction` (the contraction case of Hille–Yosida from resolvent power bounds). No pre-named seam bites: not LP-only (HY landed too), not GEN-ID (generator equality is proved), not CONV (convergence holds on all of E, uniform on compact time intervals). Two named remainders stand on the module's face (below). NO CLAIM; dials 0/4 — a general analysis fill; closes no posted question.**

## Hypotheses, named on the face

Dissipativity is taken in the resolvent-bound characterization (`DissBound`: `λ‖x‖ ≤ ‖λx − A x‖` for all λ > 0, x ∈ D) — the form the proof consumes; the duality-pairing form is noted in the header as the classical equivalent, not separately formalized. Hille–Yosida's statement consumes only n = 1 and surjectivity at λ = 1 of its power-bound family, as stated on its face.

## What landed

- `lumer_phillips`, `hille_yosida_contraction` (headlines); the constructed semigroup's generator domain equals D (`lpSemigroup_genDom_eq`), its generator is A (`lpSemigroup_hasGen`), its resolvent exists at every λ > 0 (`lpSemigroup_resolventSpec`).
- The `hlim` story, exactly: 1a's `yosidaApprox_tendsto` cannot be instantiated pre-generation (its resolvent spec is relative to an existing semigroup), so the identical on-domain convergence was proved for the abstract A, and the `hlim` hypothesis (`λ•R(λ)z → z` for all z) was **discharged** from density + the contraction bound + on-domain algebra. Post-construction, 1a's own Yosida theorem is instantiated for the LP semigroup.

## SHELF-1a's remainders — disposition for the Lumer–Phillips class

- Generator closedness/density: **DISCHARGED** (genDom = D, hence dense; sequential graph-closedness of A read off the resolvent).
- `exp(tA_λ) x → T t x`: **DISCHARGED** (pointwise for all t ≥ 0 and all x; uniform on compact intervals via a Duhamel Cauchy estimate extended by density).
- All-of-E `hlim`: **DISCHARGED** (above).
- **Resolvent integral formula** `R(λ) x = ∫₀^∞ e^{−λt} T t x dt`: **NOT discharged — named remainder, verbatim on the module's face.** Only its algebraic half (the resolvent spec) is proved.

## Named remainder (verbatim)

General-M Hille–Yosida: "for general `M >= 1`, the implication from `||(lam - A)^{-n}|| <= M lam^{-n}` for all `lam > 0` and all `n` to the generation of a semigroup with `||T t|| <= M` is NOT proved in this module."

## Parent verification (from disk)

- Canonical counter: **strict=66, defs=12** (inside the L–XL estimate 60–120); zero "sorry"/`native_decide` tokens; `SemigroupCore.lean` unedited.
- Parent module build green, independently reproduced.
- Parent axiom checks: `lumer_phillips`, `hille_yosida_contraction`, `lpSemigroup_genDom_eq` — each on exactly `[propext, Classical.choice, Quot.sound]`.

## Census

10,224 → **10,290 strict** / 10,301 → **10,367 attribute-inclusive** / 345 → **346 modules** (delta +66 strict, +1 module). README badge and body both updated at this landing and verified against the committed README.

## Backers since last landing

No change to the backer roll since the last landing.
