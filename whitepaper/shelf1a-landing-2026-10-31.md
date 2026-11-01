# SHELF-1a — LANDED PARTIAL at the pre-named remainders: the C₀-semigroup core (object, generator core, anchor, algebraic resolvent, Yosida core — at general Banach generality)

**Verdict: SHELF-1a PARTIAL, at exactly the remainders pre-named in its dispatch. The core is FULL: the C₀-semigroup object, the generator with its core theory, the bounded-generator anchor, the algebraic resolvent, and the Yosida approximants with on-domain convergence all landed at general Banach-space generality — the pin owns no C₀-semigroup theory, so the general-API half of the VISC fence and of the S2-4(b) fence RETIRES. Named OPEN on the module's face (never dropped): closedness and density of the generator; the resolvent integral formula; `exp(tA_λ) x → T t x`; and the all-of-`E` Yosida convergence (which remains a stated hypothesis, exactly what density would supply). NO CLAIM. Dials 0/4.**

## Strike-check (no strike)

Pin inventory at dispatch: Mathlib v4.35.0-rc3 owns no C₀-semigroup theory (no strongly-continuous-semigroup or Banach-space generator API anywhere in `Mathlib/Analysis` / `Archive`; `spectrum.resolvent`/`resolventSet` exist only for bounded Banach-algebra elements). Fragments consumed: `NormedSpace.exp` + `exp_add_of_commute` and `hasDerivAt_exp_smul_const` (the bounded exponential, for the anchor), and `banach_steinhaus` (the local bound). The unbounded-generator resolvent is built from scratch. The seat module `LatticeSliceYosida` is untouched.

## What landed (`SemigroupCore.lean`, general Banach space `E` over ℝ)

- **The object:** `C0Semigroup` structure — `toFun : ℝ → (E →L[ℝ] E)`, `T 0 = 1`, the semigroup law for `s, t ≥ 0`, strong continuity on `Ici 0`; plus the Banach–Steinhaus local bound `C0Semigroup.exists_opNorm_le_Icc`. (Design on the face: a structure over a family defined for all real `t` with axioms for `t ≥ 0`, keeping one-sided real differential calculus directly available; the scalar is ℝ, stated — time and the resolvent/Yosida parameters are real; the ℂ case is not claimed.)
- **The generator core (FULL):** `HasGen` via the strong right derivative at 0; the domain `genDom` as a submodule; `generator : genDom →ₗ[ℝ] E`; commutation and domain invariance (`hasGen_apply`, `genVal_apply`); the differential identity `C0Semigroup.hasDerivWithinAt_apply` — an orbit right-differentiates within `Ici t` to `T t (A x)`.
- **The anchor (FULL):** `expSemigroup A` for bounded `A` is a C₀-semigroup with `genDom = ⊤` and generator exactly `A` (`expSemigroup_hasGen`, `expSemigroup_generator_apply`) — the bridge to the pin's owned exponential.
- **The resolvent (algebraic, FULL):** `ResolventSpec` (the two inverse relations), uniqueness (`resolvent_unique`), `R(Ax) = λRx − x`, commutation with `T t`, and the first resolvent identity.
- **Yosida (FULL at the registered seam):** `yosidaApprox = λ • (λR − 1)` as a bounded continuous linear map; `A_λ = λ • A R(λ)`; `A_λ x = λ • R(λ)(A x)` on the domain; each `A_λ` generates via the anchor; for a resolvent family with `‖R(λ)‖ ≤ λ⁻¹`, `λ • R(λ) x → x` is proved on the domain, and `A_λ x → A x` on the domain under the explicitly stated hypothesis `hlim` (pointwise `λ • R(λ) z → z` on all of `E`).

## The named remainders (the PARTIAL)

Closedness of the generator; density of `genDom`; the resolvent integral formula `R(λ) x = ∫₀^∞ e^{-λt} T t x dt`; the semigroup convergence `exp(tA_λ) x → T t x`; and `hlim` on all of `E` as a theorem rather than a hypothesis (density is precisely what would supply it). Each is stated on the module's face as open. These remainders are SHELF-1b's natural hunting ground (generation theorems) but are not silently transferred — 1b fires on its own map row.

## Parent verification (from disk)

- Canonical counter: **strict=32, defs=7** (inside the M–L estimate 30–60), 633 lines; zero attribute-prefixed declarations, zero "sorry"/`native_decide` tokens; no landed file edited.
- Parent module build green, independently reproduced.
- Parent axiom check: `C0Semigroup.hasDerivWithinAt_apply`, `C0Semigroup.exists_opNorm_le_Icc`, `expSemigroup_hasGen`, `expSemigroup_generator_apply`, `resolvent_unique` each on exactly `[propext, Classical.choice, Quot.sound]`. (Checker note: the semigroup theorems live in the `C0Semigroup` namespace — unqualified names fail; use the qualified forms above.)

## Census

10,007 → **10,039 strict** / 10,085 → **10,117 attribute-inclusive** / 336 → **337 modules** (delta +32 strict, +1 module). README badge and body both updated at this landing and verified against the committed README.

## Backers since last landing

No change to the backer roll since the last landing.
