# Wightman Re-Pin — Unlock Chain Item 3 (2026-10-18)

**Module:** `lean/ThetLogos/WightmanRepin.lean` (new; no existing file
modified). **Price:** S–M (the OS re-pin's flagged sibling re-pin;
ratified as item 3 of the unlock chain, 2026-10-18 — items 1–2
stand: the `numberOp` rename, Fock-level Lorentz continuity).
**Verdict: STANDS at the priced scope.** The Wightman axioms are
re-pinned on genuine objects; the window-by-window Rung-5 table is
machine-cited; two corrections to the old pins are proved, one of
them new and against the Rung-4 sharpening itself. **No interacting
Wightman QFT is claimed to exist. The bundle pins the scalar form
of the axioms. Clay parts closed: 0.**

## Numbers

- **14 strict T1** (line-initial `^(theorem|lemma) ` on
  comment-stripped source), **0 `@[simp]`**, **0 sorry/admit**.
  Plus 11 definitions/structures (the re-pinned statements).
- Targeted build green: `lake build ThetLogos.WightmanRepin`,
  **3,810 jobs**, `.olean` present.
- `#print axioms`: 13 headlines on exactly
  `[propext, Classical.choice, Quot.sound]`; the existence-vacuity
  correction (§1, Correction 2) depends on **no axioms at all**
  (constructive term, inherited from the OS re-pin's proof). No
  `sorryAx` anywhere.
- Program total: 3,215 + 14 = **3,229 strict**.

## §1. Corrections to the old pins (T1, named as corrections)

The Wightman side had two generations of pin: the 2026-10-06-era
`WightmanAxioms.lean` (opaque `Prop` fields, marker types) and
Rung 4's `WightmanTargets.lean` (six sharp definitions, bundled).
Both generations are defective in named ways; both files are
**unmodified** by this brick.

**Correction 1 — the premise is stale.** `WightmanAxioms.lean`'s
header, its `TemperedDistMarker` docstring, and its dependency
ledger (item 1) assert that Mathlib (2026) has no Schwartz
distribution theory. False for the pinned Mathlib v4.35.0-rc3:
`𝓢'(E, F)` ships with Fourier theory
(`Mathlib/Analysis/Distribution/TemperedDistribution.lean`), Rung 6
already built on it, and the OS re-pin discharged the sibling
`SchwingerMarker` on exactly this ground. §2 of the module
discharges `TemperedDistMarker` the same way: Wightman functions
are `𝓢'(Fin n × Fin 4 → ℝ, ℂ)`. The old file's header text is
flagged for the S-editorial list (joining the standing flags
there), not edited — file edits are a separate editorial act.
Ledger item 3 ("no Poincaré representation theory adequate for
quantum fields") is likewise now **partially** stale — see §4.

**Correction 2 — the old existence statement is vacuous.**
`InteractingWightmanQFT : Prop := ∃ _ : WightmanAxioms, True` and
its alias `WightmanExistence`, over a bundle whose every content
field is an unconstrained `Prop`, are provable from the all-`True`
instantiation. The OS re-pin proved this
(`oldPin_interactingWightmanQFT_trivial`, no axioms) because its
reconstruction target lives in this file; the present module
re-cites it in the `WightmanExistence` form
(`oldPin_wightmanExistence_trivial`) so the correction sits on the
Wightman file's own correction sheet. The old pin's "open problem"
did not state the open problem: it was **unprovable-to-fail**.

**Correction 3 — NEW: the Rung-4 sharp bundle is vacuous too.**
Rung 4's `SharpWightmanTarget` replaced the opaque fields by six
sharp definitions with exact formulas — real progress as
*conditions* — but bundled them as
`∃ (all data), W1 ∧ W2 ∧ W3 ∧ W4 ∧ W5 ∧ W6`, existentially
quantifying over the semantic parameters themselves: the field,
the joint spectrum `spec`, the spacelike-separation relation, the
Wightman functions `w`. Machine-checked:
`sharpWightmanTarget_trivial` (T1, standard three) exhibits junk
data satisfying all six clauses at once — `H = ℂ`, `Ω = 1`,
one-mode test functions, `D = ⊤`; the "field" `φ(f) = f • id`
(scalar multiplication, no operator content), which is linear,
weakly Hermitian for `conjTest = star`, and whose monomials cover
`ℂ` since `polyApply [z] = z` (so W5, the expected blocker,
falls); trivial representations with `spec = {0}` (W2, W3);
`spacelikeSep = ⊥` (W4 vacuous); an arbitrary `w` with
`w 4 _ = 1`, `w 2 _ = 0` giving connected 4-point `1` (W6). The
bundle is therefore a theorem with zero physical content — the
old pin's disease one level up, in the file built to cure it.
**What is NOT impugned:** the six sharp definitions as conditions
on fixed, externally given data — they are exact, and every Rung-5
verdict against them (§3) stands untouched. What is corrected is
the `∃`-bundling. The re-pin (§2) follows the OS method: data as a
structure's field, conditions as real quantified fields,
nontriviality as a separate clause.

## §2. The re-pin

- **Data.** `W : (n : ℕ) → WightmanDist n`,
  `WightmanDist n := 𝓢'(Fin n × Fin 4 → ℝ, ℂ)` — tempered
  distributions on Minkowski `n`-point tuples, points
  pair-indexed. The test-function space is the OS re-pin's space;
  Minkowski content is in the conditions, not the type.
- **Temperedness** is the type, made explicit by the glue
  theorems `wightmanDist_continuous/add/smul` (contrast the old
  pin, where temperedness could not even be stated against the
  marker).
- **Coordinate operations** at the plain-function level, OS-style:
  `revPoints` (point reversal), `minkMotion` (diagonal Poincaré
  motion), block operations `firstBlock`/`secondBlock` reused
  from `OSRepin`. `IsLorentz Λ` pins the Lorentz part by
  preservation of the old pin's own T1 object, `minkowskiInner`
  (whose cone geometry — `forwardLightCone_convexCone`,
  reverse Cauchy–Schwarz — was the old file's genuine T1 content
  and stands).
- **W3 in Fourier-support form.** `fourierTest F ξ` is the plain
  Fourier transform of the test function (Bochner integral over
  tuple space, `2π` convention, Euclidean pairing on tuples);
  `fourierTest_integrable` (T1) proves the integrand integrable —
  kernel factor of norm 1 times a Schwartz function — so the
  integral is genuine. `InSpectralSupport ξ`: every partial sum
  of the momenta (point order) lies in the closed forward light
  cone and the total momentum vanishes. The bundle's spectrum
  field is the annihilator form: `W n` kills every `F` whose
  transform vanishes on the spectral support. *Convention note:*
  the support statement is relative to the fixed `fourierTest`
  convention, printed here and in the module; support of a
  distribution is an annihilator condition, and this is that
  condition transported through the fixed convention. Stating W3
  this way needs no unbounded-operator machinery — which is
  precisely the machinery the old price (§3) is about *proving*
  things with, not stating them.
- **The bundle** (`WightmanBundle`): data `W`, vacuum
  normalization (`W 0 f = f 0`), **W2** Poincaré covariance
  (full Lorentz ⋉ translations, diagonal), **Hermiticity**
  (reversal + conjugation), **W3** spectrum (above), **W4**
  locality (swap-invariance under a spacelike-support hypothesis,
  `SpacelikeSeparatedAt`: `⟨xᵢ − xⱼ, xᵢ − xⱼ⟩ < 0` on the
  support), **Wightman positivity** (the GNS input: factorized
  double sums are nonnegative reals, mirroring OS E2 with
  reversal in place of reflection), **clustering** (time
  separation, `Tendsto` at `atTop`). Vacuum cyclicity is
  deliberately **not** a field: it is a property of the
  reconstructed field algebra, whose distribution-level input is
  positivity — the same separation the OS re-pin made.
- **Nontriviality, separated:** `InteractingWightmanStatement :=
  ∃ B : WightmanBundle, NonGaussian B.W`, reusing the OS re-pin's
  Wick-defect clause verbatim — the same formula, because "not
  quasi-free" is the same property on both faces of
  reconstruction, and this pin's bundle is the scalar one the
  clause is stated for (consistency note in §5). Unproved. Not
  claimed. It would be refuted by a proof that every Wightman
  bundle is Gaussian — a real Prop.
- **The OS schema's second hole, filled as a predicate:**
  `SatisfiesWightmanPin W := ∃ B : WightmanBundle, B.W = W`.
  `OSReconstructionStatement IsBoundaryValueOf
  SatisfiesWightmanPin` is now fully concrete — every symbol
  defined. Filling the first hole (analytic continuation) remains
  research-scale per the OS dossier's audit; no reconstruction is
  proved or claimed.

## §3. Window-by-window table (Rung 5 verdicts, machine-cited in §5 of the module)

All Rung-5 verdicts are at the **one-mode fermionic model**
(`Fock1 ≅ ℂ²`, test functions `⟨ℂ⟩`, Majorana field `ψ(c)`) —
that scope is part of each verdict, not a footnote.

| Window | Rung-5 verdict (citation) | Status at this re-pin |
|---|---|---|
| **W1** fields | **PROVED T1** as framed — `w1_majorana` (`Rung5W1`), cited as `window_w1_majorana` | Discharged at the one-mode level. In general **OPEN**: operator-valued tempered distributions on `𝓢(ℝ⁴)`; the test-function side is no longer the blocker (Correction 1) — the field construction is |
| **W2** covariance | **PARTIAL** — ℤ₂ fermion parity only: `w2_parity` (`Rung5W2`), cited as `window_w2_parity` | Still partial, **price narrowed since Rung 5**: the one-particle mass-shell Poincaré representation stands (`MassShellMeasure`/`MassShellBoost`), its second quantization `Γ` stands on both Fock spaces (`FockPackaging*`), and strong continuity stands for translations and Lorentz, at one-particle and Fock level (`TranslationContinuity`, `LorentzContinuity`, `FockLorentz*` — unlock chain item 2). What remains: the covariance *equation for an actual field*, the geometric action on spacetime test functions `𝓢(ℝ⁴)` (the shell representation is momentum-side), and any interacting case |
| **W3** spectrum | **PARTIAL** — frame consistency for the trivial representation only: `w3_trivial` (`Rung5W3`), cited as `window_w3_trivial` | Still partial at the same price: Stone's theorem and the joint spectral calculus for commuting *unbounded* self-adjoint operators are absent from Mathlib (the corpus has only finite-dimensional Stone, `StoneFiniteDim*`). The re-pin states W3 in Fourier-support form (§2), which is statement-complete without that machinery |
| **W4** locality | **PROVED T1** at the model, algebraic content — `w4_majorana` (`Rung5W4`, `s = +1`, `spacelikeSep` trivially `True`: the model has no spacetime), cited as `window_w4_majorana`. (Creator-half CAR is unconditional T1 separately: `FieldOperators.createFermSmeared_anticommute`) | Discharged at the one-mode algebraic level. In general **OPEN**: a field on spacetime test functions with genuine support conditions — no corpus theorem; the re-pin's bundle states the general clause exactly |
| **W5** cyclicity | **REFUTED as framed** — `w5_framed_false` (`Rung5W5`): monomial-*range* density is false even for the free fermion. **Corrected form PROVED** — `w5_span_true`: span-density (in fact span = ⊤), cited as `window_w5_span_true` | Closed at the model in the corrected form, which is the literature's meaning. On the re-pin side, cyclicity is reconstruction content; its distribution-level input (positivity) is a bundle field (§2) |
| **W6** nontriviality | As framed (bosonic form): **PROVED but a FALSE POSITIVE** — `w6_majorana` (connected 4-point `−2 ≠ 0` for the *free* Majorana field; the bosonic criterion is fermion-blind), cited as `window_w6_majorana`. **Corrected form PROVED** — `w6_fermionic_wick`: with Koszul signs the connected 4-point vanishes identically (fermionic Wick), cited as `window_w6_fermionic_wick` | Closed at the model in the corrected form. The re-pin's nontriviality clause is the scalar Wick-defect (`NonGaussian`); a fermionic Wightman pin would need its own signed defect clause — unbuilt, named in §5 |

## §4. The old dependency ledger, re-audited

`WightmanAxioms.lean`'s closing ledger listed five gaps. Status
against the pinned tree and the current corpus:

1. **Schwartz distribution theory (`𝓢'`)** — **CLOSED.** Present
   in pinned Mathlib with Fourier on `𝓢'`
   (`TemperedDistribution.fourierTransformCLM`; OS dossier §4's
   grep-backed audit, same pinned checkout). The old ledger line
   is stale (Correction 1).
2. **Operator-valued distributions / quantum fields as such** —
   **still absent** as a general theory, in Mathlib and the
   corpus. Finite-mode smeared fields stand
   (`FieldOperators`, `OneModeFermion`, the Fock stacks); the
   general object is unbuilt.
3. **Poincaré representation theory for unbounded operators** —
   **partially closed, and the old line is partially stale.** The
   unitary one-particle representation on the mass shell, its
   second quantization, and strong continuity of both subgroups
   (one-particle and Fock level) all stand in the corpus (§3, W2
   row). Still absent: a joint topology / single-object
   representation of the full Poincaré group (fenced in
   `LorentzContinuity`'s dossier), and generator theory for
   unbounded operators (item under W3).
4. **The Wightman reconstruction theorem** — **pinned as a
   schema, holes named.** The OS re-pin pinned it with two
   parameterized holes; this brick supplies the second hole's
   concrete predicate (`SatisfiesWightmanPin`). The first hole —
   Bargmann–Hall–Wightman analytic continuation and
   edge-of-the-wedge — is **absent** from pinned Mathlib (0-hit
   greps in the OS dossier §4 audit, same pinned checkout).
   Filling it is research-scale; nothing at S–M is implied.
5. **Any interacting 4D example** — **open in mathematics**, not
   merely in formalization. Unchanged, and now stated by a Prop
   that could in principle be false (`InteractingWightmanStatement`).

## §5. Fences and surprises

**Fences held.** New module only; `WightmanAxioms.lean`,
`WightmanTargets.lean`, and all Rung-5 files unmodified. No
interacting existence is claimed; `InteractingWightmanStatement`
is unproved. The bundle is the **scalar (bosonic) form**: fields
of nonzero spin, the `2π`-rotation sign, and a signed fermionic
defect clause are beyond this pin, named here and in the module.
The stale header of `WightmanAxioms.lean` is flagged for the
S-editorial list, not edited. PARTIAL-δ is not implicated. Clay
parts closed: **0**.

**Surprises.**
1. The Rung-4 bundle's vacuity (§1, Correction 3) was not
   expected to fall through W5: range-density looked like the
   clause that would block junk data. It doesn't — for the
   scalar-multiple field on `H = ℂ`, every point is a length-1
   monomial (`polyApply [z] = z • Ω`), so density is free. The
   clause that actually carries content in the sharp targets is
   the *choice of data*, which is exactly what an `∃` over the
   data throws away.
2. One cosmetic friction, recorded: `local` is a reserved token
   in Lean 4, so the bundle's locality field is named `locality`.
   No statement was affected.
3. The spectrum clause stated cleanly with test-function-side
   Fourier machinery alone (an integral, an integrability lemma,
   an annihilator condition) — the distribution-side Fourier
   transform, though present in Mathlib, was not needed for the
   pin.

## §6. What this changes in the ledger

- `WightmanAxioms.lean`'s statement layer is **superseded** by
  `WightmanRepin.lean` §2–§4 as the Wightman pin of record; the
  old file stands unmodified as the historical pin, with §1 of
  this dossier as its correction sheet. Its genuine T1 content
  (the light-cone geometry) is load-bearing in the new pin
  (`IsLorentz`, `InSpectralSupport` are stated against
  `minkowskiInner`/`forwardLightCone`).
- `WightmanTargets.lean`'s six sharp definitions **stand as
  conditions on fixed data** (and Rung 5's verdicts against them
  stand); `SharpWightmanTarget` as an `∃`-bundle is **superseded**
  as an existence form and must not be cited as the existence
  target — the pin of record for existence is
  `InteractingWightmanStatement`.
- The OS reconstruction schema's Wightman-side hole now has its
  concrete predicate (`SatisfiesWightmanPin`); the remaining hole
  is analytic continuation alone, research-scale.
- **Unlock chain item 3 is closed; the chain is complete**
  (`numberOp` rename ✓, Fock-level Lorentz ✓, Wightman re-pin ✓).
