# Fock-Level Lorentz Strong Continuity — Dossier (2026-10-18)

**Verdict: STANDS — WHOLE, both statistics, no narrowing.** Unlock
chain item 2 (ratified by Jeff 2026-10-18; prerequisite item 1,
the `numberOp` rename, stands). The Lorentz brick
(`whitepaper/lorentz-continuity-2026-10-18.md`) discharged strong
continuity of the Lorentz subgroup at the **one-particle** level
and named the Fock-level transport as its fenced remainder:
"Fock-level Lorentz transport NOT free and NOT landed
(per-statistic proof + co-import fence; unpriced)". This brick is
the per-statistic proof, for **both** statistics. The
strong-continuity window of the free theory is now closed at
every level the corpus packages: translations and Lorentz, one
particle and Fock, subgroup-wise.

**T1 throughout: 14 strict theorem declarations (7 per module),
zero `sorry`/`admit`, zero `@[simp]`, headline axioms exactly the
standard three (`propext`, `Classical.choice`, `Quot.sound`).**

## What was owed

`FockPackaging` (215 T1) ported the one-particle Poincaré action
`shellU1` through the Γ functors to unitary group actions
`gammaFockU1` / `gammaFockFU1` on the assembled bosonic and
fermionic limit Fock spaces, with group law and **translation**
strong continuity transported. The Lorentz half of the packaged
action carried no continuity claim. Owed: for every Fock vector
`Ψ`, strong continuity at the identity (hence at every point, via
the group law) of `Λ ↦ Γ(shellU1 ⟨0, Λ⟩) Ψ`, `Λ ∈
RestrictedLorentz` with the topology of pointwise action
convergence from `LorentzContinuity`.

## What landed

Two new modules (nothing existing modified), mirroring the
packaging's two-module shape:

| module | content | strict count |
|---|---|---|
| `lean/ThetLogos/FockLorentzBos.lean` | bosonic transport | 7 |
| `lean/ThetLogos/FockLorentzFerm.lean` | fermionic transport | 7 |
| **brick total** | | **14** |

Program total: 3,201 + 14 = **3,215 strict**.

Targeted builds green: `lake build ThetLogos.FockLorentzBos`
(3,672 jobs), `lake build ThetLogos.FockLorentzFerm` (3,669
jobs); both `.olean`s present.

Headlines, bosonic (fermionic names differ only by the `F`
infixes: `gammaFockFU1_…`, `UmatF_…`, space `FermionicFockLim`,
domain `fermDomLim`):

```lean
theorem gammaFockU1_lorentz_tendsto (m : ℝ) (hm : 0 < m)
    (z : BosonicFockLim) :
    Tendsto (fun Λ : RestrictedLorentz => gammaFockU1 m hm ⟨0, Λ⟩ z)
      (𝓝 1) (𝓝 z)

theorem gammaFockU1_lorentz_tendsto_at (m : ℝ) (hm : 0 < m)
    (Λ₀ : RestrictedLorentz) (z : BosonicFockLim) :
    Tendsto (fun Λ : RestrictedLorentz => gammaFockU1 m hm ⟨0, Λ⟩ z)
      (𝓝 Λ₀) (𝓝 (gammaFockU1 m hm ⟨0, Λ₀⟩ z))
```

Support chain in each module (all T1): entry continuity
(`Umat_lorentz_tendsto` / `UmatF_lorentz_tendsto`); diagonal
kernel continuity with value `1`
(`gammaKernelLim_diag_lorentz_tendsto` /
`gammaKernelFermLim_diag_lorentz_tendsto`); the basis action
identity (`gammaFockU1_boseELim_lorentz` /
`gammaFockFU1_fockBasisLim_lorentz`); basis-vector continuity by
the squared-norm identity `‖Γe − e‖² = 2 − 2 Re γ`
(`…_basis_lorentz_tendsto`); finite-particle continuity by a
finite-sum squeeze (`…_dom_lorentz_tendsto`).

## Route

The translation transport of `FockPackagingBos` /
`FockPackagingFerm`, generalized at exactly one point: the
one-particle input. Those chains were built on two
filter-general kernel lemmas — the bosonic
`gammaKernelRect_tendsto_of_tendsto_filter` and the fermionic
`minorDet_tendsto_of_tendsto` — so the whole chain replays with:

* the parameter `a : Minkowski`, filter `𝓝 0`, and group element
  `⟨a, 1⟩` replaced by `Λ : RestrictedLorentz`, filter `𝓝 1`,
  and `⟨0, Λ⟩`;
* the one-particle input `shellU1_translation_tendsto` replaced
  by `shellU1_lorentz_tendsto` (LorentzContinuity, T1).

Entry continuity is then inner-product continuity against the
fixed basis vector; the diagonal kernel at a fixed configuration
is a fixed finite permanent (bosonic) / determinant (fermionic)
in the entries; basis vectors satisfy `‖Γ(Λ)e − e‖² = 2 − 2 Re
γ(Λ)` with `γ(Λ) → 1`; finite-particle vectors are squeezed by a
finite sum of basis distances; and the ε/3 extension by
unitarity (every `Γ(Λ)` is a linear isometry) over the dense
finite-particle domain closes the headline. Continuity at every
`Λ₀` follows the one-particle pattern verbatim: the
factorization `⟨0, Λ⟩ = ⟨0, Λ₀⟩ * ⟨0, Λ₀⁻¹ * Λ⟩`, the packaged
representation law `gammaFockU1_mul` / `gammaFockFU1_mul`, and
`tendsto_restricted_inv_mul`.

On the commission's expected "tensor-power step": **no tensor
power of the one-particle space is ever formed, and no new
tensor lemma was needed.** In this corpus's packaging the Γ
kernel in the concrete basis `shellONB` *is* the finite tensor
data — a basis vector's image is a kernel column, and its
continuity reduces to entry continuity through a finite
permanent/determinant. The tensor-power continuity is thereby
consumed at the kernel level, which is where the packaging put
it in the first place. Recorded here because the commission
priced the step as the brick's possible real content; the
content turned out to be the filter-generality the packaging
brick had already (silently) built in.

## Fences — what this does NOT give

* **Free Fock spaces only.** No interacting Fock continuity
  claim; nothing about any interacting theory, continuum limit,
  or Yang–Mills. Parts of any official Clay statement closed by
  this brick: **0**.
* **Subgroup-wise, not joint.** No topology on `RPoincare` is
  introduced. After this landing the packaged action is strongly
  continuous in the translation parameterization
  (`FockPackaging`) and in the Lorentz parameterization (this
  brick), separately — the same state of the art as at the
  one-particle level. Joint strong continuity in a product
  topology on the full group remains a separate, unclaimed
  statement.
* The topology on `RestrictedLorentz` is the one
  `LorentzContinuity` built (pointwise action convergence =
  entrywise matrix convergence). No other topology is claimed.

## Surprise (named, fence-relevant)

Unlock item 1 discharged the `numberOp`/`numberOp_basis`
collision between the two Fock *stacks* (`FermionicFock` vs
`BosonicAssembly`), certified by `FockCoImport.lean`, which
imports both stacks. The two **packaging** modules, however,
still cannot be co-imported with each other: both
`FockPackagingBos.lean` (line 1803) and
`FockPackagingFerm.lean` (line 1281) declare
`ThetLogos.inner_linearCombination_mixed` (a per-statistic
inner-product helper, different statements, same name) — found
by an import error when this brick's axiom probe first tried to
load both halves at once. Nothing in this brick needed the two
halves in one environment (the per-statistic module shape is
precisely the workaround, and each half's axiom check was run
separately), so the brick is unaffected; but the record should
not say "the co-import fence is down" without the qualifier:
**down at the stack level, still standing between the two
packaging modules**, for the same duplicate-name reason, at S
price to repair (rename one side, cf. the `adag`/`numberOp`
pattern). Not repaired here — out of this brick's scope.

## Verification (reproduce before citing)

* `lake build ThetLogos.FockLorentzBos` — green, 3,672 jobs,
  `.olean` present.
* `lake build ThetLogos.FockLorentzFerm` — green, 3,669 jobs,
  `.olean` present.
* Strict recount on comment-stripped source (line-initial
  `^(theorem|lemma) `): **7 + 7 = 14**. `@[simp]`: **0**.
  `sorry`/`admit` tokens in stripped source: **0**.
* `#print axioms` on `gammaFockU1_lorentz_tendsto`,
  `gammaFockU1_lorentz_tendsto_at`,
  `gammaFockU1_basis_lorentz_tendsto`,
  `gammaKernelLim_diag_lorentz_tendsto` (bosonic environment)
  and the four fermionic counterparts (fermionic environment —
  see the surprise above for why the checks are separate): each
  exactly `[propext, Classical.choice, Quot.sound]`.
* Program total: 3,201 + 14 = **3,215 strict**.
