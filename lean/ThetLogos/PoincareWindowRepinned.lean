import ThetLogos.FockPackagingBos
import ThetLogos.FockPackagingFerm

namespace ThetLogos

open MeasureTheory Filter Topology
open scoped InnerProductSpace

/-!
# ThetLogos.PoincareWindowRepinned — Rung 9 Task 4, brick R9T4-B: the re-pinned windows, assembled

COMMISSION — Jeff's "fire all" (2026-11-04), Rung 9 Task 4 front, brick
R9T4-B. Contract: `rung9-task4-scoping-2026-11-04.md` and the audit
`rung9-task4-audit-2026-11-04.md` (brick R9T4-A). Base: main-tree HEAD
78354e0 (local commit; tree-identical to remote 6e77678b).

## K-R9T4 stands — reaffirmed on this module's face

The audit's verdict was **STATEMENT MISMATCH (K-R9T4 fires)**: the two
2026-10-11 window Props of `PoincareAction.lean` —
`OneParticleRep_window` (:293) and `SecondQuantization_window` (:323) —
are discharged **0 of 6 clauses exactly as stated**, and two of the six
(W1.1, W2.1, the homomorphism clauses) assert, read literally, the
*anti*-homomorphism law over the unrestricted `PoincareGroup`, which
the corpus's packaged representations do not satisfy. **The original
windows are NOT discharged as stated, permanently.** They are not
edited anywhere in this brick; they stand as the mismatch record.

This brick closes only the **re-pinned siblings** defined below,
`OneParticleRep_window_rp` and `SecondQuantization_window_rp`, which
carry exactly the audit's three corrections:

1. **Group scope.** Every quantifier over `PoincareGroup` (Lorentz
   component the full `LorentzGroup`) becomes `RPoincare` (Lorentz
   component `RestrictedLorentz`, the proper-orthochronous subgroup) —
   the group every landed representation is actually over, and the
   group the original windows' own docstrings price as the hypothesis
   ("(iv) the *restricted* (proper orthochronous) hypothesis") without
   the Props incorporating it.
2. **Composition order.** In Mathlib, `(e₂.trans e₁) x = e₁ (e₂ x)`:
   `trans` applies its first argument first. The originals write
   `U (g₁ * g₂) = (U g₁).trans (U g₂)`, which read literally is
   `U (g₁ * g₂) = U g₂ ∘ U g₁` — the anti-homomorphism law. The
   re-pinned clauses write the homomorphism law the landed theorems
   prove: `U (g₁ * g₂) = (U g₂).trans (U g₁)`.
3. **W1.3 in a.e. form.** The original representation-formula clause
   demands the identity at *every* `p : massShell m` for the
   wavefunction evaluation. Pointwise evaluation is not defined on
   `L²` classes, so that form is **not closeable for an `L²` carrier**
   (audit verdict). The re-pinned clause states the identity
   `=ᵐ[massShellMeasure m hm]` — which is exactly what the landed
   `shellU1_coeFn_ae` proves. Stating the a.e. form requires naming
   the shell measure, so the re-pinned one-particle Prop takes the
   extra parameter `hm : 0 < m` the original did not have.

## What is proved here — pure assembly, no new mathematics

* `OneParticleRep_window_rp_proved` — the re-pinned one-particle
  window at the corpus's packaged data (`h := shellLp m hm`,
  `U1 := shellU1 m hm`, `wavefn` the `Lp` coercion,
  `planeWave := phase`, `shellAct g := shellActR g.lor⁻¹ m hm`),
  assembled from `shellU1_mul`, `shellU1_one`, `shellU1_coeFn_ae`
  (`FockPackaging.lean`).
* `gammaFockU1_eq_gammaFock_shellU1` /
  `gammaFockFU1_eq_gammaFockF_shellU1` — the Γ-of-U1 link as named
  `rfl` theorems: the packaged Fock actions *are* `Γ` of `shellU1`
  by definition (see the `_U1` note below).
* `SecondQuantization_window_rp_bosonic` /
  `SecondQuantization_window_rp_fermionic` — the re-pinned Fock
  window for the bosonic packaged action (`gammaFockU1`, vacuum
  `boseVacLim`) and the fermionic one (`gammaFockFU1`, vacuum
  `fockVacLim`), assembled from `gammaFockU1_mul` / `gammaFockU1_one`
  / `gammaFock_vacuum` and `gammaFockFU1_mul` / `gammaFockFU1_one` /
  `gammaFockF_vacuum`. The only shim is W2.2's notation-level
  identification: the landed identity laws end in `1` (the `One` of
  `≃ₗᵢ`), the window writes `LinearIsometryEquiv.refl`; the two are
  definitionally equal, discharged by `Eq.trans` with `rfl`.

## The `_U1` note (audit §2, structural)

The original `SecondQuantization_window`'s parameter `_U1` is **never
used in its body**: no conjunct relates `GammaU` to `_U1`; the
tensor-factor formula `Γ(U1)(ψ₁ ⊗ ⋯ ⊗ ψₙ) = U1ψ₁ ⊗ ⋯ ⊗ U1ψₙ` lives
only in its docstring. The re-pinned sibling **mirrors that shape
deliberately** — same unused `_U1` parameter — because the window is a
statement about a packaged action's group law and vacuum invariance;
changing its arity would re-pin more than the audit's three
corrections license. The Γ-of-U1 link lives in the definitions
(`gammaFockU1 := gammaFock m hm (shellU1 m hm g)`,
`FockPackagingBos.lean:2197`; `gammaFockFU1`,
`FockPackagingFerm.lean:1647`) and is stated in Lean above as the two
named `rfl` link theorems.

## Strong continuity is a conjunct of NEITHER window — recorded, not proved

Strong continuity appears in neither the original Props' bodies nor
the re-pinned ones; in the originals it is docstring prose only. It is
**not** added as a conjunct here, and no joint-continuity Prop is
stated in this brick: no topology on `RPoincare` exists anywhere
in-tree, and choosing one is a pin decision, not assembly. The
continuity content that *is* landed (background, not conjuncts): the
corpus's own narrower window `StrongContinuity_window`
(`MassShellMeasure.lean:976` — translations, function level),
discharged by `strongContinuity_window_proved`
(`TranslationContinuity.lean:196`); packaged subgroup continuity:
`shellU1_translation_tendsto` (`FockPackaging.lean:248`),
`shellU1_lorentz_tendsto` (`LorentzContinuity.lean:744`),
`gammaFockU1_lorentz_tendsto` (`FockLorentzBos.lean:222`),
`gammaFockFU1_lorentz_tendsto` (`FockLorentzFerm.lean:206`). The
price of the narrower window is on `MassShellMeasure.lean`'s own
face: for translations, strong continuity is dominated convergence —
`tendsto_lintegral_of_dominated_convergence` applied to
`Fₙ(p) = ‖e^{iaₙ·p} − 1‖ₑ² · ‖ψ(p)‖ₑ²`, dominated by `4‖ψ‖² ∈ L¹`;
for the Lorentz part it needs density of `C_c` in `L²` and uniform
continuity on compacts. **Joint** strong continuity of the packaged
action in a topology on the full `RPoincare` remains the OPEN,
research-scale residue of Rung 9 Task 4 — not stated, not proved,
not claimed here.

## Scope fence

K-R9T4 stands: the original windows are NOT discharged as stated,
permanently; this brick closes only the re-pinned siblings above.
Task 4's continuum content — joint strong continuity, and the
interacting theory — remains FRONTIER / OPEN, untouched. Task 4 as
literally stated in 2026-10 (including boosts implemented at finite
modes) remains NOT CLOSEABLE: the finite-mode boost item is a proved
structural negative of the rung's own dossier. NO CLAIM; dials 0/4.
-/

/-- **T5 window, re-pinned (one-particle)** — the sibling of
    `PoincareAction.OneParticleRep_window` carrying exactly the
    R9T4-A audit's three corrections. Original clauses
    (`PoincareAction.lean:299–302`) beside the corrected ones:

    * W1.1, original: `(∀ g₁ g₂ : PoincareGroup, U1 (g₁ * g₂) = (U1 g₁).trans (U1 g₂))`
      — the anti-homomorphism law over the full group.
      Corrected R1.1: `(∀ g₁ g₂ : RPoincare, U1 (g₁ * g₂) = (U1 g₂).trans (U1 g₁))`.
    * W1.2, original: `(U1 1 = LinearIsometryEquiv.refl ℂ h)`.
      Corrected R1.2: unchanged in form; the `1` is `RPoincare`'s.
    * W1.3, original: `∀ (g : PoincareGroup) (ψ : h) (p : massShell m),
      wavefn (U1 g ψ) p = planeWave g.trans p * wavefn ψ (shellAct g p)`
      — pointwise at every `p`; not closeable for an `L²` carrier.
      Corrected R1.3: the same identity as an a.e. equality of
      functions w.r.t. `massShellMeasure m hm` (hence the extra
      parameter `hm`, absent from the original). -/
def OneParticleRep_window_rp (m : ℝ) (hm : 0 < m)
    (h : Type*) [NormedAddCommGroup h] [InnerProductSpace ℂ h] [CompleteSpace h]
    (U1 : RPoincare → (h ≃ₗᵢ[ℂ] h))
    (wavefn : h → massShell m → ℂ)
    (planeWave : Minkowski → massShell m → ℂ)
    (shellAct : RPoincare → massShell m → massShell m) : Prop :=
  (∀ g₁ g₂ : RPoincare, U1 (g₁ * g₂) = (U1 g₂).trans (U1 g₁)) ∧
  (U1 1 = LinearIsometryEquiv.refl ℂ h) ∧
  ∀ (g : RPoincare) (ψ : h),
    (fun p => wavefn (U1 g ψ) p) =ᵐ[massShellMeasure m hm]
      (fun p => planeWave g.trans p * wavefn ψ (shellAct g p))

/-- **T5 window, re-pinned (second quantization)** — the sibling of
    `PoincareAction.SecondQuantization_window` carrying the audit's
    corrections (i) and (ii). Original clauses
    (`PoincareAction.lean:331–333`) beside the corrected ones:

    * W2.1, original: `(∀ g₁ g₂ : PoincareGroup, GammaU (g₁ * g₂) = (GammaU g₁).trans (GammaU g₂))`.
      Corrected R2.1: `(∀ g₁ g₂ : RPoincare, GammaU (g₁ * g₂) = (GammaU g₂).trans (GammaU g₁))`.
    * W2.2, original: `(GammaU 1 = LinearIsometryEquiv.refl ℂ Fock.carrier)`.
      Corrected R2.2: unchanged (the landed `= 1` form is the same
      operator; `1` is definitionally `refl` for `≃ₗᵢ`).
    * W2.3, original: `∀ g : PoincareGroup, GammaU g vac = vac`.
      Corrected R2.3: `∀ g : RPoincare, GammaU g vac = vac`.

    The parameter `_U1` mirrors the original's shape exactly: it is
    unused in the body, as it is there — the Γ-of-U1 link lives in
    the definitions of the packaged actions and is stated as the
    `rfl` theorems `gammaFockU1_eq_gammaFock_shellU1` and
    `gammaFockFU1_eq_gammaFockF_shellU1` below. -/
def SecondQuantization_window_rp
    (h : Type*) [NormedAddCommGroup h] [InnerProductSpace ℂ h] [CompleteSpace h]
    (Fock : FockMarker)
    [NormedAddCommGroup Fock.carrier] [InnerProductSpace ℂ Fock.carrier]
    [CompleteSpace Fock.carrier]
    (_U1 : RPoincare → (h ≃ₗᵢ[ℂ] h))
    (GammaU : RPoincare → (Fock.carrier ≃ₗᵢ[ℂ] Fock.carrier))
    (vac : Fock.carrier) : Prop :=
  (∀ g₁ g₂ : RPoincare, GammaU (g₁ * g₂) = (GammaU g₂).trans (GammaU g₁)) ∧
  (GammaU 1 = LinearIsometryEquiv.refl ℂ Fock.carrier) ∧
  ∀ g : RPoincare, GammaU g vac = vac

/-- **T1 (the Γ-of-U1 link, bosonic):** the packaged bosonic Fock
    action is *by definition* the second quantization `gammaFock` of
    the one-particle action `shellU1`. This is the link the window
    Prop's unused `_U1` parameter does not state; it lives in the
    definition (`FockPackagingBos.lean:2197`) and is named here. -/
theorem gammaFockU1_eq_gammaFock_shellU1 (m : ℝ) (hm : 0 < m) (g : RPoincare) :
    gammaFockU1 m hm g = gammaFock m hm (shellU1 m hm g) :=
  rfl

/-- **T1 (the Γ-of-U1 link, fermionic):** the packaged fermionic
    Fock action is *by definition* `gammaFockF` of `shellU1`
    (`FockPackagingFerm.lean:1647`). -/
theorem gammaFockFU1_eq_gammaFockF_shellU1 (m : ℝ) (hm : 0 < m) (g : RPoincare) :
    gammaFockFU1 m hm g = gammaFockF m hm (shellU1 m hm g) :=
  rfl

/-- **T1 (assembly):** the re-pinned one-particle window holds for
    the corpus's packaged data: `h := shellLp m hm`,
    `U1 := shellU1 m hm`, `wavefn` the `Lp` coercion to a shell
    function, `planeWave := phase`, and
    `shellAct g := shellActR g.lor⁻¹ m hm` (the window leaves
    `shellAct` a free parameter; its docstring formula is `ψ(Λ⁻¹p)`).
    Clause R1.1 is `shellU1_mul` (`FockPackaging.lean:208`), R1.2 is
    `shellU1_one` (`FockPackaging.lean:231`), R1.3 is
    `shellU1_coeFn_ae` (`FockPackaging.lean:194`) with the right-hand
    side read through the definition of `oneParticleFun`
    (`MassShellMeasure.lean:878`). Pure assembly; no new
    mathematics. This does **not** discharge the original
    `OneParticleRep_window` — K-R9T4 stands. -/
theorem OneParticleRep_window_rp_proved (m : ℝ) (hm : 0 < m) :
    OneParticleRep_window_rp m hm (shellLp m hm) (shellU1 m hm)
      (fun Ψ => (Ψ : massShell m → ℂ)) phase
      (fun g => shellActR g.lor⁻¹ m hm) := by
  refine ⟨fun g₁ g₂ => shellU1_mul m hm g₁ g₂, shellU1_one m hm, ?_⟩
  intro g Ψ
  filter_upwards [shellU1_coeFn_ae m hm g Ψ] with p hp
  exact hp

/-- **T1 (assembly, bosonic):** the re-pinned second-quantization
    window holds for the bosonic packaged action
    `GammaU := gammaFockU1 m hm` on `BosonicFockLim`, vacuum
    `boseVacLim`, with `_U1 := shellU1 m hm`. Clause R2.1 is
    `gammaFockU1_mul` (`FockPackagingBos.lean:2204`); R2.2 is
    `gammaFockU1_one` (`FockPackagingBos.lean:2213`) followed by the
    definitional identification `1 = LinearIsometryEquiv.refl` for
    `≃ₗᵢ`; R2.3 is `gammaFock_vacuum` (`FockPackagingBos.lean:2179`)
    at `W := shellU1 m hm g`, read through the definition of
    `gammaFockU1`. This does **not** discharge the original
    `SecondQuantization_window` — K-R9T4 stands. -/
theorem SecondQuantization_window_rp_bosonic (m : ℝ) (hm : 0 < m) :
    SecondQuantization_window_rp (shellLp m hm) ⟨BosonicFockLim⟩
      (shellU1 m hm) (gammaFockU1 m hm) boseVacLim :=
  ⟨fun g₁ g₂ => gammaFockU1_mul m hm g₁ g₂,
   (gammaFockU1_one m hm).trans rfl,
   fun g => gammaFock_vacuum m hm (shellU1 m hm g)⟩

/-- **T1 (assembly, fermionic):** the re-pinned second-quantization
    window holds for the fermionic packaged action
    `GammaU := gammaFockFU1 m hm` on `FermionicFockLim`, vacuum
    `fockVacLim`, with `_U1 := shellU1 m hm`. Clause R2.1 is
    `gammaFockFU1_mul` (`FockPackagingFerm.lean:1654`); R2.2 is
    `gammaFockFU1_one` (`FockPackagingFerm.lean:1663`) with the same
    `1 = refl` identification; R2.3 is `gammaFockF_vacuum`
    (`FockPackagingFerm.lean:1627`) at `W := shellU1 m hm g`, read
    through the definition of `gammaFockFU1`. This does **not**
    discharge the original `SecondQuantization_window` — K-R9T4
    stands. -/
theorem SecondQuantization_window_rp_fermionic (m : ℝ) (hm : 0 < m) :
    SecondQuantization_window_rp (shellLp m hm) ⟨FermionicFockLim⟩
      (shellU1 m hm) (gammaFockFU1 m hm) fockVacLim :=
  ⟨fun g₁ g₂ => gammaFockFU1_mul m hm g₁ g₂,
   (gammaFockFU1_one m hm).trans rfl,
   fun g => gammaFockF_vacuum m hm (shellU1 m hm g)⟩

end ThetLogos
