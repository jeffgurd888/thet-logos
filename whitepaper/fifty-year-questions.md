# The Fifty-Year Questions, Formalized

**Thet-LOGOS whitepaper — September 2026**

Five questions have blocked fundamental physics for roughly fifty years.
This document states each one as precisely as the thet-logos framework
currently allows — and no more precisely than that.

The accompanying Lean 4 module (`lean/ThetLogos/BlockedQuestions.lean`,
compiled with `lake build`) contains every statement below in machine-checked
form. Each entry is one of two things:

- **A proved fragment (Tier T3)** — machine-checked, no gaps.
- **A labeled conjecture (Tier T5, `sorry`)** — a formalized *question*,
  never an answer. Each carries explicit promote/kill criteria: what would
  promote it to a result, and what would kill it.

A `sorry` here is a receipt for work not yet done. The ledger rule holds:
**Theorem ≠ Simulation ≠ Experiment ≠ Device.**

---

## Q1. The problem of time → thermal time as physical time

**The classical question.** Wheeler–DeWitt (1967): in canonical quantum
gravity the Hamiltonian constraint annihilates the wavefunction, leaving no
Schrödinger time parameter. Time will not quantize. Nearly sixty years later,
the problem is still open.

**Why it is blocked.** Every approach assumed background time, then lost it
in quantization. The blockage is structural: you cannot derive what you
assumed.

**The reformulation.** In thet-logos time is derived, never postulated. The
thermal triple `(ρ, D_F, β)` — information, geometry, heat — synthesizes the
modular generator `K = −ln ρ` and the flow `σ_s(a) = ρ^{is}aρ^{−is}`. The
question becomes *which state, and why that one* — a tractable question, not
a paradox.

**Status.**

- *Proved (T3):* at maximal ignorance the derived time is trivial —
  `blockedQ1_trivialAtMaxIgnorance`. If `ρ = I/N`, then `σ_s(a) = a` for every
  observable: nothing evolves. Machine-checked, no gaps. More generally,
  `[ρ, a] = 0 ⟹ σ_s(a) = a` (`diagFlow_trivial_of_commute`).
- *Open (T5):* `blockedQ1_physicalClock` — there exists a thermal triple whose
  modular frequency differences `β(λᵢ² − λⱼ²)` reproduce an observed clock
  spectrum up to a nonzero scale. **Promote:** exhibit the triple and the
  measured spectrum with the identity checked. **Kill:** proof that no modular
  flow can match real clock readings.

---

## Q2. Emergence of the continuum from finite structure

**The classical question.** Does smooth spacetime emerge from finite or
discrete structure? Every discrete approach faces the continuum limit.

**Why it is blocked.** The limit is uncontrolled: no error bounds, no
recovered locality — only heuristics.

**The reformulation.** Is there a *controlled* limit of finite thermal
triples — dimensions going to infinity, error bounds going to zero — that
recovers locality? The Triple Point and Synthesis lattice engines are first
sketches, honestly labeled toys, not answers.

**Status.**

- *Open (T5):* `blockedQ2_continuumLimit` — a `ContinuumLimitData` sequence
  whose error bound vanishes and whose `recoversLocality` predicate holds.
  **Promote:** exhibit the sequence with error bounds. **Kill:** proof that no
  such limit recovers locality.

---

## Q3. Three generations and the mass hierarchy

**The classical question.** Why three fermion generations, with mass ratios
spanning twelve orders of magnitude? The Standard Model accommodates the
pattern; it does not explain it.

**Why it is blocked.** No mechanism exists: in every formulation the Yukawa
couplings are inputs, not outputs.

**The reformulation.** Extend the one-generation finite triple (32 states)
with a mechanism that triples the construction and spreads the spectrum
hierarchically. Here the requirement is stated as a precise, checkable
predicate on Dirac spectra: `HasThreefoldHierarchy` — three nonempty
generations with within-generation splittings uniformly smaller than
between-generation gaps by a ratio `r < 1`.

**Status.**

- *Open (T5):* `blockedQ3_threeGenerations` — a spectrum carrying a threefold
  hierarchy exists. **Promote:** exhibit the spectrum, ideally from a tripled
  finite-triple construction. **Kill:** irrelevance — the framework may simply
  not be the right address for this question.

---

## Q4. Closed form for the spectral (mass) gap

**The classical question.** The Yang–Mills mass gap in its full form is a
Millennium problem: prove a positive lower bound on the spectrum, with a
closed form.

**Why it is blocked.** No closed form for the gap in terms of the theory's
inputs is known in any formulation.

**The reformulation (finite form).** The finite geometry's gap
`Δ = min{|λ| > 0}` is the mass-gap analogue. The question: is `Δ` an
elementary closed-form expression in the Yukawa inputs? "Closed form" is
itself formalized here, as a tiny expression language (`ClosedForm`:
variables, constants, addition, multiplication, square root), so the question
is machine-checkable.

**Status.**

- *Proved (T3):* the gap is positive — `blockedQ4_gapPositive`, from
  `spectralGap_pos`. The gap exists; its closed form does not.
- *Open (T5):* `blockedQ4_closedFormGap` — for any Dirac-spectrum function of
  the Yukawa inputs, the gap equals some `ClosedForm` expression in those
  inputs. **Promote:** exhibit the expression. **Kill:** proof that no such
  expression exists (expected to be very hard — stated honestly).

---

## Q5. From engine design to physical device

**The classical question.** Can the thermal cycles studied as finite-triple
engine designs ever do physical work? Fifty years of quantum-engine theory
have produced models, not machines coupled to new physics.

**Why it is blocked.** No laboratory system with finite-triple effective
dynamics and a controllable gap is known.

**The reformulation.** A laboratory realization is schematic data
(`LabRealization`): a Hilbert space, a working-fluid Hamiltonian of
spectral-action form, thermal baths, a closed cycle, and positive measured
work. The Otto engine's computed `W_net = 0.155279 > 0` is the T4 numerical
shadow of this T5 question — a design, not a device.

**Status.**

- *Open (T5):* `blockedQ5_physicalDevice` — a laboratory realization
  extracting positive work from a finite-triple thermal cycle exists.
  **Promote:** a laboratory proposal with Hamiltonian, baths, and readout —
  even a 2-state toy. **Kill:** a no-go theorem showing finite-triple engines
  cannot couple to work extraction.

---

## What this document is

Not answers. Scaffolding *poised* to receive answers: each fifty-year
blocker restated precisely enough that a machine can check any future claim
to have resolved it. The proved fragments are small and real; the open
questions are large and labeled. That asymmetry is the honest state of the
field, and this framework's contribution is to make the asymmetry
machine-readable.

*Theorem ≠ Simulation ≠ Experiment ≠ Device. A `sorry` is a question, not an
answer.*
