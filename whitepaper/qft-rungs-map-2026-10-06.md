# The QFT Rungs: From the Finite Spectral Triple to Quantum Yang–Mills

**Date:** 2026-10-06
**Status:** Literature survey and project ledger (Tier T5 survey; citations are T1/T2-anchored)
**Purpose:** The precise mathematical ladder between the thet-logos finite spectral triple
and the Clay Yang–Mills mass-gap problem. This document maps the terrain; it does not
claim a route to the prize.

## How to read this map

- **Rung 0** is what thet-logos has actually proved (Tier T1, Lean 4, zero sorrys).
- **Rungs 1–4** are the climb. Each rung has four entries:
  1. **Theorem shape** — the rung stated as precisely as possible (theorem-shaped where the
     literature supports it; marked as programmatic where it does not).
  2. **ESTABLISHED** — real papers, real authors, real theorems. Every claim here carries
     a citation.
  3. **OPEN** — what is conjectural, incomplete, or disputed.
  4. **Lean 4 target** — concrete definitions and theorem statements to formalize, not vibes.
- **"Proved" vs "formal":** a computation can be mathematically rigorous (proved) without
  being machine-checked (formal). These are independent axes and this map never conflates them.
- **Updates:** as work proceeds, each rung accumulates dated ledger entries (T1/T2/T4/T5).
  Killed claims stay on the record.

---

## Rung 0 — Where we stand (T1, proved, 2026-10-05)

The thet-logos codebase (`lean/ThetLogos/`) contains a machine-checked finite real spectral
triple for the Standard Model: `FiniteSpectralTriple.lean`, `Scaffold32.lean` (32×32 Dirac
operator), `OrderOne.lean` / `OrderOneFull.lean` (order-one commutant), `CFKernel22*.lean`
(22-direction classification), `ExoticSectors.lean` (78 theorems: 8⊕2⊕2 exotic-sector
commutator structure, zero sorrys), `ModularFlux.lean` (`thermal_flux_vanishes`,
`exists_activeDriver`), `ModularTime.lean`, `ThermalKMS.lean`, `InnerFluctuations.lean`,
`ProductTriple.lean`, `SpectralAction.lean`, `SpectralActionFinite.lean`.

**Honest boundary (standing):** this is finite matrix geometry. It shares vocabulary with
the Clay problem (gauge structure, spectral gaps) and nothing else. No continuum limit,
no quantum field construction, no mass-gap theorem. Rungs 1–4 below are unbuilt.

---

## Rung 1 — Almost-commutative geometry and the spectral action

### Theorem shape

Let (M, g) be a compact 4-dimensional Riemannian spin manifold and F the finite real
spectral triple of KO-dimension 6 with algebra A_F = ℂ ⊕ ℍ ⊕ M₃(ℂ) (per generation).
For the product triple M × F and fluctuated Dirac operator D_A = D + A + JAJ⁻¹,
the spectral action S(D_A) = Tr(f(D_A/Λ)) admits, as Λ → ∞, the heat-kernel asymptotic
expansion

    Tr(f(D_A/Λ)) ~ Σ_k Λ^{4-2k} f_{4-2k} a_{2k}(D_A²),

whose first three Seeley–DeWitt coefficients a₀, a₂, a₄ reproduce the Einstein–Hilbert
action with cosmological term, the Weyl curvature term, and the full bosonic
Standard Model Lagrangian (gauge + Higgs), with the fermionic action ½⟨Jψ, D_A ψ⟩
supplying the matter sector.

### ESTABLISHED

- **The spectral action principle.** Chamseddine–Connes, "The spectral action
  principle," *Commun. Math. Phys.* 186 (1997) 731–750 (arXiv:hep-th/9606001):
  S(D,Λ) = Tr(f(|D|/Λ)) is gauge-invariant, depends only on the spectrum of D,
  and counts eigenvalues below the cutoff Λ.
- **Real structure and KO-dimension.** Connes, "Noncommutative geometry and
  reality," *J. Math. Phys.* 36 (1995) 6194–6231: real structure J, KO-dimension
  mod 8, first-order condition [[D,a],b°] = 0.
- **Classification selecting the SM.** Chamseddine–Connes, "Why the Standard
  Model," *J. Geom. Phys.* 58 (2008) 38–47 (arXiv:0706.3688): classification of
  irreducible finite real noncommutative geometries of KO-dimension 6; with an
  added quaternion-linearity hypothesis, the SM finite geometry (and k=4, i.e.
  16 fermions per generation) is singled out.
- **Neutrino mixing version.** Connes, "Noncommutative geometry and the standard
  model with neutrino mixing," *JHEP* 0611 (2006) 081 (arXiv:hep-th/0608226);
  Barrett, "A Lorentzian version of the non-commutative geometry of the standard
  model," arXiv:hep-th/0608221 (2006): independent derivation of the KO-dimension-6
  condition and resolution of fermion doubling.
- **The full heat-kernel computation.** Chamseddine–Connes–Marcolli, "Gravity and
  the standard model with neutrino mixing," *Adv. Theor. Math. Phys.* 11 (2007)
  991–1089 (arXiv:hep-th/0610241): via Gilkey's theorem on heat-kernel asymptotics
  [P. Gilkey, "The spectral geometry of a Riemannian manifold," *J. Diff. Geom.*
  10 (1975) 601–618], the coefficients of the expansion are computed explicitly
  (their Theorem 3.13 / §4): cosmological term, Einstein–Hilbert term with correct
  sign, Weyl term −(3f₀/10π²)∫C²√g d⁴x, Higgs kinetic and potential terms,
  gauge kinetic terms with the unification relation g₃² = g₂² = (5/3)g₁², and the
  non-minimal coupling −(af₀/12π²)∫R|φ|²√g d⁴x. The moduli space of admissible
  finite Dirac operators was analyzed (see also Ćaćić's work on moduli spaces of
  Dirac operators for finite spectral triples).
- **Textbook treatment.** van den Dungen–van Suijlekom, "Particle physics from
  almost-commutative spacetimes," *Rev. Math. Phys.* 24 (2012) 1230004
  (arXiv:1204.4604): comprehensive review making the block-matrix shape of D_F
  explicit. Connes–Marcolli, *Noncommutative Geometry, Quantum Fields and
  Motives*, AMS Colloquium Publications 55 (2008): the monograph tying the
  spectral action to the renormalization/motives program. Van Suijlekom,
  *Noncommutative Geometry and Particle Physics*, Springer (2015): textbook.
- **Higgs-mass episode (proved-then-patched, on the record).** Chamseddine–Connes,
  "The uncanny precision of the spectral action," *Commun. Math. Phys.* 293
  (2010) 867–897 (arXiv:0812.0165): the spectral action with big-desert RG
  running predicted a Higgs mass near ~170 GeV. The measured value is 125.09 GeV
  (ATLAS/CMS, 2012). Chamseddine–Connes, "Resilience of the spectral standard
  model," *JHEP* 09 (2012) 104 (arXiv:1208.1030): argued that RG running with a
  right-handed-neutrino threshold reconciles the prediction. **Ledger verdict:**
  this is a patched prediction, not a clean one; the framework survives but the
  episode stays on the record as a caution about "predictions" from the spectral
  action.

### OPEN

- **Lorentzian signature.** The product triple is Euclidean/Riemannian. A
  Lorentzian spectral triple with a working spectral action does not exist as a
  settled theory. Live approaches: Barrett's Lorentzian SM triple (2006);
  the **twisted spectral triple** program — Devastato–Lizzi–Martinetti, "Grand
  symmetry, spectral action and the Higgs mass," *JHEP* 01 (2014) 042
  (arXiv:1304.0415); Devastato–Martinetti, "Twisted spectral triple for the
  standard model and spontaneous breaking of the grand symmetry," *Math. Phys.
  Anal. Geom.* 20 (2017) (arXiv:1411.1320): a twisted first-order condition
  [[D,a]ρ, Jb*J⁻¹]ρ = 0 generates an extra scalar σ (stabilizing the electroweak
  vacuum) plus a vector field X_μ, with breaking to the SM obtained dynamically
  as a minimum of the spectral action. Recent: twist-generated torsion and
  Lorentz symmetry (Martinetti–Nieuviarts–Zeitoun, arXiv:2401.07848, 2024);
  Krein-space structure of the twisted SM (Martinetti, arXiv:2603.03216, 2026).
  **Note for our program:** in Connes–Moscovici the twist is ρ = σ_i for a
  modular automorphism group — a direct bridge to the thermal-time / modular-flux
  (φ) program in `ModularFlux.lean`. This is a live research seam, not an
  established result.
- **Three generations are input.** The classification selects the per-generation
  structure; the number of generations (3) is put in by hand.
- **Quantization of the spectral action itself** — see Rung 2.

### Lean 4 target (concrete)

Rung 1 splits into a feasible finite part and a hard analytic part:

1. **(Feasible now)** The finite-triple side is already T1 in thet-logos.
   Next formalizable theorems:
   - `inner_fluctuation_gauge : ∀ (A : InnerFluctuation F), gaugeGroup (fluctuatedDirac F A) = SMGaugeGroup` — inner fluctuations D ↦ D + A + JAJ⁻¹ produce exactly the SM gauge bosons (algebra-level statement; the representation theory is finite-dimensional).
   - `first_order_condition_stable : ∀ a b, ⁅⁅D_A, a⁆, bᵒᵖ⁆ = 0` — the first-order condition survives inner fluctuation (finite matrices; already the shape of `OrderOne.lean` results).
2. **(Hard, multi-year)** The heat-kernel expansion on M × F: formalize
   Seeley–DeWitt coefficients a₀, a₂, a₄ for a Laplace-type operator as
   `seelyDeWitt : (P : LaplaceTypeOperator) → (k : ℕ) → LocalInvariant`,
   then `spectral_action_expansion : Tr (f (D_A/Λ)) = Σ_k Λ^{4-2k} f_{4-2k} a_{2k} + o(Λ^{-N})`.
   This requires Mathlib heat-kernel/pseudodifferential infrastructure that does
   not currently exist — a legitimate multi-year dependency, to be logged, not
   wished away.
3. **(Speculation, marked)** A twisted-triple formalization
   (`twistedCommutator`, `twistedFirstOrder`) connecting ρ to the modular group
   σ^φ_s already in `ModularTime.lean`. Do not start until the untwisted Rung 1
   targets are T1.

---

## Rung 2 — Renormalization (Connes–Kreimer and the spectral action)

### Theorem shape

Perturbative renormalization is the Birkhoff decomposition of loops with values in
the character group of the Connes–Kreimer Hopf algebra H of Feynman graphs:
for a regularized character φ, φ = φ₋⁻¹ ⋆ φ₊ splits it into counterterm (φ₋) and
renormalized (φ₊) parts. Gauge Ward/Slavnov–Taylor identities generate a Hopf
ideal I ⊂ H, so the quotient H/I carries renormalization compatible with gauge
symmetry. Applied to the spectral action, one-loop counterterms have the same
spectral form as the bare action and can be subtracted within the spectral framework.

### ESTABLISHED

- **The Hopf algebra of renormalization.** Connes–Kreimer, "Renormalization in
  quantum field theory and the Riemann–Hilbert problem I," *Commun. Math. Phys.*
  210 (2000) 249–273 (arXiv:hep-th/9912092); Part II, *JHEP* 09 (2001) 024
  (arXiv:hep-th/0003188): the BPHZ recursion is the Birkhoff decomposition in
  the group dual to the commutative Hopf algebra of Feynman graphs (building on
  Kreimer's rooted-tree Hopf algebra, *Adv. Theor. Math. Phys.* 1998).
- **Gauge compatibility, made rigorous.** Van Suijlekom, "Renormalization of
  gauge fields: A Hopf algebra approach," *Commun. Math. Phys.* 276 (2007)
  773–798 (arXiv:hep-th/0610137): the Ward identities (abelian) and
  Slavnov–Taylor identities (non-abelian) generate a **Hopf ideal** in the
  Connes–Kreimer Hopf algebra; the quotient Hopf algebra is well-defined with
  the identities built in. This is a purely combinatorial, rigorous proof that
  renormalization is compatible with gauge symmetry.
- **Motivic depth.** Connes–Marcolli, "Renormalization and motivic Galois
  theory," *Int. Math. Res. Not.* 2004 (76) 4073–4091 (arXiv:math/0409306):
  the renormalization group as a Galois group; counterterms tied to mixed Tate
  motives (developed further with the Bloch–Esnault–Kreimer program and Brown's
  work on multiple zeta values in Feynman integrals).
- **One-loop renormalizability of the spectral action.** Van Nuland–van
  Suijlekom, "One-loop corrections to the spectral action," *JHEP* 05 (2022)
  207 (arXiv:2107.08485): perturbative quantization of the spectral action via
  background-field method; the action expands in higher Yang–Mills and
  Chern–Simons forms; the path integral over matrix fluctuations around a fixed
  noncommutative gauge background yields one-loop counterterms **of the same
  spectral form**, subtractable within the spectral framework; Ward identities
  give a fully spectral formulation of the quantum theory at one loop. The
  authors propose a "quantum effective spectral action" (sum of 1PI diagrams)
  valid at all energies.

### OPEN

- **All-loop order.** Van Nuland–van Suijlekom state the extension of their
  power-counting and diagrammatics to arbitrary loop order "will be reported
  elsewhere." As of 2026 it has not appeared. The all-loop renormalizability of
  the spectral action is **open**.
- **Wilsonian RG for the spectral action.** Deriving the low-energy SM
  Lagrangian from a *renormalized* (not bare) spectral action — the program the
  authors sketch — is unbuilt.
- **Relation to the physical SM renormalization group.** The spectral action is
  a bare action at the cutoff Λ; its RG flow down to collider energies is the
  standard (non-spectral) RG. A fully spectral RG flow is speculation.

### Lean 4 target (concrete)

Rung 2 is the most formalization-friendly rung after Rung 0, because it is
largely combinatorial:

1. **(Feasible now)** The Connes–Kreimer Hopf algebra of rooted trees:
   `CKHopfAlgebra : HopfAlgebra` with coproduct defined by admissible cuts,
   `birkhoffDecomposition : Character → Character × Character` and
   `BPHZ_eq_birkhoff : renormalizedRules = ...` — the recursion is finite
   combinatorics on trees; no analysis required. This is an ideal first
   "Rung 2" T1 target.
2. **(Feasible, moderate)** Van Suijlekom's Hopf-ideal theorem:
   `wardIdentities_ideal : Ideal H`, `isHopfIdeal wardIdentities_ideal`,
   `quotient_welldefined : HopfAlgebra (H ⧸ wardIdentities_ideal)`.
   The statement is algebraic; the hard part is formalizing Feynman-graph
   combinatorics with enough fidelity.
3. **(Hard)** The van Nuland–van Suijlekom one-loop theorem: requires the
   perturbative expansion of Tr(f(D/Λ)) in higher Yang–Mills/Chern–Simons forms
   plus background-field path-integral machinery. Depends on Rung 1's analytic
   infrastructure. Log as a downstream target, not a starting point.

---

## Rung 3 — Constructive QFT (the existence rung)

### Theorem shape (programmatic — this is the open problem)

There exists a probability measure μ on S'(ℝ⁴) (tempered distributions, with
values in the appropriate gauge-field configuration space) satisfying the
Osterwalder–Schrader axioms (Euclidean covariance, reflection positivity,
regularity, clustering), whose OS reconstruction yields a quantum Yang–Mills
theory with compact simple gauge group G satisfying the Wightman axioms
(or Haag–Kastler axioms), non-trivial (non-Gaussian) and Poincaré-covariant.

### ESTABLISHED

- **The axiomatic frameworks.** Wightman, "Quantum field theory in terms of
  vacuum expectation values," *Phys. Rev.* 101 (1956) 860–866; Gårding–Wightman,
  *Ark. Fys.* 28 (1964); Streater–Wightman, *PCT, Spin and Statistics, and All
  That*, Benjamin (1964): the Wightman axioms. Haag–Kastler, "An algebraic
  approach to quantum field theory," *J. Math. Phys.* 5 (1964) 848–861: nets of
  local C*-algebras (algebraic QFT). Osterwalder–Schrader, "Axioms for Euclidean
  Green's functions," *Commun. Math. Phys.* 31 (1973) 83–112; Part II,
  *Commun. Math. Phys.* 42 (1975) 281–305: the Euclidean axioms **and** the
  reconstruction theorem (OS ⇒ Wightman).
- **What has actually been constructed.** Glimm–Jaffe, *Quantum Physics: A
  Functional Integral Point of View*, Springer (1981; 2nd ed. 1987): the
  constructive bible — P(φ)₂, φ⁴₂, φ⁴₃, Yukawa₂. Brydges–Fröhlich–Seiler, "On
  the construction of quantized gauge fields," *Ann. Phys.* 121 (1979) and
  sequels: the **2D abelian Higgs model — the only complete example of an
  interacting gauge theory satisfying the axioms** (as the Jaffe–Witten problem
  description itself notes).
- **φ⁴₃ via stochastic quantization.** Hairer, "A theory of regularity
  structures," *Invent. Math.* 198 (2014) 269–504; Gubinelli–Hofmanova (2018),
  Barashkov–Gubinelli (2020).
- **φ⁴₄ is trivial.** Aizenman–Duminil-Copin, "Marginal triviality of the
  scaling limits of critical 4D Ising and φ⁴ models," *Ann. Math.* 194 (2021)
  163–235: the 4D scalar route is closed — which sharpens why YM₄ is the only
  remaining candidate for a non-trivial interacting 4D QFT.
- **Lattice gauge theory.** Osterwalder–Seiler, "Gauge field theories on a
  lattice," *Ann. Phys.* 110 (1978) 440–471: rigorous lattice construction;
  mass gap and area law at strong coupling (small β). Seiler, *Gauge Theories
  as a Problem of Constructive Quantum Field Theory and Statistical Mechanics*,
  Lect. Notes Phys. 159 (1982).
- **Balaban's renormalization-group program.** T. Balaban, series in
  *Commun. Math. Phys.* (1987–1995, ~500 pages): block-spin RG for lattice
  gauge theory; proves existence and convergence to the continuum limit at
  small bare coupling. **It does not prove a positive mass gap**, and critics
  (including Jaffe) note open issues at the large-field control step. This is
  the closest any program has come to the Clay existence half — and it is still
  short.
- **No interacting 4D QFT satisfying all Wightman axioms has ever been
  constructed.** This is the precise content of the Clay problem's difficulty
  and is undisputed in the literature.
- **Recent axiomatic work.** Strocchi, "Axioms for Quantum Gauge Fields,"
  arXiv:2112.08575 (2021): a proposal for axioms adapted to gauge fields
  (proposal, not a construction).

### OPEN

- The 4D Yang–Mills construction itself: continuum limit of lattice YM with
  control uniform enough to verify OS axioms, especially **reflection
  positivity** and **clustering** for gauge-invariant observables.
- OS reconstruction for gauge theories: the tension between gauge fixing
  (needed for the functional integral) and gauge invariance (needed for the
  physical Hilbert space) has no fully rigorous resolution in 4D.
- Stochastic quantization of YM₄ (Chandra–Chevyrev–Hairer–Shen program):
  2D/3D results exist; 4D is open.
- **Almost-commutative quantization:** nothing beyond van Nuland–van
  Suijlekom's one-loop result (Rung 2) exists. There is no non-perturbative
  quantization of the spectral action, and no construction of a QFT on an
  almost-commutative background M × F. Any claim otherwise is invention.

### Lean 4 target (concrete)

Rung 3 formalization must be staged by difficulty; the honest order is
kinematics → lattice → axioms → reconstruction:

1. **(Feasible now)** Lattice Yang–Mills kinematics: `WilsonAction`,
   `wilsonMeasure` (product Haar measure — Mathlib has Haar measure
   infrastructure), `plaquetteVariable`, gauge invariance
   `gauge_invariant wilsonAction` as finite-dimensional statements. This is
   real, checkable, and useful.
2. **(Feasible, moderate)** Reflection positivity on the lattice:
   `reflectionPositive : Prop` for the lattice measure, chessboard estimates
   (Fröhlich–Simon–Spencer 1976) as combinatorial inequalities. (Note: an
   independent AI-assisted effort, `mrdouglasny/reflection-positivity`, is
   attempting exactly this — track, don't duplicate blindly.)
3. **(Hard)** The OS axioms as Lean structures over Euclidean correlators;
   the Wightman axioms as structures over operator-valued distributions.
   **Blocked on:** Mathlib has no distribution theory adequate for
   operator-valued tempered distributions (2026). Log the dependency.
4. **(Very hard)** The OS reconstruction theorem. Do not attempt before (3).
5. **(Programmatic)** The Clay existence statement itself as a formal `Prop`
   — valuable as a *statement* even with the proof absent (see Rung 4).

---

## Rung 4 — The mass gap (the Clay statement)

### The Clay statement, precisely

Jaffe–Witten, "Quantum Yang–Mills theory," official Clay Mathematics Institute
problem description (2000); reprinted in Carlson–Jaffe–Wiles (eds.), *The
Millennium Prize Problems*, AMS/Clay (2006):

> **Yang–Mills Existence and Mass Gap.** Prove that for any compact simple gauge
> group G, a non-trivial quantum Yang–Mills theory exists on ℝ⁴ and has a mass
> gap Δ > 0. Existence includes establishing axiomatic properties at least as
> strong as those cited in Streater & Wightman (1964), Osterwalder & Schrader
> (1973) and Osterwalder & Schrader (1975).

Unpacked: (i) **construct** the theory — a QFT satisfying Wightman axioms (or
OS axioms + reconstruction), non-trivial (not free/Gaussian); (ii) **prove**
that the Hamiltonian's spectrum satisfies spec(H) ⊂ {0} ∪ [Δ, ∞) for some
Δ > 0, i.e. inf(spec(H) ∖ {0}) > 0 — the least massive glueball is strictly
massive. Note the problem demands this **for any compact simple G**, not just
SU(3).

### ESTABLISHED

- **Lattice mass gap at strong coupling.** Osterwalder–Seiler (1978): at small
  β (strong coupling), the lattice theory has exponential clustering — a mass
  gap — and Wilson-loop area law. This is a theorem about the *lattice*
  regularized theory, not the continuum.
- **Numerical evidence.** Lattice QCD computations show a glueball spectrum
  with the lightest state near ~1.7 GeV. This is evidence, not proof, and the
  Clay problem explicitly requires proof.
- **Undecidability of the *general* spectral gap.** Cubitt–Perez-Garcia–Wolf,
  "Undecidability of the spectral gap," *Nature* 528 (2015) 207–211
  (arXiv:1502.04573; full version *Forum of Mathematics, Pi* 10 (2022) e14):
  no algorithm decides, for an *arbitrary* translation-invariant 2D lattice
  Hamiltonian, whether it is gapped or gapless in the thermodynamic limit
  (reduction from the halting problem). **Ledger caution:** this does NOT imply
  the YM mass gap is undecidable or unprovable — YM is one specific
  Hamiltonian, not an arbitrary one. It warns against expecting a *generic*
  gap-deciding algorithm, nothing more.

### Why finite-matrix spectral gaps do not transfer

This is the load-bearing negative result for our program, stated plainly:

1. **Different objects.** The Clay gap is inf(spec(H) ∖ {0}) for H the
   Hamiltonian of a *constructed 4D QFT*. A gap in spec(D_F) for a 32×32
   matrix is a fact about a finite Dirac operator. No theorem connects them.
2. **Branch crossings.** A finite-matrix "gap" is typically a minimum over
   eigenvalue branches; at crossings the gap function is non-smooth and can
   close. The thet-logos Q4 amendment (2026-10-05, `BlockedQuestions.lean`)
   records exactly this obstruction, plus the unproved sectoral-factorization
   lemma it would need.
3. **No thermodynamic/continuum limit.** A gap that holds at finite volume or
   finite matrix size need not survive any limit — the limit itself is Rung 3's
   open problem.
4. **Conditional lemmas don't compose into theorems.** The existing
   spectral-gap result in thet-logos is a conditional finite-matrix lemma, not
   a mass-gap theorem. This map re-affirms that boundary.

### OPEN

Everything except the lattice strong-coupling gap: the continuum gap for any
G, the uniformity in G, and the connection to confinement.

### Lean 4 target (concrete)

1. **(Feasible now, high value)** Formalize the Clay *statement* as a Lean
   `Prop`, even with no proof:
   ```lean
   structure ClayYangMills (G : CompactSimpleGroup) : Prop where
     theory : WightmanQFT G        -- satisfies axioms ≥ Streater–Wightman / OS
     nontrivial : ¬ IsGaussian theory
     gap : ∃ Δ > 0, ∀ E ∈ spectrum (hamiltonian theory), E = 0 ∨ E ≥ Δ
   ```
   A machine-checked *statement* of the problem is itself a contribution: it
   pins what "solving it" means and every partial result can be measured
   against it. (Caution: hobby repos have formalized weakened lookalikes with
   `sorry`'d fields — ours must carry the real axiom content or be labeled
   conditional.)
2. **(Feasible)** The non-transfer results as *negative* theorems:
   `gap_branch_crossing : ∃ (D : FinMatrix), gapClosedUnderPerturbation D`
   — a concrete 2×2 or 4×4 example where an arbitrarily small perturbation
   closes the gap at a branch crossing. This turns the Q4 obstruction into T1.
3. **(Programmatic)** Any verified implication of the form
   `latticeGapUniform → continuumGap` with explicit hypotheses — the day such
   a conditional theorem exists in Lean, the open hypotheses become the exact
   shopping list for Rung 3.

---

## The formalization landscape (as of 2026-10)

| Effort | What it is | Status |
|---|---|---|
| **Mathlib** | The Lean mathematical library | Extensive measure theory, probability, functional analysis, Haar measure. **No QFT**: no Wightman/OS/Haag–Kastler axioms, no distribution theory adequate for operator-valued fields, no constructive QFT. |
| **thet-logos** (this program) | Finite real spectral triple, SM | The only machine-checked finite-spectral-triple formalization (T1). Rung 0 complete; Rungs 1–4 open. |
| **deicyde/qft** | Lean 4 QFT formalization built with AutoformBot (Meta) | Nascent; explicitly guided by the YM mass-gap problem; multi-book structure (constructive QFT, Segal axioms, Balaban RG, differential geometry). Early-stage, worth tracking. |
| **mrdouglasny/pphi2**, **mrdouglasny/reflection-positivity** | AI-assisted Lean formalization of constructive-QFT infrastructure | Nascent; unusually honest gap documentation (P(φ)₂ guide, RP layering). Worth tracking; do not duplicate blindly. |
| **ember-research-lab/spectral-physics-lean**, **jagg-ix/spectral-physics-lean** | Hobby Lean repos on spectral geometry / YM gap | Unverified, AI-assisted; the latter is at least explicit about what it does *not* prove (Wightman axioms as bare Props, OS reconstruction `sorry`'d). Treat as exploratory, not established. |
| **the-eriksson-programme** | Hobby Lean formalization of lattice-YM cluster expansion | AI-assisted; honest ledger of open vs closed items. Exploratory. |
| Cautionary: **piqos "millennium proof" case study** | Purported Lean proofs of all six Clay problems | Independently audited and found to be tautologies/`rfl`-disguised trivialities (documented at `danofairanks/piqos---ai---research-public-`, case study 2026-09-03). The standing lesson: a Lean file *named* after a theorem proves nothing until the statement is checked. |

**Strategic read:** the formalization field is wide open. The credible play is to
formalize *established* rungs first — Rung 1's finite side (done), Rung 2's
combinatorics (CK Hopf algebra, van Suijlekom's Hopf-ideal theorem), Rung 3's
lattice kinematics — and to formalize the Clay *statement* precisely, so that
every future partial result is measured against a fixed target. Formalizing
open problems' *proofs* before their *statements* is how the cautionary cases
above went wrong.

---

## Recent needle-movers (2023–2026)

- **Twisted spectral triples → Lorentz/time.** Torsion from twists and the
  Lorentz group inside twisted unitaries (Martinetti–Nieuviarts–Zeitoun,
  arXiv:2401.07848, 2024); "Emergence of Time from a Twisted Spectral Triple
  in Almost-Commutative Geometry" (arXiv, 2025); Krein structure of the twisted
  SM (Martinetti, arXiv:2603.03216, 2026). The twist↔modular-automorphism link
  (ρ = σ_i) is the live seam connecting this program to our modular-flux (φ)
  work. CIRM (Marseille) hosted "Applications of noncommutative geometry to
  gauge theories, field theories and quantum spacetimes" (April 2025) — the
  field is active, not dormant.
- **φ⁴₄ triviality** (Aizenman–Duminil-Copin, *Ann. Math.* 194 (2021)):
  closes the 4D scalar route; YM₄ stands alone as the candidate interacting 4D QFT.
- **Stochastic quantization of YM** (Chandra–Chevyrev–Hairer–Shen and
  follow-ups): 2D/3D constructions advance; 4D remains open.
- **One-loop spectral action** (van Nuland–van Suijlekom, 2022): the most
  recent major quantum result in the NCG program; all-loop order still open.
- **Gauge-field axioms proposal** (Strocchi, arXiv:2112.08575, 2021):
  axioms adapted to gauge fields — a proposal that would reshape what "the
  axioms" in the Clay statement could mean, if adopted. Not established.

---

## The ledger (standing entries)

1. **2026-10-06 — Map created.** Rungs 0–4 surveyed against the literature.
   Every "ESTABLISHED" claim above carries a citation; everything else is
   marked OPEN or speculation.
2. **What this map does NOT claim:** a route to the Clay prize; that any rung
   is "almost done"; that formalizing a statement is progress toward its proof;
   that the NCG program is the *only* or *best* route to YM₄ (Balaban's RG and
   stochastic quantization are independent live programs).
3. **Update rule:** new results enter as dated entries under their rung with
   tier labels (T1 machine-checked / T2 hand-verified / T4 numerical / T5
   interpretation). Killed claims return only as new, weaker entries supported
   by proof — per the standing relabeling rule.
4. **The three hardest single facts on this map** (for prioritization):
   - (a) No interacting 4D QFT satisfying the Wightman axioms has ever been constructed.
   - (b) Balaban's ~500-page RG program — the closest approach — proves no mass gap.
   - (c) The spectral action's quantization stops at one loop.
   Any plan that does not route through (a)–(c) is not a plan.

---

## References (as cited)

- Chamseddine–Connes, "The spectral action principle," *Commun. Math. Phys.*
  186 (1997) 731–750. arXiv:hep-th/9606001.
- Connes, "Noncommutative geometry and reality," *J. Math. Phys.* 36 (1995)
  6194–6231.
- Chamseddine–Connes, "Why the Standard Model," *J. Geom. Phys.* 58 (2008)
  38–47. arXiv:0706.3688.
- Connes, "Noncommutative geometry and the standard model with neutrino
  mixing," *JHEP* 0611 (2006) 081. arXiv:hep-th/0608226.
- Barrett, "A Lorentzian version of the non-commutative geometry of the
  standard model," arXiv:hep-th/0608221 (2006).
- Chamseddine–Connes–Marcolli, "Gravity and the standard model with neutrino
  mixing," *Adv. Theor. Math. Phys.* 11 (2007) 991–1089. arXiv:hep-th/0610241.
- Chamseddine–Connes, "The uncanny precision of the spectral action,"
  *Commun. Math. Phys.* 293 (2010) 867–897. arXiv:0812.0165.
- Chamseddine–Connes, "Resilience of the spectral standard model," *JHEP* 09
  (2012) 104. arXiv:1208.1030.
- Gilkey, "The spectral geometry of a Riemannian manifold," *J. Diff. Geom.*
  10 (1975) 601–618.
- van den Dungen–van Suijlekom, "Particle physics from almost-commutative
  spacetimes," *Rev. Math. Phys.* 24 (2012) 1230004. arXiv:1204.4604.
- Connes–Marcolli, *Noncommutative Geometry, Quantum Fields and Motives*,
  AMS Colloquium Publ. 55 (2008).
- Van Suijlekom, *Noncommutative Geometry and Particle Physics*, Springer (2015).
- Devastato–Lizzi–Martinetti, "Grand symmetry, spectral action and the Higgs
  mass," *JHEP* 01 (2014) 042. arXiv:1304.0415.
- Devastato–Martinetti, "Twisted spectral triple for the standard model and
  spontaneous breaking of the grand symmetry," *Math. Phys. Anal. Geom.* 20
  (2017). arXiv:1411.1320.
- Martinetti–Nieuviarts–Zeitoun, arXiv:2401.07848 (2024); Martinetti,
  arXiv:2603.03216 (2026).
- Connes–Kreimer, "Renormalization in quantum field theory and the
  Riemann–Hilbert problem I," *Commun. Math. Phys.* 210 (2000) 249–273.
  arXiv:hep-th/9912092; Part II, *JHEP* 09 (2001) 024. arXiv:hep-th/0003188.
- Van Suijlekom, "Renormalization of gauge fields: A Hopf algebra approach,"
  *Commun. Math. Phys.* 276 (2007) 773–798. arXiv:hep-th/0610137.
- Van Nuland–van Suijlekom, "One-loop corrections to the spectral action,"
  *JHEP* 05 (2022) 207. arXiv:2107.08485.
- Connes–Marcolli, "Renormalization and motivic Galois theory," *Int. Math.
  Res. Not.* 2004 (76) 4073–4091. arXiv:math/0409306.
- Wightman, *Phys. Rev.* 101 (1956) 860–866; Streater–Wightman, *PCT, Spin
  and Statistics, and All That*, Benjamin (1964).
- Haag–Kastler, *J. Math. Phys.* 5 (1964) 848–861.
- Osterwalder–Schrader, *Commun. Math. Phys.* 31 (1973) 83–112; *Commun. Math.
  Phys.* 42 (1975) 281–305.
- Glimm–Jaffe, *Quantum Physics: A Functional Integral Point of View*,
  Springer (1981; 2nd ed. 1987).
- Brydges–Fröhlich–Seiler, "On the construction of quantized gauge fields,"
  *Ann. Phys.* 121 (1979) and sequels.
- Osterwalder–Seiler, "Gauge field theories on a lattice," *Ann. Phys.* 110
  (1978) 440–471.
- Seiler, *Gauge Theories as a Problem of Constructive Quantum Field Theory
  and Statistical Mechanics*, Lect. Notes Phys. 159 (1982).
- Balaban, series on the RG approach to lattice gauge theory, *Commun. Math.
  Phys.* (1987–1995).
- Hairer, "A theory of regularity structures," *Invent. Math.* 198 (2014)
  269–504.
- Aizenman–Duminil-Copin, "Marginal triviality of the scaling limits of
  critical 4D Ising and φ⁴ models," *Ann. Math.* 194 (2021) 163–235.
- Strocchi, "Axioms for Quantum Gauge Fields," arXiv:2112.08575 (2021).
- Jaffe–Witten, "Quantum Yang–Mills theory," Clay Mathematics Institute
  problem description (2000); in Carlson–Jaffe–Wiles (eds.), *The Millennium
  Prize Problems*, AMS/Clay (2006).
- Cubitt–Perez-Garcia–Wolf, "Undecidability of the spectral gap," *Nature*
  528 (2015) 207–211. arXiv:1502.04573.

*End of map. Next update appends dated ledger entries; nothing here is edited
retroactively.*
