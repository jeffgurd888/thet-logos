# Literature Ledger — Causal Structure in Noncommutative Geometry
**For Bridge Span 5 (causality), thet-logos Lorentzian bridge**
Date: 2026-10-07 · Tier: **T5 (literature survey)** · Status: survey only — no theorems claimed, no Lean/numerics touched, no Lorentzian-physics claims beyond what the papers state.

## Scope

The question Span 5 must answer: can a FINITE *-algebra carry a causal cone at all, or is causality irreducibly manifold-level? This ledger collects what the literature says, axiom by axiom, and classifies each axiom as (a) purely algebraic — statable over a finite *-algebra with no points — versus (b) requiring points/manifold (separating points, compactness, global hyperbolicity, topology induced by the order). That classification is the deliverable.

Two frameworks are surveyed:

1. **Franco–Eckstein** (top-down): causality out of a Dirac operator via an operatorial cone condition with a fundamental symmetry J. Lorentzian spectral triple (A, Ã, H, D, J).
2. **Besnard** (bottom-up): isocones — abstract cone axioms on C*-algebras modeling causal functions, Gelfand-style duality via toposets. No Dirac operator involved.

---

## 1. Franco's causal cone — exact axioms

Source: Nicolas Franco, "An algebraic formulation of causality for noncommutative geometry", arXiv:1212.5171 [math-ph] (Dec 2012, v2/v3 Jan–May 2013; v2/v3 adds complete proof for globally hyperbolic manifolds and a distance-formula constraint). The cone is defined in Definition 4 of that paper; the recovery theorem is Theorem 7 (v2/v3); restated as Definition 13 / Theorem 14 in Franco–Eckstein, arXiv:1409.1480.

Let (A, Ã, H, D, J) be a Lorentzian spectral triple (A ideal in the preferred unitisation Ã, D Dirac-type, J fundamental symmetry of a Krein space). A **causal cone** C ⊂ Ã is a subset satisfying:

- **(F1)** ∀ a ∈ C, a* = a. (Hermitian elements only)
- **(F2)** ∀ a, b ∈ C, a + b ∈ C. (stability under sum)
- **(F3)** ∀ a ∈ C, ∀ λ ≥ 0, λa ∈ C. (positive homogeneity)
- **(F4)** ∀ x ∈ ℝ, x·1 ∈ C. (all real multiples of the unit, including negative)
- **(F5)** The closure of the complex-linear span of C equals Ã: span_ℂ(C)̅ = Ã. (spanning, in C*-norm)
- **(F6)** ∀ a ∈ C, ∀ φ ∈ H, ⟨φ, J[D, a]φ⟩ ≤ 0. (operatorial condition: the Krein form of the commutator is negative semidefinite)

The cone induces an order on the state space S(Ã):

- **(F7)** ∀ ω, η ∈ S(Ã), ω ≼ η iff ω(a) ≤ η(a) for all a ∈ C.

Motivating/validating result (Theorem 7 of arXiv:1212.5171 v2/v3; Franco–Eckstein 2013):

- **(F8 — recovery)** For a commutative Lorentzian spectral triple constructed from a complete globally hyperbolic manifold M, the relation ≼ restricted to the "physical pure states" M(Ã) = {ω ∈ P(Ã) : A ⊄ ker ω} ≅ P(A) ≅ M corresponds to the usual causal relation on M.

Notes on (F4): because negative constants are in the cone, ≼ is reflexive by construction (the trivial order ω ≼ ω always holds). The cone axiomatizes the **causal** (reflexive) order; there is no separate cone for the **chronological** (strict) relation.

---

## 2. Besnard's follow-ups

Sources: Fabien Besnard, "Two roads to noncommutative causality", arXiv:1508.01917 (review, updated Aug 2021; the isocone program started in Besnard [2009], cited therein as [6]); Proposition on causal functions from globally hyperbolic spacetimes is Besnard [2009], recalled as Proposition 11 in arXiv:1409.1480.

### 2a. Four fundamental hypotheses (motivation layer)

From the review (§2), for the set C of "causal observables" inside a Jordan algebra O:

- **(H0) Jordan paradigm:** C is a subset of a Jordan algebra O. (He argues a Jordan algebra suffices for the C*-paradigm of states/observables; later specializes to JB-algebras for functional calculus.)
- **(H1) Functional stability:** if o ∈ C and f is real non-decreasing, then f(o) ∈ C. ("a clock followed by a non-decreasing computation is still a clock")
- **(H2) Separation:** C separates the pure states of O.
- **(H3) Saturation:** every observable with non-decreasing Gelfand transform (p₁ ≼ p₂ ⇒ p₁(o) ≤ p₂(o)) is in C.

Under saturation one derives sum-stability, norm-closedness, and the working axioms. Besnard is candid: H2/H3 are "acts of faith" (his words); in the classical case H2 needs strong causality.

### 2b. The isocone axioms (working layer, Definition 1 of the review)

Let A be a unital C*-algebra, Re(A) its self-adjoint part. A non-empty set I ⊂ Re(A) is an **isocone** if:

- **(B1)** I ⊂ Re(A). (self-adjoint elements)
- **(B2)** ∀ φ : ℝ → ℝ continuous non-decreasing, a ∈ I ⇒ φ(a) ∈ I. (stability under non-decreasing continuous functional calculus)
- **(B3)** ∀ a, b ∈ I, a + b ∈ I. (stability under sum)
- **(B4)** I is norm-closed.
- **(B5)** I separates the states of A.

The pair (I, A) is an **I*-algebra**. The induced order on pure states P(A): φ ≼_I ψ iff φ(a) ≤ ψ(a) ∀ a ∈ I (equation (4) of the review).

What Besnard adds/changes relative to Franco:

1. **No Dirac operator, no J.** The isocone program "does not yet make contact with the Dirac operator" — in his words, it is not known in the noncommutative case how to distinguish true causality (from a metric) from general order relations. Franco's (F6) is precisely the piece that ties the cone to the metric; Besnard deliberately works without it.
2. **Functional calculus stability (B2) instead of an operator inequality (F6).** The original [2009] version had a lattice axiom (sup/inf of commuting elements) motivated by the Kakutani–Stone theorem; it was later shown equivalent to (B2) (ref [15] in the review).
3. **Duality theorem (toposets).** A *toposet* is a partially ordered topological space where x ≼ y ⇔ (∀ isotone f, f(x) ≤ f(y)) — the topology/order compatibility condition. Theorem 1: for M a compact toposet, (I(M), C(M)) is a commutative I*-algebra, and conversely every commutative I*-algebra is canonically of this form, with M = P(A). A spacetime is a toposet iff it is causally simple (no closed causal curves; pasts/futures closed) — the second-strongest causality condition after global hyperbolicity.
4. **Causal vs chronological.** Throughout Besnard's program (and Franco's) the cone defines the **reflexive causal order** ≼. The **chronological** (strict, ≪) relation is not separately axiomatized in either framework. Besnard flags the subtlety that the cone-induced order "could well be stronger than the causal order" (review §2) — i.e., saturation is doing real work; there is no cone construction for ≪ itself. The Lorentzian distance formula (next section) is the one object that touches proper-time/chronological content.
5. **Compactness tension.** "Compact causal spacetimes do not exist" (his emphasis in the review §2: causal ⇒ every compact spacetime has a boundary; in the locally compact case one must fix a compactification since C₀(M) contains no non-trivial isotone functions). This forces the use of a preferred compactification — a structural fragility: causal functions naturally live on non-compact globally hyperbolic spacetimes, while the C*-machinery wants unital/compact algebras. (Franco's framework handles this via the unitisation Ã rather than A.)
6. **Classification results for finite-dimensional algebras** (§5 of the review; crucial for our finite case):
   - M₂(ℂ): any closed convex cone in Re(M₂(ℂ)) containing constants with non-empty interior is an isocone; the induced order on P(M₂(ℂ)) ≅ S² is described via geodesic distance (equation (5) of the review).
   - **Theorem 4 (from [15]): Mₙ(ℂ) is egalitarian for all n except n = 2** — i.e., it admits only the trivial isocone (the whole Re(A)), inducing the equality order on pure states.
   - Lexicographic-sum construction (Theorems 2–3): an isocone over a poset P with fibre isocones (Ix, Ax), plus pushforward by surjective *-morphisms (π(I) is an isocone).
   - Example: I(M) + Re(K) (causal isotonies perturbed by self-adjoint compact operators) is an isocone of C(M) + K, inducing the order on M extended trivially to the vector states.

### 2c. Besnard's Proposition (commutative validation)

(Besnard [2009]; Proposition 11 of arXiv:1409.1480): if M is globally hyperbolic, the cone of smooth bounded causal functions determines the causal structure: p ≼ q iff f(p) ≤ f(q) for all causal functions f. But — and this is quoted from the review of the Franco–Eckstein paper — "if one takes an arbitrary convex cone (with a few additional axioms), then it is possible to recover every possible partial order structure on the manifold [Besnard 2009]". This is the motivation for Franco's operatorial constraint (F6): to restrict partial orders to those coming from a Lorentzian metric.

---

## 3. The Franco–Eckstein Lorentzian distance formula — exact statement

Sources: Franco–Eckstein, "Noncommutative geometry, Lorentzian structures and causality", arXiv:1409.1480 (Sept 2014), Definition 15 / Proposition 16; historical review in Franco, "The Lorentzian distance formula in noncommutative geometry", arXiv:1710.10959 / J. Phys. Conf. Ser. 968 (2018) 012005.

**Definition.** Let (A, Ã, H, D, J) be an **even commutative** Lorentzian spectral triple with ℤ₂-grading γ, constructed from a **complete globally hyperbolic spacetime M of even dimension**. For p, q ∈ M:

d̃(p, q) = inf { max{0, f(q) − f(p)} : f ∈ C^∞(M, ℝ), ⟨φ, J([D, f] + iγ)φ⟩ ≤ 0 ∀ φ ∈ H }.

The formula "with points traded for states" is proposed as the noncommutative-generalizable candidate.

**What it requires** (beyond the causal cone):

- Even-dimensional manifold, ℤ₂-grading γ, and the "steep" algebraic constraint ⟨φ, J([D,f] + iγ)φ⟩ ≤ 0 (algebraization of the gradient-steepness condition).
- Proposition 16: d̃ meets all properties of a Lorentzian distance (asymmetric, reverse triangle inequality, continuity/positivity on the causal relation, etc.) — proved for the commutative case.
- Provenance/limits (from arXiv:1710.10959 historical timeline): Moretti (2002–03) used a d'Alembert operator and nets of Hilbert spaces; Franco (2010) used globally "steep" functions, with the equality case proved using non-Lipschitz continuous causal functions; Franco–Eckstein (2012–13) algebraized steepness for **C¹** functions — but that algebraization is **not valid for the non-Lipschitz functions** the general proof needs, so the proof is limited to spacetimes where the distance can be approximated by C¹ steep functions (a direct proof is given for Minkowski); Rennie–Whale (2014–16) extended to non-globally-hyperbolic spacetimes with finite continuous distance; Minguzzi (2017) smoothed the argument.

Bottom line on the distance formula: it is stated in operator-algebraic form, but its justification as a distance is proved only in the commutative even-dimensional globally hyperbolic case, and the key analytic step (steep C¹ approximation of the true distance) is manifold-analysis, not algebra.

---

## 4. Finite / twisted causal results — what exists, what's absent

### 4a. Almost-commutative result (the only finite-factor result)

Franco–Eckstein, "Exploring the Causal Structures of Almost Commutative Geometries", SIGMA 10 (2014), 010, arXiv:1310.8225. They study S(ℝ^{1,1}) ⊗ M₂(ℂ) — a product of a 2D Minkowski algebra with a **finite factor**. Results (from the abstract):

- The causal structure on the space of states is fully described.
- The causality condition **imposes restrictions on the motion in the internal space**; "the requirement of causality favours a unitary evolution in the internal space."

Caveats for Span 5: (i) the algebra still contains the manifold factor — the causal cone is defined on the **whole** almost-commutative algebra, not on the finite factor alone; (ii) the finite factor here is M₂(ℂ), not the SM algebra; (iii) no general theorem for finite triples. This is the closest the literature comes to "causality meets a finite algebra" — and it still needs the manifold.

### 4b. Besnard's finite-dimensional classification (directly applicable, negative-leaning)

Theorem 4 of arXiv:1508.01917: Mₙ(ℂ) is egalitarian for n ≠ 2. Applied to our finite algebra A_F = ℂ ⊕ ℍ ⊕ M₃(ℂ):

- The M₃(ℂ) summand admits only the trivial isocone ⇒ equality order on its pure states.
- The ℂ summand is commutative with one-point pure-state space ⇒ no causal content possible.
- (The ℍ summand: Besnard's framework is complex-C*; the egalitarian theorem is stated for Mₙ(ℂ). The quaternionic case is not addressed in the sources found — record as unexamined, not as proven.)
- M₂(ℂ) is the **only** matrix algebra admitting non-trivial isocones — and the SM finite algebra contains no M₂(ℂ) summand.

Verdict: in Besnard's framework, A_F is causally degenerate (trivial isocone ⇒ no non-trivial order). Note the frameworks differ — a Franco-style causal cone needs (F6) with J and D, which the isocone program never uses — so this is not a proof that no Franco cone exists on A_F; it is a proof that no Besnard isocone gives a non-trivial causal order on the M₃(ℂ) part.

### 4c. Twisted triples — causal results

**Absent.** Searched specifically; no paper defines a causal cone for twisted spectral triples. What exists:

- Devastato–Farnsworth–Lizzi–Martinetti, "Lorentz signature and twisted spectral triples", arXiv:1710.04965 [hep-th] (2017/2018): twisting the SM triple yields the Krein space (fundamental symmetry J) associated with Lorentzian signature; a twist–Wick-rotation link. This supplies the **ingredients** for (F6) (a J), not a causal cone.
- "Emergence of Time from a Twisted Spectral Triple in Almost-Commutative Geometry", arXiv:2512.15450 (recent): states explicitly that its result "remains a local result in the compact setting, rather than a full Lorentzian space-time with global causal structure." — i.e., twisted machinery has not yet produced global causal structure.

So: the twist gives us the Krein structure (J) needed to even *state* (F6); it gives us nothing yet toward a causal cone or order.

### 4d. Summary of absences (honest)

- No published construction of a Franco-style causal cone for any purely finite spectral triple (no manifold factor).
- No published causal-cone results for twisted spectral triples.
- No finite-algebra analogue of the recovery theorem (F8): every recovery/validation result is commutative-manifold-level.
- No separate algebraic treatment of the chronological (strict) relation in either framework.

---

## 5. The (a)/(b) classification ledger

Legend: **(a)** statable over a finite *-algebra with no points; **(b)** needs points/manifold.

| Axiom | Class | Reason |
|---|---|---|
| Franco (F1) Hermitian | **(a)** | a* = a is pure *-algebra. |
| Franco (F2) sum-stable | **(a)** | Purely algebraic. |
| Franco (F3) positive homogeneity | **(a)** | Purely algebraic. |
| Franco (F4) constants in C | **(a)** | Finite algebras are unital; x·1 is algebraic. Note: (F4) + (F6) forces the trivial order to be reflexive — algebraic. |
| Franco (F5) span_ℂ(C)̅ = Ã | **(a)** (form) | Stated over the algebra; in finite dimension the C*-closure is automatic (all subspaces closed). The *content* question — does a non-trivial cone satisfying (F1)–(F6) with full span exist? — is open and unexamined in the literature for finite A. |
| Franco (F6) ⟨φ, J[D,a]φ⟩ ≤ 0 | **(a)** (form) | With J (fundamental symmetry) and D in hand, this is a concrete linear-matrix-inequality constraint on A_sa — checkable on ℂ⁶⁴ with our R_swap Krein structure and D_F. It uses H, D, J, but no points. |
| Franco (F7) order ω ≼ η on S(Ã) | **(a)** (form) | States of a finite C*-algebra are well-defined; the cone induces an order on them algebraically. Pure states of A_F are explicit (projective lines over each summand). |
| Franco (F8) recovery on M | **(b)** | Requires: commutative triple, complete globally hyperbolic M, the physical-pure-states subset M(Ã), and M(Ã) ≅ M. Every step needs the manifold. |
| Franco's setting: Lorentzian spectral triple (A, Ã, H, D, J) | **(a)/(b)** split | The data (algebras, representation, D, J) are algebraic; the *definition* of "Lorentzian" (minimal axioms) is algebraic. But non-compactness (hence the unitisation Ã rather than A) and global hyperbolicity are (b). For our finite unital A_F, Ã = A and the construction collapses trivially — the framework's non-compact machinery has nothing to act on. |
| Besnard (B1) I ⊂ Re(A) | **(a)** | Pure *-algebra. |
| Besnard (B2) non-decreasing functional calculus | **(a)** | Finite algebras have continuous functional calculus; stability under it is algebraic. |
| Besnard (B3) sum-stable | **(a)** | Purely algebraic. |
| Besnard (B4) norm-closed | **(a)** | Automatic in finite dimension. |
| Besnard (B5) separates states | **(a)** (form) / **(b)** (spirit) | Statable: states of finite A are algebraic objects. But the physical meaning — events identified by time observables — and the proof that separation holds need strong causality / points. |
| Besnard (H0)–(H3) hypotheses | **(a)** (form) / **(b)** (motivation) | Statable over O; justified only by classical spacetime (clocks, GPS coordinates, strong causality). |
| Besnard Theorem 1 (toposet duality) | **(b)** | Needs a compact toposet M; the direction (I,A) → (I(M), C(M)) reconstructs points. |
| Besnard Theorem 4 (Mₙ egalitarian, n≠2) | **(a)** | Pure C*-algebra result — directly applicable to M₃(ℂ) ⊂ A_F. |
| Besnard lexicographic sum / pushforward (Thm 2, 3; Prop 2) | **(a)** | Constructions on I*-algebras; algebraic. |
| Distance formula: algebraic form d̃ as inf over f with J([D,f]+iγ) ≤ 0 | **(a)** (form) | The expression is operator-algebraic; needs grading γ (we have one) and J, D. |
| Distance formula: requirements + proof | **(b)** | Even-dimensional complete globally hyperbolic commutative M; C¹-steep approximation argument is manifold analysis; the equality case needs non-Lipschitz causal functions. |
| "Causal functions separate points" | **(b)** | Needs points, strong causality (Besnard §2), and fails globally without causality conditions; compactness tension (no compact causal spacetimes). |

---

## 6. Bottom line

Every single cone axiom — Franco's (F1)–(F6) and Besnard's (B1)–(B5) — is **formally statable over a finite *-algebra**: they are constraints on self-adjoint elements (convexity, constants, spanning/closure, separation of states) plus, in Franco's case, one operator inequality ⟨φ, J[D,a]φ⟩ ≤ 0 that we can write down on ℂ⁶⁴ with the DLM twist's Krein structure. In principle, a finite algebra could satisfy the full axiom list, and the cone would then induce a genuine order on the finite algebra's state space — no points needed for the *statement*.

But the literature gives a finite algebra **nothing to stand on** at the next step. All validation lives at the manifold: the recovery theorem (F8) is commutative and needs global hyperbolicity; the distance formula's proof needs even-dimensional globally hyperbolic M and steep-function analysis; Besnard's duality theorem needs a compact toposet. Worse, the one classification result that touches finite algebras cuts against us: in Besnard's framework M₃(ℂ) is egalitarian — only the trivial isocone, hence only the equality order — and the SM finite algebra's commutative summand is a point. The single finite-factor result in the literature (Franco–Eckstein arXiv:1310.8225) still keeps the manifold factor; its lesson is that causality *constrains motion in the internal space* and *favours unitary internal evolution*, not that the finite factor has its own causal cone. And for twisted triples there is no causal-cone literature at all — the twist literature (arXiv:1710.04965) supplies the Krein J that lets (F6) be stated, while the newest twisted-time work (arXiv:2512.15450) explicitly stops at "a local result in the compact setting."

So for Bridge Span 5: the honest position is that the **axioms are portable to A_F but the semantics are not**. Computing the order that a maximal (F1)–(F6)-satisfying cone induces on S(A_F) is well-posed finite linear algebra — but whether such a cone is non-trivial, whether its span is all of A_F, and whether the induced order means anything physical, are questions the literature has never asked, let alone answered. The manifold-level content — global hyperbolicity, the causal/chronological distinction in curves, points separated by causal functions, Lorentzian distance as supremum of proper time — does not survive the passage to a finite algebra, and the compactness tension (causal functions want non-compact globally hyperbolic spacetimes; C*-machinery wants unitality/compactness) is exactly where the finite case breaks the classical picture. Span 5 should therefore treat any finite causal order as a formal, T5-level construction, with the manifold demands of (F8)/toposet-duality/distance-formula clearly marked as the un-crossed gap.

---

## References

- N. Franco, "An algebraic formulation of causality for noncommutative geometry", arXiv:1212.5171 [math-ph] (2012–2013). — causal cone axioms (F1)–(F6), order (F7), recovery theorem.
- N. Franco, M. Eckstein, "Exploring the Causal Structures of Almost Commutative Geometries", SIGMA 10 (2014), 010, arXiv:1310.8225. — S(ℝ^{1,1}) ⊗ M₂(ℂ); causality restricts/favours unitary internal motion.
- N. Franco, M. Eckstein, "Noncommutative geometry, Lorentzian structures and causality", arXiv:1409.1480 (2014). — Lorentzian spectral triples, causal cone restated (Def 13 / Thm 14), distance formula (Def 15 / Prop 16).
- N. Franco, "The Lorentzian distance formula in noncommutative geometry", arXiv:1710.10959; J. Phys. Conf. Ser. 968 (2018) 012005. — history: Moretti 2003; Franco 2010; Franco–Eckstein 2012–13; Rennie–Whale 2014–16; Minguzzi 2017.
- F. Besnard, "Two roads to noncommutative causality", arXiv:1508.01917 (review; updated 2021). — hypotheses (H0)–(H3), isocone axioms (B1)–(B5), toposet duality, Mₙ egalitarian theorem, lexicographic sums; isocone program originated in Besnard [2009] (cited therein).
- A. Devastato, S. Farnsworth, F. Lizzi, P. Martinetti, "Lorentz signature and twisted spectral triples", arXiv:1710.04965 [hep-th] (2017–2018). — twist yields Krein space / fundamental symmetry J; no causal cone.
- "Emergence of Time from a Twisted Spectral Triple in Almost-Commutative Geometry", arXiv:2512.15450 (recent; accessed 2026-10). — twisted-time result explicitly "local… in the compact setting, rather than a full Lorentzian space-time with global causal structure."

*Tier note: this document is a literature survey (T5). It asserts nothing about the thet-logos finite triple beyond what the cited papers establish. No claim is made that A_F satisfies any of these axioms, and no Lorentzian-physics conclusions are drawn.*
