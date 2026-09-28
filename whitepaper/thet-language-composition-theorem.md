# The Composition Theorem

**Language:** Thet: A Language of Harmonic Action (v2)
**Status:** Structural theorem, precisely stated. Proofs are short; the content
is that first-order-ness is compositional.
**Answers:** the composition-theorem step of the Three-Generation Map roadmap.

---

## 1. Definitions

Let (A, H, D) be a finite real spectral triple with representation π and
opposite representation π°(b) = J π(b)* J⁻¹, and let R be a repeat operator
(self-adjoint on H) in the sense of thet-language §3.

**Definition 1 (first-order thet event).** A thet event e with repeat operator
R_e is *first-order* if its order-one defect vanishes:

$$ \delta(e) := \max_{a,b \in \mathcal{G}} \|[[R_e, \pi(a)], \pi^\circ(b)]\| = 0 $$

where G is a finite real generating set of A (normalized). This is the
order-one commutator condition, restated as a property of the event's repeat
operator.

**Definition 2 (composite repeat operators).**
- *Sequential:* for events e₁, e₂ with repeat operators R₁, R₂ self-adjoint
  on a common dense domain, the repeat operator of e₂ ∘ e₁ is the Trotter sum
  $$ R_{e_2 \circ e_1} := R_1 + R_2 $$
  (essentially self-adjoint under standard domain conditions). Justification:
  repeating the sequence (e₂ after e₁) n times is
  (e^{iR₂t}e^{iR₁t})ⁿ → e^{i(R₁+R₂)nt} by the Trotter product formula — the
  generator of the repeated sequence is the sum.
- *Parallel:* for events on triples (A₁,H₁,R₁), (A₂,H₂,R₂), the repeat
  operator of e₁ ⊗ e₂ is the product Dirac
  $$ R_{e_1 \otimes e_2} := R_1 \otimes 1 + \gamma_1 \otimes R_2 $$
  on H₁ ⊗ H₂, where γ₁ is the grading of the first triple.

## 2. Theorem 1 — Linearity

**Statement.** Let R₁, …, Rₙ be first-order repeat operators on the same
(H, π, π°). Then every real linear combination R = Σ cₖRₖ is first-order.

**Proof.** The double commutator is linear in R:
[[ΣcₖRₖ, π(a)], π°(b)] = Σcₖ [[Rₖ, π(a)], π°(b)] = 0. ∎

**Corollary (the 84-space).** Every Dirac operator in the 84-dimensional
physically selected subspace (4×18 Yukawa + 12 Majorana directions) is
first-order. The selection procedure — charge conservation plus one-Higgs
minimality — cannot break order-one, because it selects within a vector space
of first-order operators.

## 3. Theorem 2 — Sequential composition preserves first-order-ness

**Statement.** If e₁, e₂ are first-order thet events with repeat operators
R₁, R₂ (self-adjoint, common dense domain, R₁+R₂ essentially self-adjoint),
then e₂ ∘ e₁ is first-order.

**Proof.** By Definition 2, R_{e₂∘e₁} = R₁ + R₂, which is first-order by
Theorem 1. ∎

*Reading:* repeating a sequence of first-order actions can never produce a
second-order defect. Sequential composition is safe.

## 4. Theorem 3 — Parallel composition preserves first-order-ness

**Statement.** If (A₁,H₁,R₁) and (A₂,H₂,R₂) are first-order (even) triples,
their product triple with R = R₁⊗1 + γ₁⊗R₂ is first-order for the product
algebra A₁⊗A₂.

**Proof.** Standard product-of-spectral-triples result: the order-one
condition holds for the product because the double commutator factorizes
across the tensor factors, and each factor's defect vanishes. Restated in
thet language: parallel-composed thet events inherit first-order-ness from
their components. ∎

## 5. Theorem 4 — Interchange coherence

**Statement.** First-order-ness of a composite thet expression is independent
of bracketing: the interchange law
(e₂∘e₁)⊗(f₂∘f₁) = (e₂⊗f₂)∘(e₁⊗f₁) preserves the first-order property on both
sides.

**Proof.** Both sides reduce, via Definitions 2 and Theorems 2–3, to sums and
tensor sums of the same first-order repeat operators; Theorem 1 gives
vanishing defect either way. ∎

*Reading:* it does not matter in which order you assemble a complex thet
expression — sequentially then in parallel, or the reverse. The first-order
property is a property of the *multiset of events*, not of the assembly
history.

## 6. What this buys

The thet language promises "greatest freedom" — any finite composition of
events is well-formed. The composition theorem is what makes that promise
*safe*: **free composition cannot violate the order-one condition.**
First-order-ness is not a fragile property of special operators; it is a
compositional invariant of the language. Concretely:

1. The 84 selected directions can be freely combined — any point in the
   selected space is a valid first-order Dirac operator (Corollary).
2. Building larger structures (products, sequences of thet processes) never
   reintroduces the order-one problem once the components are first-order.
3. The "greatest freedom" axiom and the "harmonic structure" axiom are
   compatible: freedom of composition does not destroy the harmonic
   (first-order) structure.

## 7. Honesty

- The proofs are short because the content is structural: linearity of the
  commutator plus the known product-triple result. No new computation was
  needed — this is the precise *statement* the roadmap asked for.
- The Trotter-sum definition of sequential repeat operators assumes
  essential self-adjointness of R₁+R₂; pathological domains are excluded by
  fiat. In the finite-dimensional model (our working case) this is automatic.
- The theorems say first-order-ness is *preserved*; they say nothing about
  which events are first-order in the first place. That classification is the
  T4 numerical work (46 / 402 directions), not this theorem.
- Status: T5 structural (language-level), consistent with the T3 machine-proven
  order-one results and the T4 numerical census.
