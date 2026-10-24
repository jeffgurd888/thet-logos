# Stage 1c-0 Q13 re-price — the general closed intertwiner form of κ_p

**Date:** 2026-10-24  
**Item:** Gap queue Q13, replacing **UNPRICED** with a priced brick decomposition  
**Sources:** `whitepaper/gap-theorem-queue-2026-10-24.md` Q13;
`whitepaper/pitch-4-stage-1c-0-2026-10-18.md`;
`lean/ThetLogos/LatticeAnalyticity.lean` (landed shapes only)

**NO CLAIM.** This is a scoping and pricing charter. It proves nothing, changes
no Stage 1c-0 verdict, and closes **0** parts of any official Clay statement.
Stage 1c-0 clause (ii) remains **PARTIAL** until the work below is built and
parent-verified.

## Price decision

**Q13 total: L (upper end).**

| Brick | Deliverable | Price |
|---|---|---:|
| Q13-0 | Target/interface freeze: J notation, orientation and transpose conventions, Haar normalization, test statements | **S** |
| Q13-1 | Pair-representation and Haar-twirl apparatus for ρ⊗ρ, ρ⊗ρ̄ and the dual/conjugate orientations | **M** |
| Q13-2 | Linkwise first- and second-moment calculus at β = 0, including centering/covariance | **M** |
| Q13-3 | Two-plaquette tensor-network contraction: incidence, orientation and index wiring for every sharing q | **M–L** |
| Q13-4 | Assembly into κ_p and mandatory specialization/agreement discharge | **S–M** |

The total is not obtained by mechanically adding the letters: Q13-1 and Q13-2
share the same Haar-invariance core, and Q13-4 should be assembly once Q13-3 is
correct. The price is nevertheless **L**, not M, because Q13-3 is bespoke:
it must turn the corpus's link-sharing geometry into a finite tensor
contraction without losing a transpose, a conjugate, an orientation or a
centering term. Q13-3 is the largest single brick.

There is **no unpriceable residue in Q13 as sourced** — arbitrary (G, ρ), with
the other Stage 1c-0 hypotheses inherited — provided “closed intertwiner
form” means the precise J-twirl formula in §1. Stronger readings are excluded
in §5 and are not silently included in the L price.

---

## 1. The target statement

### 1.1 The landed left-hand side

Fix the Stage 1c-0 data: a finite site type Λ, commuting shifts
σ : Fin 4 → Equiv.Perm Λ, a normalized bi-invariant probability measure μG on
G, a continuous unitary representation

\[
\rho : G \longrightarrow U(V),\qquad V=\mathbb C^d,\quad d>0,
\]

and a plaquette \(p=(x,\mu,\nu)\), \(\mu<\nu\). Let

\[
W_p(U)=\chi_\rho(P_p(U))
\]

be the landed `wilsonLoop` for `plaquetteSteps μ ν`, let

\[
D_q(U)=1-\frac{\operatorname{Re}\chi_\rho(P_q(U))}{d}
\]

be `plaquetteDensity`, and let \(A=\sum_qD_q\) be `actionDensity`. The object
to be rewritten is exactly the landed covariance

\[
\kappa_p
  := \operatorname{Cov}_0(W_p,A)
\]

— in Lean shape, `covZero σ μG ρ (fun U => wilsonLoop σ ρ U x
(plaquetteSteps μ ν)) (fun U => (actionDensity σ ρ U : ℂ))`.

The general theorem already landed is

\[
\kappa_p
 =\sum_{q\in\operatorname{sharingPlaquettes}\sigma
      (\operatorname{plaquetteLinks}\sigma p)}
   \operatorname{Cov}_0(W_p,D_q),
\tag{1}
\]

via `covZero_plaquetteLoop_eq_sum`. Q13 does **not** reprove (1). It must
evaluate every summand in (1) in closed pair-intertwiner form and hence give a
second, representation-theoretic formula for the same \(\kappa_p\).

### 1.2 The J / pair-intertwiner data

For finite-dimensional unitary representations \(\pi,\tau\) of \(G\), define
the Haar twirl, or **J operator**,

\[
\boxed{\;
\mathcal J(\pi,\tau)
  :=\int_G \pi(g)\otimes\tau(g)\,d\mu_G(g)
  \in \operatorname{End}(V_\pi\otimes V_\tau).
\;}
\tag{2}
\]

Its entry form is

\[
\mathcal J(\pi,\tau)_{(a,b),(c,d)}
  =\int_G \pi(g)_{ab}\,\tau(g)_{cd}\,d\mu_G(g).
\tag{3}
\]

The one-factor boundary case is

\[
\mathcal J(\pi):=\int_G\pi(g)\,d\mu_G(g)=\mathcal J(\pi,\mathbf 1).
\tag{4}
\]

The representations that must be available are not only \(\rho\otimes\rho\)
and \(\rho\otimes\bar\rho\). Plaquette words contain direct and inverse
links, and the density contains both \(W_q\) and \(\overline{W_q}\). The
apparatus must therefore cover

\[
\rho,\qquad \bar\rho,\qquad \rho^\vee,\qquad \bar\rho^\vee,
\]

where \(\bar\rho\) is the entrywise-conjugate representation and
\(\rho^\vee(g)=\rho(g^{-1})^{T}\) is the dual representation. A literal
inverse matrix factor \(\rho(g)^{-1}\) is not itself \(\rho^\vee(g)\); it is
\(\rho^\vee(g)\) followed by the fixed transpose wiring of its two indices.
Q13-1 must prove that dictionary once, rather than letting every later proof
rediscover it.

“Closed” has a specific meaning here. It is not enough to rename a Haar
integral \(\mathcal J\). Q13-1 must prove the canonical reduction

\[
\boxed{\;
\mathcal J(\pi,\tau)
  =P_{(V_\pi\otimes V_\tau)^G},
\;}
\tag{5}
\]

the orthogonal projector onto the invariant subspace of \(\pi\otimes\tau\)
(for normalized Haar measure and unitary \(\pi,\tau\)). Thus
\(\mathcal J(\rho,\bar\rho)\) is the pair intertwiner on
\(V\otimes V^*\simeq\operatorname{End}(V)\), and
\(\mathcal J(\rho,\rho)\) is the invariant-bilinear pair intertwiner on
\(V\otimes V\). Formula (5), not the notation alone, is what makes the final
expression a closed intertwiner form.

### 1.3 The contraction formula

Write \(W_q^{+}=W_q\) and \(W_q^{-}=\overline{W_q}\). Since

\[
D_q=1-\frac{W_q^{+}+W_q^{-}}{2d},
\]

the required per-plaquette identity is

\[
\operatorname{Cov}_0(W_p,D_q)
  =-\frac{1}{2d}
   \left(
     \mathfrak C^{+}_{p,q}+\mathfrak C^{-}_{p,q}
   \right),
\tag{6}
\]

where, for \(s\in\{+,-\}\),

\[
\mathfrak C^{s}_{p,q}
 :=
 \mathbb E_0[W_pW_q^{s}]
   -\mathbb E_0[W_p]\,\mathbb E_0[W_q^{s}]
\tag{7}
\]

and **each expectation in (7) is required to be the explicit finite tensor
contraction of the J data from (2)–(4)** described next.

Expand both plaquette traces into matrix indices. Group the scalar matrix
factors by the configuration link \(\ell\) that they read. Independence of
the link variables at β = 0 replaces the integral over \(U_\ell\) by:

- \(\mathcal J(\pi)\) if only one of \(p\) or the signed \(q\)-word uses
  \(\ell\);
- the entry tensor of \(\mathcal J(\pi,\tau)\) if both words use \(\ell\),

with \(\pi,\tau\) selected from \(\rho,\bar\rho,\rho^\vee,
\bar\rho^\vee\) according to whether the factor is direct, inverse or
conjugated, and with the transpose wiring from §1.2 inserted for literal
inverse factors. Contract all resulting indices along the two plaquette
words. Denote that finite contraction by

\[
\mathbb E_0[W_pW_q^{s}]
  =\operatorname{Contr}^{s}_{p,q}(\mathcal J).
\tag{8}
\]

The means in (7) use the same contraction with the other word omitted.
Substituting (6)–(8) into (1), the Q13 headline is therefore

\[
\boxed{
\begin{aligned}
\kappa_p
=&-\frac{1}{2d}
 \sum_{q\in\operatorname{sharingPlaquettes}\sigma
      (\operatorname{plaquetteLinks}\sigma p)}
 \Big[
   \big(\operatorname{Contr}^{+}_{p,q}(\mathcal J)
       -\operatorname{Contr}^{+}_{p,\varnothing}(\mathcal J)
        \operatorname{Contr}^{+}_{\varnothing,q}(\mathcal J)\big)
 \\[-1mm]
 &\hspace{34mm}+
   \big(\operatorname{Contr}^{-}_{p,q}(\mathcal J)
       -\operatorname{Contr}^{-}_{p,\varnothing}(\mathcal J)
        \operatorname{Contr}^{-}_{\varnothing,q}(\mathcal J)\big)
 \Big].
\end{aligned}}
\tag{9}
\]

The empty-word contractions in (9) are notation for the two one-loop means;
they are part of the target because dropping the covariance centering changes
the answer for a general, possibly reducible, ρ with a trivial subrepresentation.

Equations (5), (6), (8) and (9), specialized back to the landed definitions,
are the target. A formula that merely abbreviates each covariance integral as
an unexplained “contraction” does **not** satisfy Q13.

---

## 2. Apparatus inventory

### 2.1 Already landed and reusable

Within the three bounded sources, the following are present and should not be
priced again:

- **The analytic object.** `covZero`, Gibbs moments, `actionDensity`, the
  β = 0 derivative identity, and the explicit first-order expansion in
  `LatticeAnalyticity`.
- **The link-sharing reduction.** `plaquetteLinks`, `sharingPlaquettes`,
  `covZero_eq_sum_sharing`, `covZero_plaquetteLoop_eq_sum`, and
  `deriv_plaquetteLoop_eq`. In particular, the finite sum in (1) is already
  T1 for general (G, ρ).
- **β = 0 factorization.** The Stage 1a product-measure factorization used by
  the reduction: expectations of observables on disjoint link sets factor at
  β = 0, and disjoint covariance contributions cancel.
- **Local observable hygiene.** Plaquette densities depend only on their
  links; measurability, boundedness and integrability of plaquette densities
  and their products are already available in the landed module.
- **The one-dimensional model.** Circle character orthogonality, per-link
  character factorization, vanishing of the mixed moments,
  `covZero_circle_plaquette_density`, `sum_sharing_circle`, and
  `kappa_circle_plaquette`. These are the mandatory specialization test, not
  a substitute for the general apparatus.

No J tensor, tensor-product representation, dual/conjugate pair moment, or
general Haar–Schur orthogonality theorem is named in the landed
`LatticeAnalyticity` shapes or in the Stage 1c-0 dossier. This memo therefore
does not credit an unexamined object elsewhere in the corpus with reducing
the price.

### 2.2 What must be built

1. **Representation adapters.** A disciplined passage from the corpus's
   `ρ : G →* ↥(Matrix.unitaryGroup (Fin d) ℂ)` and `repMatrix` coordinates to
   tensor, conjugate and dual representations, including the entry/Kronecker
   dictionary and the transpose rule for inverse links.
2. **The J-twirl theorem.** Definition of \(\mathcal J(\pi,\tau)\),
   invariance, idempotence/self-adjointness, identification with the
   invariant-subspace projector, and the resulting pair orthogonality in
   entry form. The reducible case must be included; assuming irreducibility
   would change Q13's target.
3. **Linkwise moment calculus.** First and second Haar moments of matrix
   entries as functions on configuration space; factorization across distinct
   links; correct treatment of a link used by neither, one, or both words;
   and the covariance centering terms.
4. **Plaquette tensor networks.** Expansion of `wilsonLoop` and
   `plaquetteDensity` into oriented link factors and indices; a finite
   incidence/orientation classification for two plaquettes; and a contraction
   operation whose value is independent of harmless index relabeling and
   cyclic rotation of a trace word.
5. **Assembly and checks.** Substitution into the landed link-sharing sum,
   the conjugate/direct split of \(D_q\), and the specialization tests in §4.

### 2.3 What Mathlib can and cannot be credited with

Mathlib supplies substrate, not the finished Q13 apparatus:

- finite-dimensional matrix and tensor-product algebra, including the
  algebraic language in which a Kronecker/J operator can be represented;
- general representation/intertwiner language and finite-dimensional dual
  constructions at the API level;
- Haar measure, invariance, product measures and Fubini-style integration
  infrastructure.

No turnkey theorem is credited here in the exact corpus coordinates —
“the Haar twirl of `repMatrix ρ ⊗ repMatrix ρ̄` is the stated projector and
evaluates this two-plaquette contraction.” Basis/order isomorphisms,
unitary-group coercions, conjugate/dual compatibility and the lattice tensor
network are adapter and proof work for Q13. This is why the standard-looking
twirl theorem is M rather than S, while the bespoke contraction remains the
dominant cost.

---

## 3. Brick-by-brick scope, kills and PARTIALs

### Q13-0 — Target/interface freeze — **S**

**Build:** name the J operators and entry tensors; fix Kronecker index order;
fix the four orientation representations and the inverse-transpose rule; fix
normalized-Haar conventions; state (5), (8) and (9) as the acceptance target;
state the two mandatory checks in §4 before any proof work.

**Kill:** if the target cannot be stated without either (a) changing ρ's
hypotheses — for example adding irreducibility, finiteness of G, or a chosen
decomposition — or (b) defining \(\operatorname{Contr}\) as an abbreviation
for the original covariance integrals. Either means the charter has mistaken
notation for the closed form.

**PARTIAL:** an entry-tensor-only interface with no operator/projector form
may proceed only if Q13-1 is still chartered to supply (5); otherwise Q13 is
not being built as priced.

### Q13-1 — Pair representations and Haar twirls — **M**

**Build:** tensor/conjugate/dual adapters; \(\mathcal J(\pi,\tau)\);
invariance and projector identity (5); entry orthogonality/pair-intertwiner
consequences for all orientation pairs needed by direct and inverse
plaquette factors.

**Kill:** if the adapter cannot be made for the corpus's arbitrary unitary
ρ without changing the landed representation type or adding a hypothesis not
present in Stage 1c-0.

**PARTIAL:** if only \(\rho\otimes\bar\rho\) lands. That evaluates the
conjugate covariance sector but not all of \(W_pW_q\), hence not
\(\operatorname{Cov}_0(W_p,D_q)\) in general. A PARTIAL here must name the
missing orientation pairs exactly.

### Q13-2 — Linkwise moment calculus — **M**

**Build:** express β = 0 expectations of finite products of plaquette matrix
entries as products of one-link J moments; prove the pair rule for a link used
by both words; prove the singleton rule; derive the centered contractions in
(7), including the trivial-subrepresentation contributions to the means.

**Kill:** if β = 0 factorization cannot be pushed from whole observables to
the matrix-entry observables under the inherited measurability/continuity
hypotheses.

**PARTIAL:** if uncentered moments land but the mean subtraction cannot be
expressed in the same J data. That is not yet a covariance formula and must
not be reported as Q13 complete.

### Q13-3 — Two-plaquette tensor-network contraction — **M–L**

**Build:** expand \(W_pW_q\) and \(W_p\overline{W_q}\); classify every
\(q\) in the landed sharing set by which links it shares with \(p\) and with
what orientations; apply Q13-2 link by link; prove (8) for every such q;
show that nonsharing q give the expected centered zero through the same
contraction language, even though (1) does not need them.

**Kill:** if a relative-incidence or orientation case makes the purported
contraction differ from the actual β = 0 moment. One explicit mismatch kills
that contraction definition; it is to be corrected or the brick stops, not
averaged over.

**PARTIAL:** any restriction must be named by geometry — for example diagonal
\(q=p\) only, one-link sharing only, or torus plaquettes only. A torus-only
landing is narrower than the general link-sharing statement if it relies on
torus distinctness rather than proving the contraction for the inherited
σ-data.

### Q13-4 — Assembly and consistency discharge — **S–M**

**Build:** prove (6), substitute into (1), obtain (9), and discharge §4.
Recover the derivative form as the negative of (9) only through the already
landed derivative theorem; do not introduce a new sign convention.

**Kill:** if the assembled formula fails either mandatory check in §4. That
is a correctness stop for the whole brick sequence: audit J normalization,
dual/transpose wiring and centering before any further work.

**PARTIAL:** if (9) is proved only under irreducibility, self-duality, or a
similar extra representation hypothesis. That would be a useful special
case, not Q13's general form.

---

## 4. Mandatory consistency checks

These are acceptance conditions, not optional examples.

### C1. Circle/fundamental specialization must recover −1/2

Specialize to

\[
G=\operatorname{Circle},\qquad \rho=\operatorname{circleRep},\qquad
\mu_G=\operatorname{haarProb}(\operatorname{Circle}),\qquad
\Lambda=\operatorname{Fin}4\to\operatorname{ZMod}N,
\quad \sigma=\operatorname{torusShift}N,
\]

with \(N\ge2\) and \(\mu<\nu\). The general formula must recover, first
termwise if the contraction is evaluated per q,

\[
\operatorname{Cov}_0(W_p,D_q)
 =\begin{cases}
 -\frac12,&q=p,\\
 0,&q\ne p,
 \end{cases}
\]

in agreement with `covZero_circle_plaquette_density`, and then in total

\[
\boxed{\kappa_p=-\frac12}
\]

in agreement with `kappa_circle_plaquette`.

The representation-theoretic reason the check is sharp is visible in the J
language: the fundamental circle representation has no invariant vector;
its \(\rho\otimes\bar\rho\) pair twirl is the scalar contraction, while the
\(\rho\otimes\rho\) charge-two contraction contributing to
\(\mathbb E_0[W_p^2]\) vanishes. Together with \(d=1\), the diagonal term is
\(-(0+1)/2=-1/2\). If the Q13 formula instead produces a dimension factor,
an extra invariant-sector term, or \(+1/2\), the J normalization or sign is
wrong.

### C2. Termwise agreement with the landed link-sharing sum

For general (G, ρ), the J formula for
\(\operatorname{Cov}_0(W_p,D_q)\) must agree with the summand in the landed
theorem `covZero_plaquetteLoop_eq_sum` for every
\(q\in\operatorname{sharingPlaquettes}\). Summing the Q13 formula must give
exactly the same \(\kappa_p\), not merely the same bound, sign, derivative or
circle value.

This check also fixes the centering: for reducible ρ, the one-factor J
contractions in the means need not vanish. A proposed “closed form” that
works only after setting \(\mathbb E_0[W_p]=0\) has silently assumed away
part of the general case.

### C3. Orientation and normalization guards

The final contraction must be unchanged by cyclic rotation of either
plaquette word and by simultaneous relabeling of contracted indices. It must
also give \(\kappa_p=0\) for the trivial one-dimensional representation,
where \(W_p=1\) and \(D_q=0\); this catches a missing covariance subtraction
or an incorrect \(2d\) denominator.

---

## 5. Pricing rationale and excluded stronger readings

The source Stage 1c-0 was itself priced **M** and landed an 87-theorem module
with the general finite sum and the complete circle evaluation. It expressly
cut the pair-intertwiner apparatus because that apparatus alone would price
**above M**. The decomposition above respects that lower bound:

- Q13-1 is a real representation-theory build, not a definition: arbitrary
  reducible unitary ρ, duals, conjugates, tensor products and Haar twirls.
- Q13-2 is a real measure/factorization build: the passage from observables
  to matrix entries is exactly where hidden integrability, repeated-link and
  centering errors occur.
- Q13-3 is the bespoke and largest piece: two oriented plaquette words, all
  relative incidences, and index wiring in the corpus's coordinates.
- Q13-0 and Q13-4 are smaller only because the earlier bricks are required to
  expose the right interfaces and because the landed finite sum/circle
  theorems provide exact targets.

Hence **L (upper end)** is the defensible total. Pricing Q13 as M would
contradict the source's own cut decision; pricing it as a wall would ignore
the fact that every mathematical ingredient has a finite, named route and
the two ends of the calculation are already landed.

Two stronger readings are **not** included and have no defensible price from
the bounded record:

1. **A canonical Schur-basis expansion for arbitrary reducible ρ.** Q13's
   sourced target is equality in terms of J twirls/invariant projectors. A
   further decomposition of those projectors into a chosen irreducible
   basis, multiplicity spaces and explicit Clebsch–Gordan data is a different
   deliverable.
2. **Higher-moment degenerate link words.** If “general” is expanded beyond
   the inherited plaquette-incidence setting to pathological σ-data in which
   one configuration link occurs more than twice across the two signed
   plaquette words, pair intertwiners alone are insufficient; higher Haar
   moment tensors would be required. Q13-3 must either prove that such cases
   do not arise for its stated scope or land the corresponding PARTIAL by
   name. This optional extension is not folded into the L price.

Subject to those exclusions, there is no named unpriceable residue: the route
is finite, the interfaces are explicit, and the acceptance checks are
already theorems.

## Recommended commissioning order

\[
\mathrm{Q13\!-\!0}\;\longrightarrow\;
\mathrm{Q13\!-\!1}\;\longrightarrow\;
\mathrm{Q13\!-\!2}\;\longrightarrow\;
\mathrm{Q13\!-\!3}\;\longrightarrow\;
\mathrm{Q13\!-\!4}.
\]

Do not commission Q13-3 before Q13-1 and Q13-2 have fixed the J and moment
interfaces; the contraction brick is the expensive one precisely because it
should not be allowed to invent local conventions as it goes.
