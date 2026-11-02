# PNP-2 — The P vs NP barrier map (T2 dossier memo)

Date: 2026-11-02. Lane 3, PAPER-GRADE deliverable — no Lean, no builds.
Registration: `whitepaper/next-rotation-scoping-2026-11-01.md`, PNP-2 entry;
pack: `routeb-general-scratch/pack-pnp-2-barrier-map.md`.
Companion audit: `routeb-general-scratch/scoping-pnp-0-2026-11-02.md` (PNP-0).

> **NO CLAIM. Parts of P vs NP closed by this memo: 0.**
> Tier: **T2** — a dossier of named, published theorems (T4 classical
> knowledge, cited) recorded at statement grade, plus statement shapes
> and house pre-pricing checks derived from them. Nothing here is a
> house theorem, a formalization, or progress on P vs NP. The map
> fences *proof techniques the house may attempt*; it does not touch
> the problem itself.

Attribution discipline: every author / title / venue / year / page
identifier below was checked against a public source on 2026-11-02
and is copied from that source (Sources, §5). Nothing is cited from
memory alone. Where sources differ in a spelling (e.g. the BGS title
appears in both singular and plural forms), the form used is the one
in the cited source and the variant is noted, not silently merged.

---

## 0. What a "barrier" is, in one paragraph

Each barrier below is a *proved theorem about a class of arguments*,
not a conjecture about P vs NP. Each one exhibits a concrete reason
a specified form of argument cannot settle the question: relativization
exhibits two oracle worlds giving opposite answers; natural proofs
show (under a cryptographic hypothesis carried inside the statement)
that a specified style of circuit lower bound would break the very
hardness it tries to prove; algebrization exhibits oracle /
algebraic-extension pairs giving opposite answers even after
arithmetization is allowed. The house use of each barrier is exactly
its contrapositive: a **self-killing test** applied to any future
house attempt *before* that attempt is priced.

---

## 1. Relativization — Baker–Gill–Solovay (1975)

### 1.1 The named statement

**Attribution (verified).** Theodore Baker, John Gill, Robert Solovay,
"Relativization of the P=?NP Question", SICOMP 1975 — as listed in
*Computational Complexity: Favorite Theorems: Relativization* [S1].
Bibliographic form in a citing source: "T. Baker, J. Gill, and
R. Solovay. Relativizations of the P =? NP Question, SIAM J. Comput.,
4 (1975), pp. 431–442" [S2, bibliography; the same citation, "SIAM J.
Comput. 4, 431–442 (1975)", is quoted in S3]. (Title singular in S1,
plural in S2 — both forms circulate; the journal, volume, year and
pages agree.)

**Statement (standard form).** There exist oracles
$A, B \subseteq \{0,1\}^*$ such that

$$P^A = NP^A \qquad\text{and}\qquad P^B \ne NP^B,$$

where $P^O$ (resp. $NP^O$) is the class of languages decided in
polynomial time by a deterministic (resp. nondeterministic) Turing
machine with oracle access to $O$ — membership queries to $O$
answered in one step. S1 states it in exactly this two-oracle form
("They created oracles A and B such that $P^A = NP^A$, $P^B \ne NP^B$");
S3 states it identically.

**Definition carried by the statement.** An argument *relativizes*
if it remains valid, with at most routine changes, when every
machine in it is given access to an arbitrary oracle — i.e. it proves
$C^O \mathrel{R} D^O$ for *all* oracles $O$ whenever it proves
$C \mathrel{R} D$. Diagonalization / simulation arguments of the
classical computability kind relativize.

**Consequence (the barrier).** No relativizing argument settles
P vs NP in either direction: a relativizing proof of $P = NP$ would
also prove $P^B = NP^B$, contradicting the $B$ oracle; a relativizing
proof of $P \ne NP$ would also prove $P^A \ne NP^A$, contradicting
the $A$ oracle. Any resolution must use a *non-relativizing*
ingredient — a step that is true of unrelativized computation and
false in at least one oracle world.

### 1.2 Statement shape — what a Lean form would have to quantify over

A non-vacuous Lean statement would have to quantify over **all
oracles** $A : \text{Language Bool}$ (i.e. `Set (List Bool)`), over a
genuine **oracle Turing-machine model** (a TM2-style machine with a
query state / oracle tape whose step relation is parameterized by
$A$), and over the **relativized classes** $P^A, NP^A$ built from
polytime oracle deciders — then assert
$\exists A\, B,\; P^A = NP^A \land P^B \ne NP^B$, with both the
equality and the inequality *proved* for the exhibited oracles.
PNP-1a's landed vocabulary (`PvsNPDefs.lean`: `PolyDecider`, `InP`,
`PClass`, `pairStr`, `InNP`, `NPClass`, `PeqNP`, `NPSubsetP`) cannot
state this non-vacuously today: its deciders are the pin's
unrelativized `FinTM2` machines with no oracle access at all, and the
pin itself has no oracle TM (PNP-0 §1.4: oracles exist in the pin only
at the partial-recursive level, not as oracle TMs). The only
"relativized classes" definable from PNP-1a alone would ignore the
oracle — $P^A := P$ by fiat — making the two-oracle statement either
false or a costume (see §4).

### 1.3 Self-killing test (pre-pricing check)

> **RELATIVIZATION CHECK.** Before any house P-vs-NP attempt is
> priced, answer in writing: *does the proposed argument go through
> unchanged if every machine in it is given an arbitrary oracle?*
> If yes — or if no specific step can be named that fails in some
> oracle world — **the attempt is dead on arrival; stop, do not
> price it.** To pass, the attempt must name its non-relativizing
> ingredient and the world that kills the relativized version:
> for a $P \ne NP$ attempt, the equality world $A$ with
> $P^A = NP^A$; for a $P = NP$ attempt, the separation world $B$
> with $P^B \ne NP^B$. "Diagonalization, but more carefully" is not
> a named ingredient.

---

## 2. Natural proofs — Razborov–Rudich (1994 / 1997)

### 2.1 The named statement

**Attribution (verified).** Alexander A. Razborov and Steven Rudich,
"Natural Proofs", *Journal of Computer and System Sciences*, Vol. 55,
No. 1, 1997, pp. 24–35; "first presented at the Twenty-sixth Annual
ACM Symposium on Theory of computing, Montreal, Quebec, Canada. 1994,
pp. 204–213" — both forms verbatim from the EATCS 2007 Gödel Prize
page for the paper [S4]. (The Aaronson–Wigderson paper [S7] cites the
work with a 1993 preprint date; this memo follows the prize page's
1994 presented / 1997 published dating.)

**Definitions (standard form, [S5], [S6]).** A property of Boolean
functions is a family $\Phi = (\Phi_n)$, $\Phi_n$ a set of Boolean
functions $\{0,1\}^n \to \{0,1\}$, equivalently a property of their
truth tables (strings of length $2^n$). $\Phi$ is **natural** if it
contains a property that is:

- **Constructive:** membership of a function in $\Phi_n$ is decidable
  in time polynomial in the truth-table length — i.e. $2^{O(n)}$,
  singly exponential in $n$ ((quasi-)polynomial in $2^n$ in the
  looser formulation) — given the truth table as input [S5].
- **Large:** $\Phi_n$ holds for at least a $2^{-O(n)}$ fraction of
  all $n$-input Boolean functions (a "sufficiently large fraction"
  [S5]; simplified textbook variants state other non-negligible
  densities — the load-bearing point is: a random function has the
  property with non-negligible probability).

$\Phi$ is **useful against a class $\mathcal C$** if every sequence
of Boolean functions having the property infinitely often defines a
language outside $\mathcal C$ [S5]. A **natural proof** (against
$\mathcal C$) is a lower-bound proof that exhibits a language outside
$\mathcal C$ via a natural property useful against $\mathcal C$.

**Main theorem — with its hypothesis inside the statement.**
In the textbook form (Arora–Barak draft, Thm 23.9 [S8]): *suppose a
P-natural property exists that is useful against P/poly; then there
are no strong pseudorandom function generators* — in particular the
standard candidate hard problems (factoring, discrete log) become
easy at the stated subexponential scale. Equivalent contrapositive
form (Princeton lecture notes, Thm 3 [S9]): *if Discrete Log and
Factoring do not have $2^{n^\varepsilon}$-time algorithms for some
$\varepsilon > 0$, then there is no P-natural property useful against
P/poly.*

Stated as the barrier is used:

> **Assume strong pseudorandom functions / generators exist** —
> concretely, the cryptographic hardness hypothesis above
> (pseudorandom functions indistinguishable from random by the
> relevant circuit class, with the exponential hardness specified
> in the paper's main theorem [S5]). **Then no natural property is
> useful against P/poly.** In particular no natural proof proves
> $NP \nsubseteq P/\text{poly}$, and since $P \subseteq P/\text{poly}$,
> no natural proof proves $P \ne NP$ by the circuit-lower-bound route.

The hypothesis is **part of the theorem, not a footnote**: the
unconditional statement is false-to-fact in this form — the barrier
is a conditional theorem. Two scope precisions, both on the record
in the sources: (i) the barrier directly governs the *circuit*
route — proving $P \ne NP$ via superpolynomial circuit lower bounds
for an NP language; an argument not routed through P/poly is not
addressed by it and must say so rather than claim exemption by
silence. (ii) One special case *is* unconditional: the paper also
proves, without assumptions, that there is no natural proof that
certain cryptographic problems (integer factoring, discrete log)
are hard [S4, citation; S5].

### 2.2 Statement shape — what a Lean form would have to quantify over

A non-vacuous Lean statement would have to quantify over
**properties of Boolean functions**: families
$\Phi_n \subseteq (\{0,1\}^n \to \{0,1\})$ presented by their truth
tables, with a **counting / density** clause over all $2^{2^n}$
functions of $n$ variables (largeness), a **decidability-in-time-
polynomial-in-$2^n$** clause (constructivity — a polytime notion
applied to truth-table strings, not to the original inputs), a
**circuit model and the class P/poly** (usefulness is defined by
exclusion of polynomial-size circuit families), function *families*
and the languages they define, and — inside the hypothesis —
**pseudorandom function generators and distinguishers** with their
hardness parameters. PNP-1a's vocabulary cannot state any of this
non-vacuously: it owns no circuits and no P/poly at all, no type of
Boolean functions as objects with truth-table encodings, no density
or counting over function spaces, no randomness, generators, or
distinguishers; its only polytime notion (`PolyDecider` over
`FinTM2`) decides languages over `List Bool` in time polynomial in
the input length — a different resource scale from constructivity's
polynomial-in-$2^n$. Renaming `InP` on truth tables "constructivity"
without the circuit class and the cryptographic hypothesis would
state a different, weaker proposition under the barrier's name —
the costume failure of §4.

### 2.3 Self-killing test (pre-pricing check)

> **NATURAL-PROOFS CHECK.** For any house attempt routed through
> circuit lower bounds (target: $NP \nsubseteq P/\text{poly}$, or any
> property of Boolean functions used to exclude small circuits):
> *is the key property constructive (decidable efficiently from the
> truth table) and large (true of a non-negligible fraction of all
> functions)?* If both — **the attempt is dead on arrival under the
> stated cryptographic hypothesis; stop, do not price it.** To pass,
> the attempt must do one of three things, named in advance:
> (a) exhibit the property and prove it **non-constructive** or
> **non-large**; (b) carry the Razborov–Rudich hypothesis's failure
> as an explicit cost — i.e. admit the attempt also breaks strong
> pseudorandom generators, and price *that* claim too; or
> (c) show the argument is **not** routed through a
> useful-against-P/poly property at all, naming what replaces it.
> An attempt that cannot say which of (a)/(b)/(c) it is, is not yet
> an attempt. (Scope fence: this check governs the circuit route;
> the barrier is conditional — anyone invoking it without its
> hypothesis, in either direction, has misstated the theorem.)

---

## 3. Algebrization — Aaronson–Wigderson (2008)

### 3.1 The named statement

**Attribution (verified).** S. Aaronson and A. Wigderson,
"Algebrization: a new barrier in complexity theory", in STOC, 2008,
pp. 731–740 [S2, bibliography]. Authors in full: Scott Aaronson,
Avi Wigderson [S7, paper title page].

**Definition (the paper's own, [S7] §1.2).** Given an oracle $A$,
write $\tilde A$ for a **low-degree extension** of $A$: $A$ viewed as
a Boolean function, extended to a low-degree polynomial over a
finite field or ring, evaluable at non-Boolean points. An inclusion
$C \subseteq D$ **algebrizes** if $C^A \subseteq D^{\tilde A}$ for
all oracles $A$ and all low-degree extensions $\tilde A$ of $A$. A
separation $C \nsubseteq D$ **algebrizes** if
$C^{\tilde A} \nsubseteq D^A$ for all $A, \tilde A$. The asymmetry
is essential and is the paper's own emphasis: in both cases only one
class receives the algebraic oracle $\tilde A$; the other receives
the Boolean $A$ [S7].

**The two facts that make it a barrier for P vs NP** ([S7] §1.2,
stated there as the §5 results; the first is also Thm 5.1 as cited
in [S2]):

1. **The known non-relativizing techniques algebrize.**
   Arithmetization-based results — e.g. $IP = PSPACE$ and
   $MIP = NEXP$ as inclusions, and separations such as
   $MA_{EXP} \nsubseteq P/\text{poly}$ — hold in algebrized form:
   for all $A, \tilde A$, $PSPACE^A \subseteq IP^{\tilde A}$,
   $NEXP^A \subseteq MIP^{\tilde A}$,
   $MA_{EXP}^{\tilde A} \nsubseteq P/\text{poly}^A$. So the technique
   that defeated relativization lives *inside* the algebrizing class
   of arguments.

2. **P vs NP does not algebrize — in either direction.** There
   exist oracles $A$ and low-degree extensions $\tilde A$ such that
   $$NP^{\tilde A} \subseteq P^A
     \qquad\text{(indeed } PSPACE^{\tilde A} \subseteq P^A\text{)}$$
   — so no algebrizing argument proves $NP \nsubseteq P$ — **and**
   there exist oracles $A, \tilde A$ such that
   $$NP^A \nsubseteq P^{\tilde A}
     \qquad\text{(indeed } NP^A \nsubseteq BPP^{\tilde A},\;
       RP^A \nsubseteq P^{\tilde A}\text{)}$$
   — so no algebrizing argument proves $NP \subseteq P$ either.
   (Easy instance of the first pair, [S7] §1.3.2: take $A$ a
   PSPACE-complete language and $\tilde A$ a PSPACE-complete —
   multilinear — extension of $A$; then $NP^{\tilde A} = P^A =
   PSPACE$. The second pair is the hard direction, proved in the
   paper via lower bounds in its algebraic query-complexity model.)

**Consequence (the barrier).** Arithmetization + relativization
*together* still do not suffice: any resolution of P vs NP — and
likewise of P vs RP, or NEXP vs P/poly [S7, abstract] — requires a
**non-algebrizing** technique, an ingredient that does not survive
replacing an oracle by its low-degree extension on one side.

### 3.2 Statement shape — what a Lean form would have to quantify over

A non-vacuous Lean statement would have to quantify over **oracle /
extension pairs** $(A, \tilde A)$: a language $A$, a finite field or
ring $\mathbb F$, and a low-degree (multivariate) polynomial over
$\mathbb F$ extending $A$'s Boolean function — plus **algebraic
oracle machines** that may query $\tilde A$ at arbitrary
$\mathbb F$-points, the relativized-and-algebrized classes
$P^A, NP^A, P^{\tilde A}, NP^{\tilde A}$, and, for the hard
direction, the paper's algebraic query-complexity lower bounds.
PNP-1a's vocabulary cannot state this non-vacuously, for three
stacked reasons: it has no oracle machine at all (§1.2's gap, which
algebrization inherits); its only polynomials are `Polynomial ℕ`
used as **time bounds** — a natural-number polynomial evaluated at
an input length, not a field polynomial extending a Boolean
function, so the corpus owns no low-degree-extension operator or
even its type; and it has no finite-field vocabulary wired to the
complexity classes. A "Lean algebrization" written today could only
assert the displayed inclusions for classes defined to make them
true — the costume failure of §4, one level deeper than
relativization's.

### 3.3 Self-killing test (pre-pricing check)

> **ALGEBRIZATION CHECK.** For any house P-vs-NP attempt that
> passes the relativization check by naming arithmetization as its
> non-relativizing ingredient, answer in writing: *does the
> argument still go through when one side's oracle $A$ is replaced
> by a low-degree extension $\tilde A$ over a finite field — the
> $C^A \subseteq D^{\tilde A}$ / $C^{\tilde A} \nsubseteq D^A$
> forms?* If yes — **dead on arrival; arithmetization alone is an
> algebrizing ingredient, not an escape; stop, do not price it.**
> To pass, the attempt must name a **non-algebrizing** ingredient:
> a step with no low-degree-extension analogue, and the pair it
> fails on — for a separation attempt, a pair with
> $NP^{\tilde A} \subseteq P^A$; for an inclusion attempt, a pair
> with $NP^A \nsubseteq P^{\tilde A}$. "Uses polynomials over a
> field, but subtly" is not a named ingredient.

---

## 4. The unpriceable, named

**Formalizing any barrier theorem in Lean is unpriceable today** —
carried from the PNP-2 registration verbatim in substance. It is not
priced L, or XL, or "later at known cost"; it is *unpriceable*, and
this memo is the deliverable that stands in its place.

The reason is structural, not a matter of effort. A barrier theorem
is a theorem **about proof techniques**. Stating one honestly
requires a logic-of-proofs vocabulary the corpus does not own:
quantification over arguments themselves, or over the semantic
proxies the literature uses for them — all oracle worlds (§1.2),
all properties of Boolean functions together with circuits, density,
and pseudorandom generators (§2.2), all oracle / low-degree-extension
pairs together with algebraic oracle machines (§3.2) — each proxy
itself a theory (oracle TMs; circuit complexity and P/poly;
cryptographic generators; algebraic query complexity) that the
corpus has not built and PNP-1a does not begin. What *could* be
written today is a Lean file that asserts a barrier-shaped sentence
over classes rigged so the sentence holds by definition, or that
imports the barrier as an axiom: a **costume formalization** — the
theorem's clothes with no theorem inside. Producing that, and
counting it as a formalized barrier, is exactly the failure mode
this board's kill discipline (K-PNP-1: a pin satisfiable by
construction artifacts is vacuous; kill and re-enter) exists to
catch. The honest grades available today are the ones used here:
the barriers as cited T4 theorems, their statement shapes as T2
analysis, and their self-killing tests as house law for pricing.

## 5. What the map does NOT do — and the board's completeness picture

**What the map does not do.** It proves nothing about P vs NP. It
does not show P ≠ NP, does not show P = NP, does not show any
attempt the house might make will fail, and does not constrain the
problem — only the house's future attempts: an attempt that fails
one of the three checks in §§1.3 / 2.3 / 3.3 is not priced. The
barriers themselves are conditional or technique-relative in
exactly the ways stated (natural proofs carry their cryptographic
hypothesis; relativization and algebrization rule out *classes of
arguments*, not the truth of either answer). **Parts of P vs NP
closed: 0** — by this memo, and by the whole PNP line to date.

**Relation to PNP-1a/b/c — the board's completeness picture.**
The pins state the problem; this map fences the proof techniques.

- **Pin** — PNP-1a (definitions: `PolyDecider`, `InP`, `PClass`,
  `pairStr`, `InNP`, `NPClass`, landed as `PvsNPDefs.lean`) and
  PNP-1b (the board statement `PvsNPBoardStatement := PeqNP`,
  landed as `PvsNPStatement.lean`): the question, stated in the
  corpus's own vocabulary, NO CLAIM.
- **Witness** — PNP-1c (the K-PNP-1 witness brick: D5 decode,
  `Ldiag`, `KPNP1Witness : Prop := Ldiag ∉ PClass`, *stated, not
  proved*): the receipt that the pin's P is a non-vacuous notion —
  a language can be stated outside it.
- **Map** — PNP-2 (this memo): the three proved barriers as named
  statements, statement shapes, and self-killing tests.

With the map beside the pin and the witness, the PNP board's
**registered content is complete (pin + witness + map)** — complete
as a *board*: the problem stated honestly, its non-vacuity
witnessed at statement grade, and the known obstructions to proving
it mapped as pre-pricing law. Completeness of the board is not
progress on the problem: the dial stays where it was, **NO CLAIM;
parts of P vs NP closed: 0.**

---

## Sources (checked 2026-11-02; identifiers copied verbatim from these)

- **[S1]** Computational Complexity blog, "Favorite Theorems:
  Relativization" — "Theodore Baker, John Gill, Robert Solovay,
  Relativization of the P=?NP Question, SICOMP 1975"; oracles A, B
  with $P^A = NP^A$, $P^B \ne NP^B$.
  https://blog.computationalcomplexity.org/2006/03/favorite-theorems-relativization.html
- **[S2]** University of Toronto CSC 2429 lecture notes (Apr 2, 2014),
  bibliography — "[1] S. Aaronson and A. Wigderson, Algebrization:
  a new barrier in complexity theory, in STOC, 2008, pp. 731–740.
  [2] T. P. Baker, J. Gill, and R. Solovay, Relativizatons
  [sic] of the p =? np question, SIAM J. Comput., 4 (1975),
  pp. 431–442"; and "Theorem (Theorem 5.1). There exist oracles
  A, Ã such that $NP^{\tilde A} \subseteq P^A$."
  http://www.cs.toronto.edu/~toni/Courses/PvsNP/Lectures/lecture11.pdf
- **[S3]** Rybalov (2018), abstract quoting the classical theorem —
  "T. Baker, J. Gill and R. Solovay [SIAM J. Comput. 4, 431–442
  (1975)]: there exist two oracles A and B such that
  $P^A = NP^A$, but $P^B \ne NP^B$."
  https://explore.openaire.eu/search/publication?pid=10.17223%2F20710410%2F40%2F8
- **[S4]** EATCS, "Gödel Prize — 2007" — awarded to "Alexander A.
  Razborov and Steven Rudich" for ""Natural Proofs", Journal of
  Computer and System Sciences, Vol. 55, No. 1, 1997, pp. 24-35",
  "first presented at the Twenty-sixth Annual ACM Symposium on
  Theory of computing, Montreal, Quebec, Canada. 1994, pp. 204–213";
  citation notes the widely held conjecture that "pseudorandom
  number generators" exist, and the unconditional result for
  factoring / discrete log.
  http://eatcs.org/index.php/component/content/article/501
- **[S5]** "Natural proof", Wikipedia — notion "introduced by
  Alexander Razborov and Steven Rudich in their article "Natural
  Proofs", first presented in 1994, and later published in 1997";
  constructivity (decidable in (quasi-)polynomial time in the
  $2^n$-sized truth table), largeness ("sufficiently large
  fraction"), usefulness ("every sequence of boolean functions
  having the property infinitely often defines a language outside
  of C"); "assuming pseudorandom functions exist, these proofs
  cannot separate the complexity classes P and NP".
  https://en.wikipedia.org/wiki/Natural_proof
- **[S6]** Computational Complexity blog, "The Importance of Natural
  Proofs" (2006) — largeness + constructivity; "such a proof
  against polynomial-size circuits would break pseudorandom
  generators".
  https://blog.computationalcomplexity.org/2006/05/importance-of-natural-proofs.html?showComment=1147289640000
- **[S7]** S. Aaronson, A. Wigderson, "Algebrization: A New Barrier
  in Complexity Theory" (paper text, IAS-hosted PDF) — abstract
  ("access not only to an oracle A, but also to a low-degree
  extension of A over a finite field or ring"; "almost all of the
  major open problems — including P versus NP, P versus RP, and
  NEXP versus P/poly — will require non-algebrizing techniques");
  §1.2 definition and both pair forms
  ($NP^{\tilde A} \subseteq P^A$, indeed $PSPACE^{\tilde A}
  \subseteq P^A$; $NP^A \nsubseteq P^{\tilde A}$, indeed
  $RP^A \nsubseteq P^{\tilde A}$, $NP^A \nsubseteq BPP^{\tilde A}$);
  §1.3.2 PSPACE-complete easy instance.
  https://www.math.ias.edu/~avi/PUBLICATIONS/MYPAPERS/SCOTT/alg.pdf
- **[S8]** Arora–Barak draft, Ch. 23 (Duke-hosted) — "Theorem 23.9
  (Razborov, Rudich) Suppose a P-natural property Φ exists that is
  useful against P/poly. Then there are no strong pseudorandom
  function generators. In particular, FACTORING and DISCRETE LOG
  can be solved in less than $2^{n^\varepsilon}$ time…"
  https://courses.cs.duke.edu/spring07/cps240/lectures/naturalchap.pdf
- **[S9]** Princeton COS 598B Lecture 12 (2005) — natural-property
  definition (computable in $2^{O(n)}$ time from the truth table;
  usefulness against polynomial-size circuits) and "Theorem 3: If
  Discrete Log and Factoring do not have $2^{n^\varepsilon}$-time
  algorithms for some $\varepsilon > 0$, then there is no P-natural
  property useful against P/poly."
  https://www.cs.princeton.edu/courses/archive/spr05/cos598B/lec12.pdf

*House sources (not attribution sources): PNP-0 audit
`scoping-pnp-0-2026-11-02.md` §§1.4, 3–5 for the pin's shelf and
PNP-1a's shapes; `PvsNPDefs.lean` / `PvsNPStatement.lean` for the
landed names as written above.*
