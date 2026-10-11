# Rung 3 Scoping: What a "Continuum Limit" Could Mean — Dossier (2026-10-10)

**Status:** Rung 3 scoping dossier. This document claims NO continuum limit.
Its job is to survey the candidate meanings, price each one exactly, and
kill every sentence that drifts into claiming a limit we do not have.

**Verdict: STANDS** — provided §0's kill guardrail and §6's kill list are
enforced. Any section that claims a limit is dead on sight; the section
dies, not the document.

**How to read the prices:** each option gets an *exact obstruction* (the
precise structure that does not exist), a *price* (what would have to be
built), and a *tractability rank* (§5). Prices are in work-units, not
calendar time: T1 = machine-checkable, T2 = formulable, T4 = numerical,
T5 = vision/research.

---

## §0. The conceptual guardrail (KILL ON SIGHT)

The finite factor `A_F` has **no scale parameter**. There is no `a → 0`, no
`L → ∞`, no refinement, no coarse-graining parameter attached to a finite
matrix algebra. A finite-dimensional spectral triple does not "become"
continuous under any limiting procedure — finite-dimensionality is preserved
by limits in the relevant topologies, and where it is not, what you get is
a different object entirely (an infinite-dimensional algebra), not "the
finite triple in the continuum."

Consequence, stated explicitly: **any continuum limit lives on the
manifold-factor side — refinement of M — with the finite factor riding
along unchanged.** The almost-commutative product `C^∞(M) ⊗ A_F` takes a
continuum limit exactly through its `C^∞(M)` factor. The sentence "the
finite triple converges to the continuum" is KILLED with the reason:
there is no directed system of finite triples to converge in (§1 names the
missing system exactly), and convergence of the product is convergence of
the manifold factor tensored with a fixed finite factor.

Related laundering that dies here: speaking of "the continuum limit of
ACMD" as if the finite Dirac `D_F` acquires a spatial resolution; speaking
of the 4-dim finite kernel as if it "becomes" the continuum zero-modes of
a Dirac operator; any use of the lattice toy's kernel factorization
(`ker = ker_lat ⊗ ker_F`) as evidence for continuum behavior — the
factorization is a finite-volume algebraic identity of the product form,
already labeled as such in the toy's own headline H2. Kill the carryover
language, not the identity.

---

## §1. Option A — Inductive limit of matrix algebras / AF-algebras

**The route.** In operator algebra, the standard way to get a continuum out
of finite pieces: a *directed system* of finite-dimensional C*-algebras
`A_1 → A_2 → ···` with unital injective *-homomorphisms, whose inductive
limit `A_∞ = lim→ A_n` is an AF-algebra (approximately finite-dimensional).
Refined to triples: a directed system of finite spectral triples
`(A_n, H_n, D_n)` with *compatible* Dirac operators — meaning the
embeddings intertwine the Diracs (typically `[D_n, π_n(a)]` controlled
across levels, or the triples converge in the spectral-propinquity sense).

**Exact missing structure.** We have **ONE triple** (`A_F`, 32-dim, KO-dim 6)
— not a directed system. Specifically absent:

1. **No tower.** There is no sequence `A_F^{(n)}` of algebras, no candidate
   embeddings `ι_n : A_F^{(n)} → A_F^{(n+1)}`. The finite algebra is a single
   object; nothing refines it.
2. **No Dirac compatibility relation.** Even if a tower were proposed, there
   is no rule for how `D_F^{(n)}` would pull back or push forward along the
   embeddings. Spectral-propinquity convergence (Latremolière) requires the
   Diracs to control the embeddings — no such control exists because there
   are no embeddings.
3. **No scale parameter.** AF convergence needs the system to "get finer" —
   but refinement is a property of the directed system, and §0 already
   killed the idea that the finite factor has an intrinsic scale to refine.
   Any tower would have to be invented wholesale, not read off the theory.

**Price.** Constructing a directed system is not "taking a limit" — it is
inventing a new mathematical object and then justifying why it converges.
Price: T5 (vision). This option is priced at *full invention cost*: the
system would have to be postulated, the compatibility of the Diracs proved
(T1-level work at best, if the system exists), and the identification of
the limit with anything physical separately argued. The limit object would
not be `A_F`; it would be a replacement for `A_F`.

**Tractability rank: 3rd (least tractable).** It asks the program to replace
the one piece of the product that is already machine-checked solid. No.

---

## §2. Option B — Lattice refinement (building on the Rung-2 toy)

**The route.** The Rung-2 toy (`scripts/rung2_lattice_toy.py`) built the
product `D_lat ⊗ I + Γ_lat ⊗ D_F` on a 4D lattice with `L = 3, 4`. The
refinement program: take `L → ∞`, `a → 0` (lattice spacing), hold physical
volume fixed, and ask whether the lattice product converges (in resolvent
sense, or via its spectral action / propagator) to the continuum product
`C^∞(M) ⊗ A_F`.

**What taking L → ∞ would require** — each item priced honestly:

1. **Doubler handling (the toy explicitly does not).** The naive lattice
   Dirac used in the toy has exact doubler zero modes at the 16 Brillouin
   zone corners (measured: kernel 64 at L=4 — labeled "exact doubler zero,
   toy artifact"). A real refinement program must pick a fermion
   discretization — Wilson (adds a mass term, breaks chiral symmetry
   explicitly), staggered/Kogut–Susskind (tastes), overlap/Ginsparg–Wilson
   (exact chiral symmetry, expensive), domain wall — each with its own
   broken-symmetry price. The toy deliberately leaves this open and labels
   it; the limit cannot be taken without paying the doubler tax. Price: T2
   (choose and formalize) + T4 (numerics at each L) before any limit exists.
2. **A scaling limit for the Dirac.** The lattice Dirac must be rescaled as
   `a → 0` so that the low spectrum converges to the continuum Dirac
   spectrum (the standard `D_lat → D_cont` via Bloch-wave analysis, with
   the Brillouin zone unwrapping onto ℝ⁴). This is textbook for the free
   naive/Wilson Dirac, T2–T4 territory — but it is a statement about the
   *lattice* factor only. Price: moderate, standard material.
3. **The finite factor rides along unchanged.** Under refinement, the
   product is `D_lat^{(L)} ⊗ I_{32} + Γ_lat^{(L)} ⊗ D_F` with `D_F` fixed
   at every L. There is no refinement of `D_F`, no scaling of the 32
   dimensions, no `L`-dependent finite algebra. Any limit theorem says:
   the lattice factor converges to the continuum manifold factor; the
   finite factor is a spectator parameter. This is the concrete
   instantiation of §0's guardrail. Price: zero — it's the one free part,
   and it is the point.
4. **The mixed-scale problem.** The toy mixed `a = 1` toy units with
   GeV-scale `D_F` "without apology" (its own words). A real refinement
   needs one coherent scale: either the lattice spacing is fixed against
   the finite Dirac's eigenvalues, or a joint scaling is justified. This
   is currently unpriced — it is a modeling decision, not a theorem. Label
   it as such.

**Why the toy is explicitly not this.** The toy's own header: "TOY. TIER
T4-AT-BEST NUMERICAL TOY. Not a continuum result." Its explicit
cannot-shows (§1e of the Rung-2 dossier): no continuum limit, doublers
unhandled, single tiny volume, no index theorem, mismatched units. L=3, 4
are two data points; a limit needs a *sequence* with a *controlled*
extrapolation. The toy's honest deliverable — kernel factorization as an
algebraic identity of the product form — is exactly the part that does NOT
depend on L, and therefore carries no continuum information. The toy is a
scaffold for the product structure, not a discretization of the manifold.

**Tractability rank: 2nd.** The physics community knows how to do lattice
refinement; the doubler tax is real but standard. But note what it buys:
it would validate the *product form* against a lattice approximation of
the manifold factor — it does not construct the continuum manifold, and
it does not touch the finite factor. Bounded deliverable, honest price.

---

## §3. Option C — The analytic package (Connes' reconstruction direction)

**The route.** The target is not a *limit* at all but the *analytic
axiomatization*: the statement that the product triple satisfies the
axioms that characterize the continuum — the direction of Connes'
reconstruction theorem. The axioms, per axiom, with exact T2-vs-missing
inventory against `TripleData` in `ProductTriple.lean`:

| Axiom | Status in the T2 classes | Genuinely analytic (missing) |
|---|---|---|
| **Bounded commutators**: `[D, π(f)]` bounded ∀ f | **Shadow present**: `TripleData` carries `D` and `π` as `Module.End ℂ S`; the commutator is *statable* (`prod_commutator_decomp` splits it T1). **Missing**: `S` is a bare ℂ-module — no norm, no inner product, so "bounded" is not even *statable*, let alone proved. The manifold factor would need the Sobolev/elliptic estimate. |
| **Compact resolvent**: `(D ± i)⁻¹` compact | **Absent entirely.** No topology on `End(S)` in the axiomatization; compactness of operators needs the Hilbert structure. This is the axiom that forces discreteness of the spectrum with finite multiplicities — it is *the* analytic core of "this is a geometry." Missing: the Hilbert space. |
| **Finiteness**: `H` is a finitely generated projective module over `A`, with an `A`-valued inner product | **Shadow present**: the spinor modules are carried as modules; the *algebraic* shape is statable. **Missing**: the Hermitian structure (A-valued inner product), which needs analysis (the Dixmier trace / integral). |
| **Reality**: the antilinear `J` with KO signs | **Shadow present**: `conjJ` is carried as the LINEAR anti-automorphism `X ↦ JXJ⁻¹` with the KO-sign axioms `hkoD`, `hkoΓ` — the algebraic relations close T1 (`conjJprod_D`, `conjJprod_Γ`). **Missing**: the antilinear `J` itself — pinned T5 (`AntilinearJProd`, §7). Note: Rung 3 Worker 1 is taking the J/Krein side; coordinate, don't duplicate. |
| **First-order condition**: `[[D, π(a)], π°(b)] = 0` | **Shadow present**: `ProdTwistedFirstOrderCond` is *formulated* (T5 pin) with the exact obstruction named (opposite involution for the doubled product algebra not constructed). **Missing**: the opposite-algebra representation `π°` via antilinear J — blocked on the antilinear pin above. |
| **Orientability**: Hochschild cycle `c` with `π(c) = Γ` | **Shadow partially present**: `Γ` is carried with `hΓsq`, `hΓD` (grading axioms); KO-dim arithmetic closes T1 (`koProd_signs`, `koDim_add`). **Missing**: the Hochschild cycle itself — needs the differential calculus over `C^∞(M)` (universal calculus modulo junk), which is manifold analysis. |
| **Poincaré duality**: K-theoretic cap-product pairing | **Absent.** Needs K-homology/K-theory of the C*-closure of the algebra — analytic index theory. No T2 shadow beyond the algebraic KO signs. This is the deepest analytic axiom and the farthest out. |

**The honest reading.** The T2 axiomatization is an *algebraic skeleton* of
the analytic package: it carries the objects the axioms talk about (`D`,
`π`, `Γ`, the KO signs, the `X ↦ JXJ⁻¹` shadow) and proves the algebraic
relations among them (T1), while every genuinely analytic word — bounded,
compact, Hilbert, Hermitian, cycle, index — is absent. This is not a
defect; it is the documented boundary (§7's "Analytic boundary" note:
"the class axiomatizes only the algebraic relations; nothing in this file
claims analytic control"). The reconstruction direction asks: starting
from the T2 skeleton, which analytic axioms can be *formulated* (T2
extension) vs *proved* (T1) vs merely *assumed* (T5)? Formulating them as
class extensions is attackable; proving them needs the continuum.

**Price per axiom (honest):** bounded commutators — formulable as a T2
extension once a norm exists (needs Hilbert space first: blocked on the
Hilbert pin); compact resolvent — the expensive one, needs the spectral
analysis of the manifold Dirac (genuinely Rung-3 continuum work);
finiteness — needs the Hermitian structure (T5); reality — coordinated
with Worker 1 (don't duplicate); first-order — blocked on reality;
orientability — needs the differential calculus (T5); Poincaré duality —
research-level (T5, farthest out).

**Tractability rank: 1st (most tractable) — but only the formulation
step.** Stating the analytic axioms as T2 class extensions over a
Hilbert-space-enriched `TripleData` is the cheapest concrete move in this
dossier. Proving them is the whole of Rung 3.

---

## §4. The finite factor rides along — the key conceptual point, restated

For the record, in the plainest possible language (per the standing
preference for jargon-free restatements):

The finite triple is a *fixed list of 32×32 matrices*. A continuum limit is
a procedure that makes something *finer*. You cannot make a fixed list of
matrices finer. So any honest continuum-limit program refines the
*manifold* side — more lattice points, smaller spacing, or the analytic
axioms that characterize the continuum Dirac — and the finite matrices
come along for the ride unchanged. The product converges because its
manifold factor converges; the finite factor contributes the same 32
dimensions at every stage. Anyone who says "the finite triple becomes
continuous" owes you either a directed system (§1: doesn't exist) or a
scale parameter (§0: doesn't exist). Kill the sentence, keep the product.

---

## §5. Ranked by tractability

1. **Option C, formulation step only** — formulate the analytic axioms as
   T2 class extensions over a Hilbert-enriched triple. *Price:* T2
   (formulation) per axiom; the proofs stay T5. This is the cheapest
   attackable next step (§5, below).
2. **Option B (lattice refinement)** — pick a doubler-handling
   discretization, run the L-sequence, check the lattice factor's
   spectrum converges. *Price:* doubler tax (T2+T4) + scaling limit
   (standard) + mixed-scale decision. Buys validation of the product
   form, not the continuum.
3. **Option A (AF / inductive limit)** — invent a directed system of
   triples wholesale. *Price:* full invention cost (T5); replaces the
   already-solid finite factor. Not recommended.

**Quarantined (not attackable now):** proving compact resolvent or
Poincaré duality for the product (needs the continuum Hilbert analysis —
the whole of Rung 3); any statement of the form "the finite triple
converges"; using the lattice toy's kernel factorization as continuum
evidence (already killed in the toy's own headlines).

---

## §6. Cheapest attackable next step (coordinate with Rung 3 Worker 1)

**The step:** extend the T2 class with the *analytic* axioms as
formulable-but-unproved structure — starting with the Hilbert inner
product on the spinor module (the single enrichment that unblocks
"bounded," "compact," "Hermitian" as statable words), then bounded
commutators and the finiteness Hermitian structure as further class
extensions. Everything stays clearly labeled: formulation T2, proof T5.

**Coordination boundary with Worker 1:** Worker 1 owns the J/Krein side —
the antilinear real structure and the Krein fundamental symmetry as T2
class extensions (the `AntilinearJProd` / `KreinProdPin` pins). This step
owns the *Hilbert/analytic* side — inner product, boundedness, compact
resolvent, finiteness. The two meet at reality/first-order: the
antilinear J (Worker 1) is the prerequisite for the opposite-algebra
representation in first-order (this step). Do not duplicate Worker 1's
definitions; reference them. If Worker 1 lands the Hilbert inner product
as part of the Krein work, this step's first extension collapses into a
reference — that's a win, not a conflict.

**What it explicitly does NOT do:** prove compactness of any resolvent,
claim any limit, touch the finite factor, or re-open the lattice toy.

---

## §7. Kill list (this dossier's own discipline)

Killed, with reasons, inside this document's scope:

1. **"The finite triple converges to the continuum"** — no directed
   system (§1), no scale parameter (§0). Dead.
2. **"The lattice toy shows the continuum"** — the toy's own cannot-shows
   stand; kernel factorization is L-independent and therefore
   continuum-free. Dead.
3. **`ρ_M ⊗ ρ_F` as any kind of product twist** — already killed in the
   Rung-2 dossier; stays dead (flip acts on pairs, not factors).
4. **Lorentzian-signature claims from the Krein pins** — the Rung-2
   dossier's "NO Lorentzian-signature claims" stands; Worker 1's Krein
   work does not re-open it.
5. **Any sentence in this dossier that claims a limit** — per the task's
   kill/stand rule, the section dies. Audit note: no such sentence
   exists in §§0–6; the document claims obstructions and prices only.

**What stands:** the three options with their exact obstructions and
prices; the §0/§4 guardrail; the ranked list; the single cheapest next
step with its Worker-1 coordination boundary.

---

*Local commit; nothing pushed. Dossier: Rung 3 Worker 3, 2026-10-10.*
