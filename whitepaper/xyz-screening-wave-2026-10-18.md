# P2 — The XYZ Screening Wave: the sector grid, screened to exhaustion

**Date:** 2026-10-18. **Item:** P2 of the heat/gravity/light XYZ
gauntlet, as inherited by the triadic pin
(`whitepaper/xyz-triadic-pin-2026-10-17.md`, §4): the screening wave
(gauntlet §6: PRICED — M), ratified into the build line by Jeff
2026-10-17 and launched on the trit experiment's landing under the
line-up rule. **Deliverable:** `lean/ThetLogos/TriadicScreening.lean`
(283 lines; **19 theorems + 1 definition**, strict counting
convention; targeted build green, 3,129 jobs; zero `sorry`/`admit`;
every theorem's axiom set is exactly `[propext, Classical.choice,
Quot.sound]` — in particular, **no `sorryAx`**: nothing here depends
on the quarantined `xyz_tripotents_exist`).

**Headline verdicts.**

- **(a) `genM 1`–`genM 6` are ALL tripotents (T1, proved).** The
  M-sector family's tripotence is now determined for every member:
  `genM 0` tripotent (prior corpus), `genM 1`–`genM 6` tripotent
  (this wave), `genM 7` not a tripotent (prior corpus).
- **(b) All 24 grid triples are DEAD — ALIVE 0, UNRESOLVED 0.**
  The 21 triples with `a ≠ 7` die by rule **R5** (ℤ[i] entry ring:
  the generated TRO provably misses `smGen 11`). The 3 triples with
  `a = 7` die at the tripotence screen (`genM 7` is not a
  tripotent). Each verdict below names its killing theorem.
- **(c) No sixth invariant was found — and none was needed.** The
  sector class is closed by R5 + the one tripotence fact + the
  finiteness of the grid. Assembled, the 24 kills prove
  **`¬ TriadicSectorExistence`** (T1): the sector sharpening
  R3♯(sectors) is REFUTED. Open Problem 2 itself is **not** touched
  and remains open — see the fences in §3, which are part of the
  verdict, not fine print.

Program count: 2,598 + 19 = **2,617** strict (parent to re-verify by
the standing recount). Clay parts closed: 0, before and after.

---

## §1. Sub-task (a): tripotence of `genM 1`–`genM 6`

The pin (§4, item 2) named this as P2's first sub-task: "the
tripotence of genM 1–6 is not established anywhere in the corpus
today." It is now established, positively, for all six.

| `a` | `Tripotent (genM a)` | Status | Address |
|---|---|---|---|
| 0 | yes | prior corpus | `tripotent_genM0`, `XYZTripotents.lean:1125` |
| 1 | **yes** | **this wave** | `tripotent_genM1` |
| 2 | **yes** | **this wave** | `tripotent_genM2` |
| 3 | **yes** | **this wave** | `tripotent_genM3` |
| 4 | **yes** | **this wave** | `tripotent_genM4` |
| 5 | **yes** | **this wave** | `tripotent_genM5` |
| 6 | **yes** | **this wave** | `tripotent_genM6` |
| 7 | **no** | prior corpus | `not_tripotent_genM7`, `XYZTripotents.lean:1161` |

**Method.** One uniform theorem, `tripotent_genM_of_ne_seven`
(`a ≠ 7` ⇒ `Tripotent (genM a)`), by the corpus's own
Hermitian-square-projector route (`tripotent_of_hermitian_sq_proj`,
used for `genM 0` in the fourth wave), with the `a = 0` computations
generalized:

- `genM_herm a` (self-adjointness, all `a`) — prior corpus,
  `MartinettiRep.lean:3039`.
- `genM_sq_diag a` (this wave): `(genM a)² = Matrix.diagonal
  (genMsupp a)` for **every** `a`, by `genM_sq_onblock` (prior
  corpus) plus §A's off-diagonal vanishing. The a-general support
  projector `genMsupp a` replaces the a-0-specific `genM0supp`.
- §A, the `Fin 3` computations (this wave): `gellMann_sq_offdiag`
  (every `(gellMann a)²` is diagonal, all `a`) and
  `gellMann_sq_of_ne` (for `a ≠ 7`, the square's diagonal is 1
  wherever `gellMann a` has a nonzero entry), both by finite case
  analysis over `Fin 8 × Fin 3 × Fin 3`. Read off those
  computations, the square patterns are `diag(1,1,0)` for
  `a = 0, 1, 2`; `diag(1,0,1)` for `a = 3, 4`; `diag(0,1,1)` for
  `a = 5, 6` — and `diag(1/3, 1/3, 4/3)` for `a = 7`, whose
  non-{0,1} values are exactly where the support step, and with it
  tripotence, fails. No step of (a) was blocked; no negation was
  needed for any of 1–6.

## §2. Sub-task (b): the 24-triple grid

Grid: `X = genC` (the only member of `sectorC`), `Y = genH k`
(`k : Fin 3`), `Z = genM a` (`a : Fin 8`). Member tripotence going
in: `genC` ✓ (`tripotent_genC`), `genH k` ✓ (`tripotent_genH`),
`genM a` per §1. Screens applied per triple: the tripotence screen;
R1 (diagonal), R2 (conjugation), R3 (sector support), R4
(pair-support), R5 (entry ring); and the reachability scoreboard
(membership reach is proved uniformly by
`sector_triple_reaches_members`: every grid triple reaches its own
three members, i.e. `smGen 0`, `smGen (k+1)`, `smGen (a+4)` under
the definitional identifications of `smGen`).

Applicability of R1–R4 to the grid, once for all rows: **R2** does
not apply (no grid member is a conjugate of a diagonal matrix; the
members are the raw sector generators). **R3** does not apply
(grid triples are multi-sector by construction — that was the
pin's design; R3 kills single-sector confinement). **R4** does not
apply (its form is `{UJ, D₁, D₂}`; no grid triple contains `UJ`).
**R1** applies, by inspection of the defining matrices, only where
all three members are diagonal — `(k, a) = (2, 2)` and `(2, 7)`
(`genH 2` is σ₃-block-diagonal, `genM 2`/`genM 7` are
λ-diagonal); this is recorded as an inspection note, not a
theorem, and **no verdict rests on it** — both rows are already
dead by their primary kill.

| # | `k` | `a` | Verdict | Killing rule / theorem |
|---|---|---|---|---|
| 1 | 0 | 0 | **DEAD** | R5 — `sector_triple_misses_11` (misses `smGen 11`) |
| 2 | 0 | 1 | **DEAD** | R5 — `sector_triple_misses_11` |
| 3 | 0 | 2 | **DEAD** | R5 — `sector_triple_misses_11` |
| 4 | 0 | 3 | **DEAD** | R5 — `sector_triple_misses_11` |
| 5 | 0 | 4 | **DEAD** | R5 — `sector_triple_misses_11` |
| 6 | 0 | 5 | **DEAD** | R5 — `sector_triple_misses_11` |
| 7 | 0 | 6 | **DEAD** | R5 — `sector_triple_misses_11` |
| 8 | 0 | 7 | **DEAD** | tripotence screen — `not_tripotent_genM7` (Z fails) |
| 9 | 1 | 0 | **DEAD** | R5 — `sector_triple_misses_11` |
| 10 | 1 | 1 | **DEAD** | R5 — `sector_triple_misses_11` |
| 11 | 1 | 2 | **DEAD** | R5 — `sector_triple_misses_11` |
| 12 | 1 | 3 | **DEAD** | R5 — `sector_triple_misses_11` |
| 13 | 1 | 4 | **DEAD** | R5 — `sector_triple_misses_11` |
| 14 | 1 | 5 | **DEAD** | R5 — `sector_triple_misses_11` |
| 15 | 1 | 6 | **DEAD** | R5 — `sector_triple_misses_11` |
| 16 | 1 | 7 | **DEAD** | tripotence screen — `not_tripotent_genM7` |
| 17 | 2 | 0 | **DEAD** | R5 — `sector_triple_misses_11` |
| 18 | 2 | 1 | **DEAD** | R5 — `sector_triple_misses_11` |
| 19 | 2 | 2 | **DEAD** | R5 — `sector_triple_misses_11` (R1 also applies, inspection note above) |
| 20 | 2 | 3 | **DEAD** | R5 — `sector_triple_misses_11` |
| 21 | 2 | 4 | **DEAD** | R5 — `sector_triple_misses_11` |
| 22 | 2 | 5 | **DEAD** | R5 — `sector_triple_misses_11` |
| 23 | 2 | 6 | **DEAD** | R5 — `sector_triple_misses_11` |
| 24 | 2 | 7 | **DEAD** | tripotence screen — `not_tripotent_genM7` |

**Counts: DEAD 24 (21 by R5, 3 by the tripotence screen);
ALIVE 0; UNRESOLVED 0.**

The uniform form of the verdict is one theorem,
`sector_triple_dead (k : Fin 3) (a : Fin 8)`: no triple
`(genC, genH k, genM a)` is a tripotent triple generating all
twelve `smGen`. The R5 rows rest on three ℤ[i]-entry facts —
`genH_gaussInt` (prior corpus), `genC_gaussInt` and
`genM_gaussInt_of_ne_seven` (this wave, §C of the module; the
latter via `gellMann_gaussInt_of_ne_seven`: entries of
`gellMann a`, `a ≠ 7`, lie in `{0, ±1, ±I}`) — composed with the
corpus's R5 theorem `no_gaussInt_triple_reaches_genM7`
(`XYZTripotents.lean:901`).

Scoreboard note for the `a = 7` rows: as matrices, those triples
do contain `smGen 11 = genM 7` by membership — but the target's
`Tripotent Z` conjunct fails, so they are not candidate witnesses
at all. The scoreboard's proved reach for every row is exactly its
own three members; no row's full generation was left UNRESOLVED,
because each row carries a proved obstruction (R5 rows: at
`smGen 11`; `a = 7` rows: at the tripotence conjunct).

## §3. The assembly, and its fences

`sectorC` is a singleton, `sectorH` and `sectorM` are ranges over
finite index types. So any witness to `TriadicSectorExistence`
*is* one of the 24 grid triples, and the 24 verdicts assemble in
eleven lines (`not_triadicSectorExistence`):

> **R3♯(sectors) is REFUTED (T1).** There do not exist
> `X ∈ sectorC`, `Y ∈ sectorH`, `Z ∈ sectorM`, each a tripotent,
> whose generated TRO contains all twelve `smGen`.

This is recorded under the commission's kill-outcome clause: the
screens closed the whole (sector) class, and the closure is
proved, not conjectured. It is a corollary of the screens, not a
separate attack on existence.

**Fences — what this does NOT do.**

- **Open Problem 2 (`xyz_tripotents_exist`) remains OPEN.** It
  quantifies over all matrices. A witness built from tripotents
  outside the three named families — in particular from
  non-ℤ[i]-valued tripotents, which R5 cannot see (e.g. suitable
  projections with irrational entries) — is untouched by every
  screen here. Nothing in this wave constrains such triples, and
  the corpus's one quarantined `sorry` (the statement's own, at
  `XYZTripotents.lean:492`) is neither used nor discharged.
- The unrestricted generating claim R3 (gauntlet) therefore stays
  exactly where the pin left it: PARTIAL, skeleton = Open Problem
  2. What died is the pin's *sector sharpening* of it — the
  one-per-named-family restriction. Any future candidate enters,
  per the house relabeling rule, as a new candidate, not as a
  resurrection of R3♯(sectors).
- No principle seat labels are affected (there are none; pin §1).

## §4. Sub-task (c): the sixth-invariant slot

**No sixth invariant is claimed — neither proved nor conjectured
by this wave.** The screens suggested none, because none was
needed: the sector class closed under R5 + the `genM 7`
tripotence fact + grid exhaustion. For the record, the reason no
invariant of the R5 *family* can close the unrestricted class:
R5 is the instance `R = ℤ[i]` of an entry-ring invariant — any
subring of ℂ closed under `star`, addition and multiplication is
preserved by ternary products and hence by `MemGenTRO` (the ℤ[i]
case is the corpus's `memGenTRO_gaussInt`; the parametrized
generalization is a remark here, not a formalized theorem). Such
an invariant obstructs only triples valued in `R`, and tripotents
with entries outside any fixed proper `R` exist; so no entry-ring
invariant closes Open Problem 2. A class-closing invariant for
the unrestricted problem — or a construction — remains what the
pin's §5, item 1 priced it: **UNPRICED (research)**. The
sixth-invariant slot in the wave's commission is therefore
answered: *empty, with the reason stated*.

## §5. Verification record

- Build: `lake build ThetLogos.TriadicScreening` — green,
  **3,129 jobs**; `.lake/build/lib/lean/ThetLogos/
  TriadicScreening.olean` present.
- Axioms: `#print axioms` run on all 19 theorems of the module
  (scratch probe, deleted): each depends on exactly
  `[propext, Classical.choice, Quot.sound]`. **No `sorryAx`** —
  the wave imports `ThetLogos.TriadicPin` (hence
  `XYZTripotents.lean`) but depends on `xyz_tripotents_exist`
  nowhere.
- Counts: strict method (line-initial `^(theorem|lemma) ` on
  comment-stripped source): **19 theorems**, 1 definition
  (`genMsupp`). Module total for the program: 2,598 → 2,617.
- The corpus's pre-existing fences are unchanged: the sole
  `sorry` at `XYZTripotents.lean:492` stands quarantined inside
  its own statement; this module adds no `sorry`/`admit`
  (grep-verified, zero hits in code or prose).

## §6. Deviations, named

1. **The assembly (§3) goes one formal step beyond per-triple
   verdicts.** It is included deliberately: it is a proved
   corollary of the commissioned screens (via the singleton/range
   shapes of the sector families), claimed under the commission's
   clause that a proved closure of the class is a legitimate KILL
   outcome for the wave. Its fence (Open Problem 2 untouched) is
   stated in the module header, the theorem's docstring, and §3
   above.
2. **The sixth-invariant deliverable is an empty slot with a
   reason (§4)**, rather than a stated invariant: the screens
   closed the commissioned class without one.
3. No other deviations. Sub-task (a) needed no negations and hit
   no blockers; sub-task (b) left no row unresolved.

*End of dossier. The screening wave's deliverable is a closed
grid: six tripotence determinations, twenty-four kills with named
killers, and one refuted sharpening — with the problem it sharpens
left standing, open, exactly where it was.*
