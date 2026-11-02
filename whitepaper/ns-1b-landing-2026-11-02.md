# NS-1b LANDING DOSSIER — the Navier–Stokes board statement — 2026-11-02

**Item:** NS-1b (Millennium Lane 3) — the statement half of
NS-1, against NS-1a's frozen definitions. **The NS pin is
complete.**

## VERDICT: BOARD STATEMENT LANDED — four alternatives at Fefferman shapes; K-NS-1 does not fire

**Artifact:** `lean/ThetLogos/NavierStokesStatement.lean`
— strict 5 (the five `Iff.rfl` unfoldings, labeled
statement-grade), defs 5. Verified by the coordinator in
the main tree (build green); all proved content on exactly
`[propext, Classical.choice, Quot.sound]`. NS-1a untouched.

**The four alternatives** (ν universally quantified inside
each — the composition choice is stated on the module's
face; the system Prop also carries 0 < ν internally):
- **A** — ∀ν>0, ∀ admissible u° (R³ data), f ≡ 0: ∃u p,
  system ∧ smooth ∧ bounded energy.
- **B** — the torus mirror (periodic data/forcing/solution
  packages, torus energy).
- **C** — ∀ν>0, ∃ (u°, f) with R³ data and (5)-admissible
  forcing, such that NO (u, p) satisfies system ∧ smooth
  ∧ bounded energy.
- **D** — the torus mirror of C.
- **`NSBoardStatement := A ∨ B ∨ C ∨ D`** — the Clay
  problem is solved by proving any one.

**The A/C relation, recorded exactly as the module states
it:** C is NOT ¬A; neither A⇒¬C nor C⇒¬A holds (A fixes
f ≡ 0 over ∀-data; C is ∃-data over all (5)-admissible
forcing — a C-witness may use f ≢ 0). ¬A⇒C holds. NS-0
§3's ¬C⇒A holds only under Fefferman's ambient-ν reading,
NOT under this ∀ν-inside composition (¬C yields A at a
single viscosity only). No implication is proved or claimed
as a theorem — this is audit reading at statement grade,
on the face. B/D mirror.

**K-NS-1 receipt:** the face vacuity check passed — no
unsatisfiable conjunct and no dropped side condition in
any composition; the five unfoldings are the receipt.

**Header fence:** the September 2026 (C)/(D) claim is
recorded as unverified and contested (per NS-0: arXiv
fidelity critique; CMI still listing the problem Active
at 2026-11-02); the pin neither endorses nor refutes it.

## Fences

NO CLAIM; **parts of Clay Navier–Stokes closed: 0.** The
board's statement-grade rung is complete: vocabulary
(NS-1a) + statement (NS-1b), at the same grade as RH-1 and
PNP-1a/b. Nothing beyond the pin is registered on this
board.

**Census after landing: 12,559 strict / 13,040 total / 436 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
