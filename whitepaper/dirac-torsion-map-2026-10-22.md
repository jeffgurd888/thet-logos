# DiracTorsionMap — the D_F Torsion Map: BOTH SEATS SETTLED (2026-10-22)

**Commission:** queue item 3 of the unparked fleet line, admitted by Jeff
2026-10-19 ("density side first, torsion map after"). Priced step 1 of the
Morley gauntlet dossier (§7): *build η from Dirac data (grading/sign),
compute the induced defect T under inner fluctuations D ↦ D_A.*
`EdgeSignature` (§3, T1) built the abstract law and left this D_F-specific
map priced and unbuilt; this brick builds it.

**Module:** `lean/ThetLogos/DiracTorsionMap.lean` — **18 strict
theorems/lemmas, 4 defs**.

## The law, instantiated

`EdgeSignature`'s law needs only `η² = 1` — no self-adjointness, no
Hermiticity: `torsion_defect : (η + T)(η + T) = 1 + (ηT + Tη + T²)`, and
flatness is `(η + T)² = 1 ↔ ηT + Tη + T² = 0`. Here it is instantiated at
`R := Matrix (Fin 32) (Fin 32) ℂ` on the corpus's actual finite Dirac
family (`FiniteSpectralTriple.buildDirac`, the MartinettiRep `smDirac`),
with `fluctuatedDirac D A = D + A + UJ Aᵀ UJ` the corpus's inner
fluctuation. Two seats for η were put to the question.

## Seat 1 — the grading seat (η := γ_F): SURVIVAL STANDS

`grading_seat_survival`: the grading seat's torsion map is the **zero
map**. The uncorrected grading's defect vanishes, and the substance is
the invariance theorem `fluctuatedDirac_gamma_odd`: every inner
fluctuation of a γ-odd Dirac operator by a γ-odd 1-form stays γ-odd — the
η read off the grading is unchanged by `D ↦ D_A`, so the induced
correction is `T = 0` and flatness holds trivially.

## Seat 2 — the sign seat (η₀ := y⁻¹·D₀): SURVIVAL KILLED, for every s ≠ 0

On the flat sector, η₀ is the normalised flat Dirac operator (T2
nomenclature for the seat; `smDirac_flat_sq` proves η₀² = 1 at `y ≠ 0`).
The deformation is the Majorana line `s`. The verdict is an exact iff:

`majorana_survival_iff : (η₀ + T)² = 1 ↔ s = 0` (for `y ≠ 0`).

The kill has a named witness: `defect_entry` computes the defect at the
single entry `(⟨0⟩, ⟨24⟩)` — the (ν_L, ν̄_R) corner — as exactly
`(↑y)⁻¹ * star s`, nonzero for every `s ≠ 0`. In the sign seat, D_F's
torsion **is** the Majorana block, and it does not survive: the deformed
operator is an involution only where the Majorana block vanishes.

This is a kill delivered as a T1 theorem, reported at the same speed as
the Seat 1 stand, per the house rule: a proved failure is a result.

## Verification

- Build: `lake build ThetLogos.DiracTorsionMap` green — "Build completed
  successfully (8985 jobs)", lake exit code 0 captured to a file (never
  piped); `.olean` present (1,946,840 bytes). The compile survived three
  VM restarts; all scratch lived in persistent storage and each run was
  relaunched cleanly, one build at a time.
- Repairs during compile touched **proof bodies only** (30 hunks, all
  after draft line 278): declaration signature lines verified
  byte-identical to the draft; no statement, name, definition, seat
  identification, or header claim was narrowed. One root cause worth the
  record: the draft's `(↑y)⁻¹ • …` elaborates with scalar type ℝ, so
  ℂ-scalar lemmas silently mismatched until the proofs were routed
  through the shown real-scalar form.
- Parent verification on the shipped text: source md5 matches the built
  source exactly; independent comment-stripped scan — strict 18, defs 4,
  sorry 0, admit 0, axiom declarations 0; headline statements read
  directly.
- `#print axioms` on `grading_seat_survival`,
  `fluctuatedDirac_gamma_odd`, `majorana_survival_iff`, `defect_entry`,
  `smDirac_flat_sq`, `dirac_torsion_flat_iff`: each exactly
  `[propext, Classical.choice, Quot.sound]`. No `sorryAx`, no new axioms.

## Fences

- The sign seat lives on the flat sector (all Yukawa values equal to a
  single real `y ≠ 0`, Majorana value `s`); the iff is a statement about
  that sector and that deformation line, not about arbitrary
  fluctuations of the full five-parameter family.
- The grading seat's survival is an invariance statement about γ-odd
  fluctuations; it says nothing about fluctuations with γ-even parts.
- Finite toy only: no continuum torsion, no spacetime torsion tensor, no
  part of any official Clay statement. The board remains NO CLAIM.

## Ledger effect

The EdgeSignature law now has its D_F instance: the abstract defect
calculus is no longer floating free of the corpus's Dirac operator.
Seat ledger: grading η survives fluctuations (T = 0); sign η survives
nothing — the Majorana block is exactly the obstruction, measured at one
entry.

Program census: 3,442 → **3,460 strict** / 3,482 → **3,500
attribute-inclusive**; counted modules 123 → **124**.
