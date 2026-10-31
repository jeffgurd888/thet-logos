# Q7CR-6c — LANDED: verdict (ii) ORBIT COVARIANCE (the pre-registered expectation, proved). K-Q7CR-6b DISARMED

**Verdict: the supplied C₇ action is NOT a symmetry of the instantiated Q⁷ package — it acts on the family of D₇-packages by the stated permutation of the clock-diagonal parameters (orbit covariance), with the spectrum preserved as a multiset and the C⁴ charge grading preserved as a spectator. A finding about the instantiated package, not a defect of the action or the object. NO CLAIM. Dials 0/4. Parts closed 0.**

**Standing sentence (verbatim, on the module's face): "via C4" survives only as "graded by C4."** Jeff's headline remains his T5 interpretation on Q7CR-0's face, untouched in either direction. K-Q7CR-6c (mediation) fired at scoping and stays fired; nothing here revives it.

## The decision

- **Family identity:** `q7ConjPow_diagOpC` — for every diagonal parameter d and every k, (S₇ᴿ)ᵏ · diagOpC d · (S₇ᵏ)⁻¹ = diagOpC (d ∘ cyc₇ᵏ). Instantiated: conjugation sends `factorQ7.D` to `diagOpC (a₇ ∘ cyc₇)`.
- **Non-symmetry at full rank:** `factorQ7_not_symm` — the conjugated package ≠ the instantiated package, decided by the exhibited moved entry (site 0: a₇ 0 = 3 ↦ a₇ 1 = −3); `a₇_injective` also proved (all seven clock entries distinct). Symmetry (option (i)) is therefore FALSE at the seat; orbit covariance (option (ii)) is the proved verdict.
- **Spectrum corollary:** the diagonal spectrum as a multiset is carried to itself (`q7ConjPow_diagSpectrum`, `factorQ7_spectrum_carried`) — exactly what is preserved (the multiset of entries) vs. what is moved (which site carries which entry) is stated on the face.
- **Charge clause, proved at the composite level:** `actQ7Comp = opTensorQ q7ShiftR 1 1` preserves every `sectorComp j` (`actQ7Comp_mem_sectorComp`, via `chargeComp_mul_actQ7Comp`) — the C⁴ grading is a spectator of the Q⁷ action.
- **Composite package transport, FULL** (the pre-authorized PARTIAL seam did not open): the partner package `factorQ7Orbit` built with pairing/involution laws transported; grading transport in the stated form (`q7Conj_one_gamma`); `composite_package_transport` per the memo's formula. Assembled headline `q7cr6c_verdict` (all five clauses).
- **K-Q7CR-6b (invisibility/decoration): DISARMED** — the action is visible: it permutes the package family in a stated orbit, carries a stated spectral reading, and preserves every stated charge sector. It neither leaves the packages invariant nor is it decoration; it is an orbit action.

## Parent verification (from disk)

- Module `lean/ThetLogos/Q7C4R4LinkCov.lean` (NEW): canonical counter **strict=23, defs=7**, zero attribute lines, zero "sorry"/`native_decide` tokens; the standing sentence verified verbatim ×1 by grep; no Span-3 vocabulary spent.
- Parent build green (3,380 jobs). Parent axiom check: all five checked headlines on exactly `[propext, Classical.choice, Quot.sound]` (builder's check covered six, same result).

## Census

9,067 → **9,090 strict** / 9,145 → **9,168 attribute-inclusive** / 312 → **313 modules** (delta +23 strict, +1 module).

## Backers since last landing

No change to the backer roll since the last landing.
