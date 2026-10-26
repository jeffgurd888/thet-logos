# The Honest Battery — landing dossier

**Module:** `ThetLogos/SliceBattery.lean`
**Verdict:** built FULL; T1–T3 stand, T4 conditional exactly as
pre-registered
**Size:** 20 strict theorems / 7 definitions
**Build:** parent-verified in the isolated tree and again in the
main tree, parent build EXIT 0
**Axioms:** clean on all checked headlines
**Census after this landing and the FG-2c-3 landing:**
**5,684 strict theorems / 183 counted modules**
(was 5,589 / 181; +20 here, +75 for FG-2c-3)

**NO CLAIM.** This is a finite operator-theoretic package at the
program's own seat. It is not a device, not a power source, and
not a route around the zero-point extraction kill. It closes no
part of any official statement. The program's four dials stand at
**0/4**.

## In plain language

A battery is honest if its bookkeeping cannot lie. This one
stores energy in excited states of the slice Hamiltonian, and its
own theorems fix the bookkeeping: the vacuum's stored energy is
exactly zero, no allowed operation can extract more than was put
in, and the vacuum is a fixed point of every operation the theory
owns. It is a battery that provably cannot be overdrawn — and
whose emptiest state is not an engineering limit but a theorem.

The wider field's honest claim for quantum batteries is a
charging-speed advantage. Output greater than input is nobody's,
and nothing in this dossier says otherwise.

## D0 — the energy

The stored energy of a state `x` in the Hamiltonian's domain is

```
E(x) = Re ⟪Ĥx, x⟫
```

and this equals the value of the closed quadratic form discharged
earlier in the FG-2 line. The battery's energy is therefore not a
new quantity with a new name; it is the form's value, read as
storage.

## T1 — the floor

- `E(x) ≥ 0` for every state in the domain.
- `E(Ω) = 0`.

The vacuum is provably empty. This is the zero-point extraction
kill instantiated at this seat: the kill says no cyclic operation
can net-extract work from a ground state; T1 and T3 are that
principle made local, with this seat's own Hamiltonian, domain,
and vacuum.

## T2 — the vacuum is a fixed point

- `T̂_c Ω = Ω`.
- `R_λ Ω = λ⁻¹ • Ω` for every `λ > 0`.
- `cfc f T̂_c Ω = (f 1) • Ω` for every continuous `f`.

The last clause is proved by polynomial induction plus
Weierstrass approximation on `[0, 1]`, using the FG-2c-0 result
that the spectrum of `T̂_c` lies in `[0, 1]`. Every continuous
function of the transfer operator acts on the vacuum by the
scalar `f 1` and nothing else: on the vacuum, the whole operating
algebra idles.

## T3 — passivity, in full generality

For every domain-preserving continuous linear equiv `U`, the
extracted work satisfies

```
W(U) = E(Ω) − E(UΩ) ≤ 0.
```

No restriction to a special class of operations is needed. Any
allowed cycle that starts at the vacuum returns at most what it
started with — which is nothing. This is the general form of the
passivity statement at this seat, proved without descent to
special cases.

## T4 — the smallest stored quantum, conditional as pre-registered

T4 was pre-registered in its conditional form, and it lands in
exactly that form — no stronger.

**The implication is proved:** under the single named hypothesis
`SliceSpectralCorrespondence`, every unit state orthogonal to `Ω`
at the U(1) seat stores

```
E(x) ≥ −log(1 − δ)
```

for some `δ ∈ (0, 1)`. The existence of such a `δ` at `β > 0` is
itself proved from the weld's data (`sliceBattery_gap_exists`).

**The named hypothesis is the whole remaining content.**
`SliceSpectralCorrespondence` is exactly FG-2c-4's IDENTIFY
content: it is the statement that would tie the Hamiltonian's
energy scale to the transfer operator's gap. Accordingly:

- If FG-2c-4 IDENTIFY lands FULL, T4 discharges to unconditional
  in a later addendum, and that addendum — not this dossier —
  will carry the discharge.
- Until then, T4 is conditional, and it is printed conditional
  everywhere it is cited.

**Asserted nowhere in this package:** `exp(−Ĥ) = T̂_c`. Any
sentence that needs that identity needs FG-2c-4, and FG-2c-4 has
not landed at the time of this dossier.

## Backers since last landing

This is the first dossier to carry this section, under Jeff's
standing promise of 2026-10-25: **every donation will be published
with the proof stream.**

**The roll stands empty at this landing.** No donations were
confirmed by Jeff between the previous landing and this one, so
there are no names to inscribe here. The empty roll is printed
rather than omitted, so that the promise's bookkeeping is visible
even when it has nothing to report.

The rails, which are part of the promise:

- A name is published exactly as the giver wishes — full name,
  initials, a dedication, or anonymously.
- An amount is published only with the giver's okay; otherwise
  the entry records a gift of bench time.
- Inscription happens on Jeff's confirmation, because donations
  arrive where only Jeff can see them; a donation confirmed late
  is inscribed retroactively, dated by its gift, in the open.
- The channel is Cash App: **$Gurd888**.

The ledger of record is `BACKERS.md` in the public repository.
Each landing's dossier carries its backers section; the ledger
collects them.

## Fences

- **Not a power source.** The vacuum's ergotropy at this seat is
  zero by T1 and T3. Nothing here reopens, qualifies, or routes
  around the zero-point extraction kill.
- **Not a device.** No physical system, efficiency, capacity, or
  charging rate is claimed. The charging-speed advantage named
  above belongs to the field's literature framing, not to this
  package.
- **T4 is conditional** until FG-2c-4 lands, and is cited only as
  conditional until a discharge addendum exists.
- **Dials:** 0/4. **Parts closed:** 0.

---

*Next brick: FG-2c-4 IDENTIFY — whose landing, if FULL, also
carries T4's discharge. Free forever, for everyone — one common
bond.*

---

## Addendum (2026-10-26) — the correspondence after FG-2c-4

FG-2c-4 IDENTIFY has landed (dossier: `whitepaper/stage2-fg2c4-identify-landing-2026-10-26.md`, verdict PARTIAL-A with the split reversed from this dossier's expectation). The hypothesis `SliceSpectralCorrespondence` now stands as follows:

- **Jensen conjunct: DISCHARGED.** `sliceBattery_jensen` (in `ThetLogos/LatticeSliceIdentify.lean`) proves exp(−E u) ≤ ⟪u, T̂_c u⟫.re for every unit domain state at the circle seat, with no vacuum-orthogonality hypothesis. The battery's smallest-stored-quantum implication can now be quoted with this conjunct as a theorem.
- **Gap conjunct: STILL OPEN, sole remaining clause.** ⟪x, T̂_c x⟫.re ≤ 1 − δ awaits a completion transport (the corpus's gap bound controls the pre-completion operator's spectrum, not the completed operator's pairings). Until that transport exists, the correspondence as a whole remains a named hypothesis of this battery's T4 statement, exactly as the module's own docstring records.

## Addendum 2026-10-26 (completion transport — PARTIAL by the pre-registered slip)

`SliceTransport.lean` (strict 12) landed A1 (completed weld, by density) and A3 (moment step, b₁² ≤ b₂) IN FULL, and A2's spectrum dichotomy (every real spectral point of transferOp is 1 or ≤ 1 − δ, from GapBoundU1 alone). A2's form-gap step stopped at a machinery obstruction in the pin: `ContinuousFunctionalCalculus ℝ (osSpace →L[ℂ] osSpace) ?p` does not synthesize, and the hand-supplied instance's star is not defeq to `ContinuousLinearMap.instStarId`. NOT a math kill. The correspondence remains a carried hypothesis; its remainder is now exactly A2's form-gap, with Route A′ (compact spectral decomposition, priced L) the named continuation. Dossier: stage2-transport-partial-landing-2026-10-26.md.
