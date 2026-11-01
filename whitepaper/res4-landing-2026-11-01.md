# RES-4 LANDING DOSSIER — 2026-11-01

## K-RES-1 FIRES AT THIS SEAT — at full rank, first

The mandatory evaluation (the RES scoping memo's pre-registered
kill, evaluated on the proved numbers):

- **Pigeonhole floor: 434. Proved excess: 434. Difference: 0.**
- `collCount3 = 15360` decomposes by the proved (a3) pattern
  into exactly three carrying triples: the diagonal
  (0, 0, 0) ↦ 13312 (within-factor degeneracy of the chosen
  coarse factors) and one **pairwise** face — the s₇–s_R shared
  gap ±4 with s₄ on its diagonal — (±4, 0, ∓4) ↦ 1024 each,
  2048 total. **Genuinely ternary terms (all coordinates
  nonzero): 0.**
- Named-ratio counts: `resCount 2 1 = 0`, `resCount 3 2 = 0`.
- Octave census: maximal dispersion — 14 classes, one distinct
  value per class, longest OctChain 0.

**Verdict: K-RES-1 FIRES at the Q7CR seat.** The seat's proved
resonance pattern is entirely floor + within-factor degeneracy
+ that one two-factor face. There is no ternary resonance
structure at this seat and nothing above the pigeonhole floor.
The seat is **bookkeeping**; the abstract theorems (RES-0..3)
are the RES line's content. This is the kill the line was
built to be able to fire — registered before the seat was
computed, fired on the proved numbers, reported at the same
volume as the line's landings.

## What landed (the module itself is FULL)

**Item:** RES-4, per the ratified scoping memo §3 and the
coordinator pack (`pack-res-4.md`). **Artifact:**
`lean/ThetLogos/SumResonanceSeat.lean` — strict 63, defs 13
(above the memo's 26–44 band: the overrun is consumed
infrastructure — factor multiplicity transports, explicit
diffRanges, the ternary count formula, tone forms — each used
by a deliverable proof; disclosed, not trimmed). Verified by
the coordinator in the main tree (build green, 3204 jobs);
all nine headlines on exactly
`[propext, Classical.choice, Quot.sound]`.

- **RES-4a (the bridge) FULL:** Q7CR-2 delivers its factor
  spectra over ℝ only; the module builds the ℚ mirrors and
  proves `seatSpecQ_cast_eq` — the RES-0 `sumSpec3` of the ℚ
  mirrors casts exactly to Q7CR-2's landed composite spectrum.
- **collCount3 by (a3), FULL in Lean:** the (a3) support is
  exactly the three triples above; `collCount3_seat = 15360`.
- **Ratios, zero-fenced, FULL:** unison 15360; octave 0; fifth
  0 (via the proved tone form (2w+1)/64; the zero-tone
  multiplicity at the seat is 0, so the fence correction is
  vacuous — proved, not assumed).
- **Octave census, FULL:** 14 distinct values, pairwise
  OctEq-separated, no OctChain of length 1 anywhere.
- **Forcing check, FULL in Lean:** `forcing_seat` — floor ≤
  excess ∧ excess = 434 ∧ difference = 0; max multiplicity 48
  at tone 257/64 (≥ the ceiling bound 32).
- **BRIDGE-1:** BR1-026 appended to the registry with this
  landing (exact-ℚ seat computation, script
  `res4-seat.py`; M₁ = 2723 and M₂ = 1518111/64 agree with
  BR1-012).

## A stale-read note, disposed of on the record

The RES-4 builder's Step-0 inventory described
`SumResonanceRatios.lean` (RES-3) as "untracked and incomplete,
ending in a sorry" — that was the file **as read mid-flight**,
while RES-3's own builder still had it in progress (RES-4 was
dispatched before RES-3 landed). The landed tree contradicts
the note: RES-3 is committed (2c39527), contains zero `sorry`
terms, and was coordinator-rebuilt green. RES-4 does not import
RES-3 (its ratio counts are proved from RES-0 directly), so
nothing in this landing depends on the stale read. Recorded so
the note never casts doubt on a landed module.

## Fences

§4 on the module's face: the factor spectra are CHOSEN INPUTS
(Q7CR-2's named choices; any clock-data diagonal among them is
entered measured data, T2/T4); seat resonances are properties
of the choices; **this line makes no Dial-1 entry**. NO CLAIM;
no dial moves. **The RES line is COMPLETE** (RES-0/1/2/3 FULL;
RES-4 FULL with K-RES-1 fired at its seat; RES-2b optional,
unfired).

**Census after landing: 11,359 strict / 11,586 total / 386 counted
modules; zero `sorry` terms tree-wide.**

## Backers since last landing

None new on the record since the last landing.
