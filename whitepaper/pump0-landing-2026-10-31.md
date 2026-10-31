# PUMP-0 — LANDED: the charge pump registration pin (driven, miniature, net zero on its face)

**Date:** 2026-10-31 · **Brick:** PUMP-0 (S), head of the
PUMP line, per `scoping-charge-pump-2026-10-31.md`.
Module: `ThetLogos.ChargePumpPost`. **Verdict: LANDED**
(strict 1 / defs 12, parent-verified from disk; main-tree
build green, 3,244 jobs; the one strict item is the
proved face check).

**Fences: NO CLAIM. Parts of any official statement
closed: 0. Dials: 0/4.** **Claims registry: Card PUMP**
is registered for this line; its verdict brick is
PUMP-2 — no outcome class is reported until then.
**K-PUMP-4 discipline binds this dossier:** no
separation language for the transported quantity; the
β > 0 hypothesis is never dropped; what moves is sector
population of a chosen rung label, under an external
drive, with net-per-cycle exactly zero.

## What is registered

- **The seat (pin data):** sectors A = {0,1}, B = {2,3}
  of `Fin 4`; `χB` (1 on B, else 0), `QB` (its diagonal
  matrix form), `popB` (sector population); the state
  `chargePumpState β := gibbsState z4Generator β` —
  landed-identical to the Z4 ladder weights; the drive
  as EXTERNAL protocol data: `chargePumpTurnedWeight`
  (the j-th iterate of the landed `z4Shift` pullback),
  with `chargePumpFlux` (Δⱼ) and
  `chargePumpEnergyExchange` (Δ⟨E⟩ⱼ) as the registered
  per-step quantities.
- **Targets, verbatim in substance (memo §2):**
  `chargePumpH1` — the one-turn flux identity
  (popB change = z4Weight β 0 − z4Weight β 2
  = (1 − exp(−β/2)) / z4Partition β; positivity only
  under 0 < β, on the statement; the β = 0 flux = 0
  clause included); `chargePumpH2` — the cycle
  accounting (4-step exact return; Σ Δⱼ = 0 via
  Δⱼ₊₂ = −Δⱼ; directed crossing total exactly 1;
  per-step trace defect exactly 0; Σ Δ⟨E⟩ⱼ = 0);
  `chargePumpH3` — the drive characterization (a
  bijection transports zero sector population for all
  weight functions iff it preserves the partition).
- **The face check, proved (K-PUMP-1 guard discharged
  at registration):** `chargePump_face_check :
  χB (z4Shift 1) ≠ χB 1` — the pinned drive does NOT
  preserve the sector partition, so the transport
  headline is not vacuous by construction.

## On the face

The honesty clause is part of the pin: **no owned
charge operator exists at this seat** — the sectors are
rungs of a ladder and `popB` is population of a chosen
label; its identification with electric charge is
Jeff's T5 reading and is asserted nowhere in this line.
The state's own modular flow does nothing
(`gibbsWeight_stationary` cited): the clock turns are
applied by an external protocol, and the accounting's
honest words are fixed — *per-step flux, winding total
one, net zero, drive external, β sets the weights*.
Conservation is the rail, never a result (K-PUMP-3);
no field object is defined or implied (K-PUMP-5);
battery passivity is the standing rope. The line is
free-standing: it gates on nothing unlanded and is
independent of Q7CR-3 (whose composite charge grading
is a different, larger object).
**Census: 8,491 → 8,492 strict / 8,569 → 8,570
attribute-inclusive / 291 modules** (recounted from disk).

## Backers since last landing

The backer roll (`BACKERS.md`) is unchanged since the last
landing; no new confirmed gift is on the record. Thank you to
everyone reading the stream — the corpus is free for everyone,
forever.

*End of dossier.*
