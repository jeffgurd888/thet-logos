# Trit Experiment — Results Dossier

**THE §4 EXPERIMENT OF THE TRIT–DATA-CENTER CHARTER, RUN AND DECIDED.
Verdict: DIES-K3.** Written 2026-10-18. Charter:
`whitepaper/trit-datacenter-scoping-DRAFT-2026-10-17.md` (§4 design,
§5 kills, §6 public language). Protocol, code, and raw results:
`~/workspace/trit-experiment/` (`PROTOCOL.md`, `results/*.json` — every
number below matches those files). Pre-registration: `PROTOCOL.md` was
written before any scored run; the thresholds below are its, not
post-hoc.

Tier discipline (charter): everything empirical here is a **software
emulation on binary hardware with modeled energy (Proxy P1)** plus a
fenced wall-time supplement. No ternary hardware exists; no number in
this dossier is a hardware energy saving (K4); no gallon, facility, or
water sentence is licensed by anything here (K5, charter §6).

---

## 0. Verdict, in the pre-registered shapes

**DIES-K3 — "it's the bits, not the base."**

- At fixed accuracy, the ternary configuration's modeled energy per
  token beat the best binary low-precision baseline by **+58.0%**
  (Proxy P1) — far past K1's 10% margin. K1's energy test, on the one
  proxy this environment could compute, **passes**.
- But the K3 decomposition shows the win is **fully accounted for by
  bits moved per token**: a hypothetical binary scheme at *exactly
  ternary's bit-width* (1.58 bits/weight, identical traffic in every
  term) posts modeled energy a hair **below** ternary's. The
  radix-attributable residual is **−0.108 µJ/token** (−0.027% of the
  best-binary baseline) — i.e., ≤ 0, and K3 fires by its pre-registered
  condition.
- What survives: a literature note, exactly as K1/K3 pre-scripted —
  *low precision helps; three-ness, at this scale of evidence, does
  not separably help.* The trit framing of the data-center direction
  dies in writing, per Jeff's ruling. Low-precision inference itself
  is vindicated — as the literature already knew, and as our INT4 row
  shows again.
- Proxy P2 (wall energy): **ENVIRONMENT-BLOCKED** — this VM exposes
  no RAPL/powercap counters. The verdict rests on P1 alone, with this
  fence printed (protocol §6 contingency, fixed in advance).

## 1. Protocol summary

Full text: `~/workspace/trit-experiment/PROTOCOL.md`. Essentials:

- **Task:** word-level LM, WikiText-2 raw v1 (HF `Salesforce/wikitext`
  parquet — the original S3 zip endpoint is dead; same dataset).
  Vocabulary: train frequency ≥ 3 → **33,277** types. Train stream:
  first 400,000 train tokens. Eval stream: first 512 non-overlapping
  128-token chunks of the test stream (65,536 stream tokens; **65,024
  scored positions** under the standard shift — see §6, deviation 4).
- **Model:** one FP32 master — decoder-only transformer, d_model 128,
  3 layers, 4 heads, d_ff 512, tied embeddings, **4,870,912 params**
  (4,849,280 matmul weights). AdamW lr 2e-3, batch 16×128, 585 steps
  (3 epochs), seed 20261018. Trained in 1,009 s on 2 cores; final
  training loss 6.54.
- **Fixed accuracy band:** eval perplexity ≤ 1.10 × the FP16 variant's
  eval perplexity. FP16 reference: **712.76** → band ceiling **784.04**.
- **Variants:** FP16; INT8 (primary: torch dynamic-quantized Linear
  from the master; sensitivity row INT8-PERROW); INT4; INT2;
  TERNARY-PTQ (BitNet absmean rule); TERNARY-QAT (150 STE fine-tune
  steps from the master, lr 5e-4; 286 s; final loss 6.587). PTQ and
  QAT ternary are different objects, reported separately, never pooled
  (charter §4). Primary ternary = QAT if in band, else PTQ.
- **P1:** per generated token, batch-1 decode, context 128 — exact
  op/traffic census × Horowitz ISSCC 2014 (45 nm) table (protocol
  §5.2; sub-8-bit multiply by the pre-registered quadratic scaling).
  Components: arithmetic / weight traffic / activation traffic / KV
  traffic.
- **P2:** RAPL — blocked (§0). Supplementary wall-time per generated
  token (greedy, 64 tokens, fixed 16-token prompt, full-context
  recompute harness, 3 interleaved rounds, median): printed in §4,
  labeled NOT energy, excluded from the verdict.
- **K1:** ternary ≥ 10% below best in-band binary baseline in both
  proxies (P2 blocked → P1 carries, fence printed). **K3:** radix
  residual = E(equal-bits binary counterfactual) − E(ternary) ≤ 0
  fires the kill.

## 2. Environment census

| item | value |
|---|---|
| machine | VM, AMD EPYC 9D25, **2 cores**, 7 GB RAM |
| OS / Python | Linux, Python 3.12.3 |
| torch | 2.14.1+cpu (venv, CPU wheel index) |
| numpy / pyarrow | 2.5.4 (venv) / 26.0.0 |
| RAPL / powercap | **absent** (`/sys/class/powercap/` empty) → P2 blocked |
| dataset | WikiText-2 raw v1 parquet via HuggingFace |

## 3. Accuracy (the gate)

Eval perplexity + top-1 next-token accuracy, fixed eval stream:

| variant | ppl | top-1 | in band (≤ 784.04) |
|---|---|---|---|
| FP32-master (context) | 712.53 | 0.1083 | — |
| **FP16 (reference)** | **712.76** | 0.1084 | ✓ |
| INT8 (dynq) | 713.46 | 0.1085 | ✓ |
| INT8-PERROW (sensitivity) | 712.65 | 0.1083 | ✓ |
| INT4 | 717.58 | 0.1081 | ✓ |
| INT2 | 1582.08 | 0.0872 | ✗ |
| TERNARY-PTQ | 1716.94 | 0.0716 | ✗ |
| **TERNARY-QAT (primary)** | **696.13** | **0.1099** | ✓ |

Readings, plainly:

- **Best binary baseline = INT4** (INT8 also in band; INT2 out).
- **TERNARY-PTQ fails the fixed-accuracy gate outright** (ppl 1716.9,
  2.4× the reference). At this scale, ternary weights cannot be
  stamped onto a conventionally trained net after the fact — the
  trained-ternary object is the only ternary object, consistent with
  BitNet's trained-from-scratch premise (charter §2.2).
- TERNARY-QAT's 696.13 is *below* the FP16 reference. Named cause:
  the QAT row consumed 150 extra fine-tuning steps the PTQ rows did
  not — that budget is the BitNet method's cost, pre-registered and
  disclosed, and the band is a ceiling, not a ranking. The margin is
  small (2.3%); no claim is made on it.
- Absolute perplexities (~700) are a 4.9M-parameter word-level model's
  numbers. The experiment is a *relative* comparison at fixed
  accuracy, as chartered — nothing here is a language-modeling result.

## 4. Proxy P1 — census results (modeled energy per token)

µJ/token, batch-1 decode, context 128. Full table in
`results/census.json`.

| variant | arith | weight traffic | act traffic | KV traffic | **total** |
|---|---|---|---|---|---|
| FP16 | 9.895 | 1551.770 | 0.103 | 31.703 | **1593.471** |
| INT8 | 1.484 | 775.885 | 0.051 | 15.852 | **793.272** |
| INT4 | 0.757 | 387.942 | 0.051 | 15.852 | **404.602** |
| INT2 (out of band) | 0.575 | 193.971 | 0.051 | 15.852 | **210.449** |
| **TERNARY (1.58 bit)** | 0.660 | 153.237 | 0.051 | 15.852 | **169.800** |
| TERNARY @ 2-bit packing (sensitivity) | 0.660 | 193.971 | 0.051 | 15.852 | **210.534** |
| **BITS-ONLY counterfactual** | 0.552 | 153.237 | 0.051 | 15.852 | **169.692** |

Weight traffic is 96–98% of every total: at batch-1 decode, this
experiment is a measurement of *bytes moved*, which is precisely the
terrain K3 was written for.

**K1 margin (P1):** (404.602 − 169.800) / 404.602 = **+58.03%** vs the
best binary baseline (INT4). Passes ≥ 10%.

**K3 decomposition:** the ternary–INT4 gap is 234.80 µJ; the
weight-traffic term alone accounts for 234.71 µJ of it (153.237 vs
387.942 — the 1.58-vs-4 bit-width ratio), the arithmetic term adds
+0.10 µJ in ternary's favor vs INT4's multiplier — and against the
*equal-bits* binary counterfactual the sign flips:

> radix residual = E_BITS-ONLY − E_TERNARY
> = 169.692 − 169.800 = **−0.108 µJ/token** (−0.027% of baseline) ≤ 0.

In the Horowitz table, ternary's select/add (an INT8 add, 0.03 pJ)
costs *more* than a quadratically-scaled 1.58-bit binary multiply
(0.0078 pJ); accumulation (0.1 pJ) and every traffic term are
identical. Nothing is left over that belongs to the radix. **K3
fires.**

**Sensitivity that seals it:** pack ternary at the 2 bits/trit that
real kernels (bitnet.cpp) actually use, and its modeled total is
210.53 µJ — indistinguishable from the 2-bit binary scheme's 210.45.
At honest packing, "ternary" and "2-bit binary" are the same energy
story told in two vocabularies.

**Supplementary wall-time (NOT energy; excluded from the verdict):**
median ms/token, emulation harness — INT8-DYNQ 4.26;
TERNARY-QAT-DYNQ 5.12; INT4-DEQ 13.46; TERNARY-QAT-DEQ 14.55;
INT2-DEQ 15.46; TERNARY-PTQ-DEQ 15.76; FP32-master 15.87; FP16 78.72.
These measure what this binary CPU spends *emulating* each
configuration (real int8 kernels vs dequantize-per-pass harnesses vs
CPU float16), nothing about represented arithmetic. Full rounds in
`results/timing.json`.

## 5. Verdict application (mechanical, protocol §7)

1. Accuracy gate: TERNARY-QAT in band → primary ternary = TERNARY-QAT.
   INT2 and TERNARY-PTQ out, as printed.
2. Best binary baseline: INT4 (404.602 µJ). K1 margin (P1) +58.03%
   ≥ 10% — K1 does **not** kill on energy. (P2 environment-blocked;
   K1's two-proxy form could not be completed in this environment —
   fence recorded, and moot: K3 decides.)
3. Radix residual −0.108 µJ ≤ 0 → **DIES-K3**.

**The direction — ternary representation as a separable energy lever
for inference, and with it the trit framing of the data-center
question — dies in writing, here.** The kills were named before the
runs (charter §5); the numbers fell where they fell.

## 6. Deviations from protocol, named

1. **Dataset transport:** WikiText-2 arrived as HuggingFace parquet,
   not the charter-era S3 zip (endpoint dead). Same wikitext-2-raw-v1
   data. (Logged in PROTOCOL.md §0 before runs.)
2. **INT8 object clarification (§7b of the protocol, logged before
   any run):** the protocol named both per-channel PTQ and torch
   dynamic quantization for INT8; the primary row is the
   dynamic-quantized object, with the per-row object evaluated as a
   sensitivity row. P1 is identical for both; the verdict path is
   unaffected.
3. **P2 environment-blocked** (no RAPL): pre-registered contingency,
   exercised. Wall-time printed as supplement only.
4. **Scored tokens:** the eval stream is 512 × 128 = 65,536 tokens;
   scored positions are 65,024 (127 per chunk, standard shift). The
   protocol's "65,536 tokens" describes the stream consumed.
5. **Master steps:** 585, not the protocol's ≈586 estimate
   (195 steps/epoch × 3; 3,120 of 3,125 chunks per epoch). Arithmetic,
   not a change.
6. **Pre-results repairs (before any scored run of the affected
   objects):** an FP16 attention-mask dtype bug that crashed the first
   evaluation attempt on the FP16 row (FP32 context row had completed;
   no variant result existed); tied embedding/head double-key handling
   in the variant artifacts. Both fixed in code, named here.
7. **QAT data order:** TERNARY-QAT fine-tuned on the first 150 batches
   of the master's epoch-0 order (same seed stream), per protocol.

## 7. What this licenses anyone to say

Per charter §6 and K4/K5 — the sayable shape, and no larger:

> "In a pre-registered software model — labeled a model — ternary-
> weight inference used 58% less modeled energy per token than the
> best binary low-precision baseline at matched accuracy; the same
> decomposition showed the advantage was entirely explained by the
> reduced bit-width, with nothing left over attributable to the
> ternary radix itself. The ternary framing of this direction is
> therefore killed, in writing, by the program that proposed it."

Not sayable: any hardware energy saving; any percentage applied to a
facility; any gallon figure; "we can save the data centers." The chain
from modeled joules to water was never built here — and after this
landing, the radix link of it is closed.

**Files:** protocol + code + raw results in
`~/workspace/trit-experiment/` (`PROTOCOL.md`; `results/accuracy.json`,
`census.json`, `timing.json`, `verdict.json`; logs alongside). All
dossier numbers match those files.

*End of dossier. The kill is the deliverable: a clean negative,
pre-registered, at proof speed — the difference between a program
that formulates and one that advertises.*
