# 0010 — Consolidation: dimensional collapse, the Fourier-folded ribbon, and the Remember-vs-Compute topology law

**Status:** CLOSED on the measured questions (Path B″ topology, FFT fork, Path C recurrent control);
theory synthesis OPEN (hypothesis register at end).
**Date:** 2026-06-21.
**Depends on:** 0007 (Cantor inverse-system law), 0008 (Path A q-law calibration),
0009 (Path B/B′ — dimensional collapse SUPPORTED, Cantor/DSI REFUTED).
**Corrects narrative:** the "flat-torus (b₁=2)" grokking claim in
`docs/SGC_CANONICAL_GROKKING_THEORY.md` is shown below to be a necessity-argument LABEL,
never a measurement.

## The question

0009 left the grokked modular-addition hidden manifold as a SMOOTH low-dimensional object
(`d_corr ≈ 1.6–1.7`), conjectured to be "a few superimposed Fourier-feature circles." Three
things were still open; this entry closes them, plus a new "why" via a control experiment:

1. **Topology (Path B″).** Is that smooth object a loop/torus (`b₁≥1`) or contractible
   (`b₁=0`)? Direct persistent-homology measurement — never performed in February.
2. **Function (FFT fork).** Fourier features (Nanda) or a non-Fourier algebraic code?
3. **Reconciliation.** How does this square with the February "flat torus" / Betti-autopsy /
   cybernetic-grokking narrative?
4. **Why (Path C).** If the feedforward geometry is contractible, what FORCES topology into a
   representation when it *does* appear?

## Forensic reconciliation with February (ground-truth audit)

Pulled and read the primary Feb artifacts. The apparent conflict with "we proved a flat torus
in February" is ILLUSORY — February never measured `b₁` on neural activations:

- **`docs/SGC_CANONICAL_GROKKING_THEORY.md:18`** lists the evidence for "Flat Torus" as
  *"modular arithmetic structure necessitates toroidal connectivity"* — a NECESSITY ARGUMENT.
  Every February MEASURED quantity is real (Gauss `K≈10⁻⁸`, ridge ratio 0.6→44, functional-
  defect collapse) but none is a Betti number.
- **`experimental_record/functional_blanket_breakthrough.md:151`** concludes the OPPOSITE of a
  geometric torus: *"the Markov blanket is FUNCTIONAL … not GEOMETRIC."* The FFT below confirms
  that functional reading.
- **`experimental_record/betti_autopsy.py:29-68`** computes `b₁ = E−V+b₀` on **ARC sheaf-
  Laplacian operators**, NOT neural activations (verdict `:345-350`: "all operators b₁=0").
  The `34/34 → 4/4 b₁` story is about ARC stalk graphs — a different object and system.
- **L1 "topological poison"** is a property of ARC stalk-graph pruning
  (`demos/spiking_sheaf_engine.py:861`); the modular MLP uses decoupled **L2** weight decay
  (`experiments/representation_manifold_grokking.py`), no graph. The category was conflated.
- The **<100-epoch grokking detector** (`experimental_record/functional_grokking_detector.py:292-310`)
  gates on functional defect + class separation — **no `b₁`, no topology** — fully consistent
  with `b₁=0`.

Net: February's measured results stand; the "neural flat-torus (b₁=2)" was an unmeasured label.
This entry supplies the first direct measurement.

## MEASURED RESULTS

### Path B″ — persistent homology of the grokked FEEDFORWARD MLP → b₁=0 everywhere

Script `experiments/persistent_homology_grokking.py` (gudhi sparse Vietoris–Rips; ripser blocked
by a numpy-2 / sklearn ABI break). **Calibration GATE passed at the neural ambient dim `R^128`**
(0008/0009 discipline applied recursively): circle→b₁=1, fuzzy circle (noise 0.06)→b₁=1,
flat torus→(b₁=2,b₂=1), sphere→(0,1), Gaussian→(0,0); H1 null floor → **`τ₁*=0.394`** (1.5×),
`τ₂*≈0.19–0.22` (2.0×). The fuzzy-circle false-negative control proves the probe still finds a
loop buried under substantial high-d noise — so a neural `b₁=0` is a genuine ABSENCE.

| layer (seed 42, post-grok) | prior | measured |
|---|---|---|
| `embed_a(a)` (97) | circle b₁=1 | **b₁=0** |
| `embed_b(b)` (97) | circle b₁=1 | **b₁=0** |
| joint `[eₐ⊕e_b]` (grid) | TORUS b₁=2,b₂=1 | **b₁=0** |
| hidden class-means (97) | circle b₁=1 | **b₁=0** |
| hidden full (`d_corr` cloud) | b₁=1 + scatter | **b₁=0** |

Every neural layer is topologically TRIVIAL: all top H1 persistences fall below `τ₁*`. The grokked
manifold is a contractible blob — not a torus, not a circle.

### FFT fork — the Fourier-FOLDED ribbon (function ≠ topology)

Script `experiments/fft_classmeans_grokking.py`. FFT of hidden class-means `C[s]`,
`s=(a+b) mod 97`, bracketed by white-noise (PR 47.7/48, top5 12.2%) and clean-3-tone
(PR 3.0/48, top5 100%) baselines computed by the identical pipeline:

- **OBSERVED: PR = 4.0/48, top5 = 99.2%, dominant k ∈ {26, 25, 15, 8}** (47/43/23/15 of the
  128 hidden neurons tuned to those four frequencies).

⇒ The grokked solution IS Fourier — textbook Nanda key-frequency features — reconciling the
mechanistic-interpretability literature. But the four MEDIUM frequencies wind the (a+b)-curve
~25× and fold it flat, so the topological loop washes out below `τ₁*`. **Functionally Fourier;
geometrically/topologically contractible.** This is the precise resolution of 0009's "a few
superimposed Fourier circles."

### Path C — Remember-vs-Compute control: RECURRENCE ⇒ b₁≥1

Pre-registered prediction (stated before running; the reader is pre-calibrated, so the readout
cannot be fudged): *a network that must REMEMBER a cyclic state, rather than COMPUTE it in one
pass, is forced to carry the stimulus topology* — numeric prediction **`b₁≥1`** (vs feedforward
`b₁=0`). Script `experiments/recurrent_modular_grokking.py`:
a GRU path-integrator tracking `s_t=(s_{t-1}+v_t) mod 97`, `v∈{-1,0,+1}`, uniform random start
(absolute-set token at t=0 for full ring coverage), `hidden_dim=128`, gradient-clipped, read by
the **identical** calibrated reader that gave the feedforward `b₁=0`.

| config | held-out acc | b₁ class-means (top H1 pers.) | b₁ full cloud | dominant Fourier |
|---|---|---|---|---|
| feedforward MLP (baseline) | grok ~1.0 | **0** (sub-`τ₁*`) | **0** | k = 8,15,25,26 |
| recurrent, wd=0.5 (matched) | 0.4754 | **1** (1.286) | **1** (0.678) | k=1 (53.7%) |
| recurrent, wd=1e-3 | 0.9999 | **1** (0.841) | **1** (0.456) | k=1,2,3 |

**`b₁` flips 0→≥1 with recurrence alone** — same task family, same `hidden_dim=128`, same reader,
across the `wd` range, and even at 47% accuracy (so the loop is the computational SCAFFOLD, not
an overfit artifact). At seed 42 the code is a clean SINGLE ring (one dominant H1 bar; fundamental
k=1 + harmonics shaping a localized bump), top persistence on par with the textbook circle
calibration cloud (1.32). The EXACT Betti count is seed-dependent (see the multi-seed replication
addendum below); `b₁≥1` with one dominant essential loop is the robust, reproducible signature.
Toy analogue of the head-direction ring attractor (Kim et al., Science 2017) and the grid-cell
torus (Gardner et al., Nature 2022).

## SYNTHESIS — the Remember-vs-Compute topology law (the MEASURED part)

Topology is forced into a representation only when that representation must be DYNAMICALLY
MAINTAINED — *not* by the task's periodicity per se:

- **Discrete recurrence (Schnakenberg 1976 / discrete Hodge).** A nonzero stationary current is
  divergence-free (Kirchhoff) and lives in the graph cycle space, of dimension `= b₁`. On a tree
  (`b₁=0`) a self-sustaining NESS is impossible. This is the rigorous grounding for the ARC-sheaf
  `b₁≥1` requirement. *(There is NO `DiscreteFluidDynamics` "proof" in-repo — that artifact was
  confabulated; the literature result above is the real basis.)*
- **Continuous recurrence (attractor topology).** Holding a periodic variable requires an
  attractor manifold homeomorphic to the stimulus → ring/torus (`b₁≥1`). Measured in grid cells
  and HD cells; reproduced here in Path C.
- **Feedforward (compute).** Under neither obligation; minimizes loss+`wd` by folding periodicity
  flat → `b₁=0` (Path B″).

⇒ Same modular task, OPPOSITE topology, decided by remember-vs-compute. February's "torus
necessity" intuition was pointing at the RECURRENT/attractor truth; the feedforward MLP simply
is not in that regime.

## HYPOTHESIS REGISTER — NOT established; do not cite as measured

- **[H-a] Remember-vs-Compute as a GENERAL architectural law** (beyond `Z_p` integration).
  Support: 1 toy (Path C) + 2 neuroscience datasets. Needs ≥2 more stimulus topologies — a
  2-torus integrator (predict `b₁=2, b₂=1`) and a spherical variable (predict `b₂=1`).
- **[H-b] Architecture taxonomy** (sheaf = fixed topology, transformer = fixed coordinates,
  diffusion/EBM = fixed dynamics, spiking/predictive-coding = fixed locality/error-gating).
  Status: organizing METAPHOR; each cell needs a measured discriminator before it is a claim.
- **[H-c] Thermodynamics of prediction** (Still, Sivak, Bell & Crooks, PRL 2012): predictive code
  ≈ low dissipation, memorization ≈ dissipative. Status: literature-grounded analogy; SGC has not
  measured dissipation-vs-predictivity directly.
- **[H-d] "db₁/dt ≥ 0 Conservation Law of Thought" / "Yamabe-neck cascade."** Status: NOT found in
  code; mis-named (monotonicity ≠ conservation); UNVERIFIED narrative.
- **[H-e] Cybernetic controller restores a neural torus.** Status: PARTIALLY addressed — it is
  RECURRENCE, not the controller, that yields the ring; the controller's role is untested.

## Falsifiers (for the MEASURED law)

- A FEEDFORWARD modular net that reads `b₁≥1` on the SAME calibrated reader ⟹ topology is not
  exclusive to recurrence.
- A RECURRENT integrator of a periodic variable that reads `b₁=0` at high accuracy ⟹ Principle B
  is wrong.
- A 2-torus / spherical integrator that does NOT produce the predicted `b₁/b₂` ⟹ the attractor-
  topology law is wrong.

## Discipline & honest scope

- Scripts: `experiments/persistent_homology_grokking.py`, `experiments/fft_classmeans_grokking.py`,
  `experiments/recurrent_modular_grokking.py`. Caches in `experiments/logs/ph_grok/`.
- Calibration-gate-first; every top persistence printed (signal-vs-floor auditable); the barcode
  reader is IDENTICAL across feedforward and recurrent clouds.
- The topological probe CANNOT distinguish a folded torus from a folded circle from a blob once
  folding pushes persistence below `τ₁*` — all read `b₁=0`. "Fourier-folded ribbon" is therefore a
  FUNCTIONAL (FFT) + GEOMETRIC (flat, `d_corr≈1.6–1.7`) statement, with topology = trivial.
- The recurrent task is path-integration — related to, but not identical with, the feedforward
  `a+b` map. The control isolates recurrence, not the exact same target function.
- Path B″ feedforward (`b₁=0`) is still single-seed (42); multi-seed feedforward replication
  remains REQUIRED before a publication-grade contrast. Path C recurrent IS now replicated
  (seeds 42–45; addendum below).

## Results (multi-seed replication, Path C — seeds 42–45, wd=1e-3 — 2026-06-21)  [addendum]

Replicated the recurrent integrator across seeds 42–45 (clean config `wd=1e-3, L=32`, held-out
acc 0.98–1.00) and re-read all four cached `H[s]` clouds in ONE calibrated pass
(`experiments/recurrent_replication_summary.py`, identical `τ₁*=0.394`):

| seed | held-out acc | b₁ (class-means) | top-4 H1 persistences (gate 0.394) |
|---|---|---|---|
| 42 | 1.00 | **1** | 0.841 / 0.348 / 0.343 / 0.084 |
| 43 | 0.98 | **2** | 0.892 / 0.645 / 0.245 / 0.134 |
| 44 | 0.99 | **2** | 0.924 / 0.533 / 0.241 / 0.093 |
| 45 | 1.00 | **4** | 0.993 / 0.484 / 0.424 / 0.417 |

**CONFIRMED (pre-registered claim): `b₁≥1` in 4/4 seeds** (vs feedforward `b₁=0`). Every seed has
ONE dominant loop (top persistence 0.84–0.99, on par with the circle calibration cloud 1.32) —
the fundamental ring is the robust, reproducible signature, and the remember-vs-compute CONTRAST
is unaffected.

**REFINED (over-strong part retracted): the EXACT count is NOT robustly 1 — it is {1,2,2,4}.** The
ring carries higher Fourier harmonics (k2,k3; the FFT k1 share is 31–54% across seeds), which make
the closed class-mean curve MULTI-LOBED; finite-sample Vietoris–Rips then registers the
sub-dominant lobes as extra H1 bars (persistence 0.42–0.65, all below the dominant bar). Partly a
thin-curve artifact: seed 45's FULL cloud (with within-state scatter) drops to `b₁=2` as the
scatter thickens the curve and washes the smallest lobes out.

**Methodological lesson (logged): Rips H1 bar-counting OVER-COUNTS loops on a thin, harmonic-rich
closed curve.** A single wiggly closed curve (topologically `S¹`, `b₁=1`) can present 2–4 persistent
bars. Deciding "one multi-lobed ring vs genuinely k independent cycles" requires circular-coordinate
/ winding analysis (de Silva–Vejdemo-Johansson persistent cohomology), NOT Betti counting. The
seed-42 `b₁=1` was the low-harmonic case, not the generic one. Only the "exactly one ring"
sharpening is downgraded to OPEN.

**Next:** (i) circular-coordinate winding number on the dominant cycle to test the single-`S¹`
hypothesis; (ii) feedforward `b₁=0` replication at seeds 43–45 to complete the contrast;
(iii) 2-torus integrator ([H-a], predict `b₁=2, b₂=1`).

## Results (Leg 1a — circular-coordinate resolution of {1,2,2,4} — 2026-06-21)  [addendum]

Built `experiments/circular_coordinate_probe.py`: Fourier-deconvolve each recurrent `H[s]`
(an `s`-parametrised closed curve), read `b₁` of progressive reconstructions with the IDENTICAL
calibrated reader, and measure the dominant-mode-plane winding number (the top-2 PCA plane mixes
comparable frequencies and gave false zeros, so it is NOT used).

| seed | dominant carrier `k*` | winding(k* plane) | isolated-`k*` `b₁` | fundamental k=1 `b₁` (pers.) | full-cloud `b₁` |
|---|---|---|---|---|---|
| 42 | 1 | −1 | 1 | 1 (1.56) | 1 |
| 43 | 1 | −1 | 1 | 1 (1.46) | 2 |
| 44 | 1 | −1 | 1 | 1 (1.43) | 2 |
| 45 | **3** | **−3** | 1 | 1 (1.67) | 4 |

**RESOLVED — it is ONE circular carrier per seed, NOT k independent cycles.** In 4/4 seeds the
*isolated* dominant Fourier mode is a single circle (`b₁=1`) and the k=1 fundamental is a clean
`S¹` with persistence **1.43–1.67** (≥ the textbook circle's 1.32). Progressive reconstruction
reproduces the full counts: satellite bars appear ONLY as higher harmonics (k≥3) are added
(seed 45: `b₁` 1→1→2→2 as k≤1→2→3→4). So the full-cloud `b₁∈{1,2,2,4}` is **harmonic-lobe
Vietoris–Rips OVER-COUNTING of a single circular carrier** — a measurement artifact, not topology.

**New finding:** the carrier *frequency* is seed-dependent — seeds 42–44 ride k=1, **seed 45 rides
k=3** (winding −3). Since `gcd(k,97)=1`, any harmonic uniquely labels `Z₉₇`, so k=3 is a valid
circular code (and the most over-counting-prone, hence its full `b₁=4`).

**Net:** the seed-42 "single ring" *does* generalise — as **one `S¹` carrier per seed** — once
Rips over-counting is removed by deconvolution. The remember-vs-compute law stands sharpened:
**recurrent = a single circular carrier (`b₁=1` fundamental, winding ±k*); feedforward = `b₁=0`.**
The exact Rips Betti count is a spectral artifact, not a topological invariant. (Tool reused by
the Leg-2 transformer probe.)

## Results (Leg 2 — DRIVE THE WEDGE: transformer — seed 42 — 2026-06-21)  [addendum]

Built `experiments/transformer_modular_grokking.py`: 1-layer transformer (`d_model=128`, 4 heads,
`d_mlp=512`), tokens `[a,b,=] → (a+b) mod 97`, full-batch AdamW `wd=1.0`. **Grokked at step ≈7200**
(train→1.0 by step 400; test 0.01→**1.000**). Probed with the IDENTICAL calibrated reader + the
Leg-1a circular-coordinate tool. **The pre-registered predictions were largely FALSIFIED — and
that falsification is the finding.**

| cloud | full-cloud `b₁` | dominant carrier `k*` | k≤4 recon `b₁` | FFT key frequencies |
|---|---|---|---|---|
| token embedding `W_E` | **0** (pers 0.13) | 31 (winds 31×) | 1 | k=31,6,22,32,8  (PR 7.3, top5 80%) |
| residual @ `=` | **0** (pers 0.20) | 31 | 1 | k=31,6,22,32,8  (PR 4.7, top5 98%) |
| residual full (N=9409) | **0** | — | — | — |
| MLP neurons | folded | 31 | — | k=31,6,22,32,8  (PR 4.8, top5 95%) |

- **P1 (embedding `b₁≥1`, the "clock") — FALSIFIED** at full resolution: the FULL embedding reads
  `b₁=0` (top H1 persistence 0.13 ≪ `τ₁*=0.394`). The clock survives ONLY as 2-D key-frequency
  projections — the *isolated* k=31 mode is a clean circle (`b₁=1`) and the k≤4 reconstruction is
  `b₁=1`, but the full object folds.
- **P2 ("feedforward→`b₁=0`" is MLP-specific) — REFUTED:** the transformer FOLDS to `b₁=0` exactly
  like the MLP. `feedforward → b₁=0` is GENERAL across both architectures measured.
- **P3 (residual) — `b₁=0`** (folded), consistent with the circle being an *encoding*, not a
  maintained state.

**Reconciles Nanda AND relocates the real variable to CARRIER FREQUENCY (not architecture class).**
The transformer's clock (Nanda 2023) is real but is a handful of KEY FREQUENCIES `{6,8,22,31,32}` —
all medium/high. Each key frequency is individually a circle (isolated-`k*` `b₁=1`), but the
superposition of *high*-frequency carriers winds ~31× and folds the full representation flat
(`b₁=0`), precisely as the MLP's k=8–26 keys did. All three architectures on one axis:

```
  recurrent integrator   carrier k* = 1 (1–3)   LOW  -> open loop     -> b1 >= 1
  feedforward MLP        keys k = 8,15,25,26     HIGH -> folded ribbon -> b1 = 0
  transformer            keys k = 6,8,22,31,32   HIGH -> folded ribbon -> b1 = 0
```

**REFINED WORKING LAW (emerging; supersedes the naive remember/compute→topology framing in the
body above):** representational topology is set by the **carrier frequency**, which is set by the
**smoothness constraint** of the computation. A RECURRENT integrator must map `s → s±1` by a LOCAL
update, so neighbouring states must be adjacent in representation → LOW spatial frequency (k=1) → a
topologically OPEN loop (`b₁≥1`). FEEDFORWARD computation of `a+b` has NO smoothness constraint and
is free to use HIGH-frequency trig-identity features (parameter-efficient) that wind many times and
fold flat (`b₁=0`). "Remember vs compute" was the right *intuition*; the *mechanism* is carrier
frequency.

**HONEST CAVEATS:** single transformer seed (42) — **replication at seeds 43–45 is underway before
this law is treated as established**. The carrier-frequency law is inferred from 1 recurrent family
+ 2 feedforward architectures; the CAUSAL claim ("recurrence *forces* low frequency") is motivated
but not yet tested by intervention (that is exactly the Leg-3 order-parameter / ablation frontier).
My P1/P2 being wrong is logged, not hidden — the wedge confirmed the `b₁=0` side and moved the
explanatory burden onto frequency.

## Results (Multi-seed replication: feedforward + transformer — seeds 42–45 — 2026-06-21)  [addendum]

Two clean multi-seed passes, identical calibrated reader (`τ₁*=0.394`); logs at
`experiments/logs/ph_grok/{ff_multiseed,transformer_replication}.txt`.

**FEEDFORWARD MLP — `b₁=0` REPLICATES CLEANLY (4/4 seeds).** Every layer (`embed_a`, `embed_b`,
joint, hidden class-means, hidden full) at every seed 42–45 and every grok stage (pre/at/post)
reads `b₁=0`, top H1 persistence **0.15–0.33** — all well below `τ₁*`. The "feedforward→`b₁=0`"
null is solid and reproducible. (Stray `b₂=1` readings are H2 noise-floor artifacts on the
`N=97`/`N=9409` clouds — a circle cannot have `b₂=1` — not geometry.)

**TRANSFORMER — the carrier-frequency claim REPLICATES; my seed-42 "clean `b₁=0`" does NOT.**

| seed | embed dom `k*` | embed full `b₁` (topH1) | resid dom `k*` | resid full `b₁` (topH1) |
|---|---|---|---|---|
| 42 | 31 | 0 (0.13) | 31 | 0 (0.20) |
| 43 | 38 | 0 (0.25) | 38 | 1 (0.40) |
| 44 | 42 | 1 (0.51) | 42 | 2 (0.46) |
| 45 | 21 | 0 (0.35) | 21 | 1 (0.82) |

- **ROBUST (4/4):** the dominant carrier is a HIGH key frequency (`k*`=21–42) and the low-freq
  (k≤4) reconstruction is always circular. Transformers ride HIGH carriers like the MLP (k=8–26)
  and UNLIKE the recurrent integrator (k=1–3). The **low-vs-high carrier axis is the crisp,
  reproducible architectural signature.**
- **CORRECTED:** the transformer does NOT cleanly fold to `b₁=0`. Full-cloud `b₁` is BORDERLINE
  and seed/cloud-dependent — embed `{0,0,1,0}`, resid `{0,1,2,1}` — with top persistences
  STRADDLING `τ₁*` (0.13–0.82, single-read, no bootstrap). The transformer is **INTERMEDIATE**
  between the cleanly folded MLP (`b₁=0`, ≤0.33) and the open recurrent ring (`b₁≥1`, 0.84–0.99),
  not a clean copy of either. My Leg-2 "folds to `b₁=0` exactly like the MLP" was a single-seed
  (42) artifact.

**3-architecture summary (each 4 seeds, identical reader):**

```
  recurrent integrator   carrier k=1-3    topH1 0.84-0.99   b1>=1   SOLID open ring
  feedforward MLP        carrier k=8-26   topH1 0.15-0.33   b1=0    SOLID folded
  transformer            carrier k=21-42  topH1 0.13-0.82   b1=0-2  BORDERLINE intermediate
```

**REFINED LAW (honest, multi-seed):**
- The **carrier frequency** is the robust architectural invariant: maintained-state recurrence
  rides LOW (k=1–3); feedforward computation (MLP *and* transformer) rides HIGH (k=8–42).
- Full-cloud **topology is downstream and threshold-sensitive**: only the low-frequency recurrent
  ring is solidly OPEN (`b₁≥1`); the high-frequency MLP is solidly FOLDED (`b₁=0`); the
  high-frequency transformer is BORDERLINE (persistences near `τ₁*`). So "high frequency→`b₁=0`"
  is clean for the MLP but only PARTIAL for the transformer — attention evidently preserves more
  circular structure than the MLP's aggressive joint folding.

**HONEST CAVEAT:** because the transformer's loop persistences sit near `τ₁*`, the topological
reader cannot crisply classify it — the FFT carrier-frequency signature is the reliable
discriminator. The "remember vs compute" intuition survives as *maintained-state recurrence forces
a LOW-frequency (smooth/local) circular code*; the clean `b₁` dichotomy is specific to the
recurrent-vs-MLP poles, with the transformer genuinely in between.

## Results (Leg 3: the α-gate recurrent phase transition — L=12 & L=24, seed 42 — 2026-06-22)  [addendum]

Sweep the recurrence gate α in `hₜ = cell(xₜ, α·hₜ₋₁)` from 0 (feedforward, no memory) to 1
(full recurrence) on modular path-integration; watch the carrier frequency and `b₁` turn on.
Motivated by the Bateman–Turok **ghost-parity** analogy (Curt Jaimungal TOE podcast; arXiv
`2408.04089` *Making sense of ghosts* + the new *Escape from Ostrogradsky via Hidden Ghost
Parity*). Script `experiments/recurrent_phase_transition.py`; logs `phase_transition_L{12,24}_seed42.txt`.

**PHYSICS FRAMING (honest, stated before crediting any analogy).** The Bateman–Turok ghost-parity
/ Krein-space resolution of the Ostrogradsky instability in quadratic gravity is *real, premiering
physics* (Turok states the caveats himself: "halfway there… may or may not apply to the full thing…
a limit, not the real world"). But the proposed map (high-freq mode = negative-norm *ghost*;
recurrence = ghost-parity *projection*) is a **generative metaphor, not a derivation**:
- Neural activations live in a **positive-definite** Euclidean space — there is **no indefinite
  (Krein) metric**, hence no negative-norm sector, so nothing literally *is* a ghost.
- Ostrogradsky concerns higher **time**-derivatives; recurrence `hₜ=f(hₜ₋₁)` is **first-order** in
  time → no Ostrogradsky ghost in the technical sense.
- There is no involution / S-matrix / commutation requirement in a GRU.

The metaphor earns weight only via a **differential prediction** the plain dynamical view lacks —
a **discontinuous** snap vs a smooth crossover. Pre-registered three rivals (`H_snap` discontinuous;
`H_smooth` crossover; `H_cap` memory-horizon) + Devin's own (incoherent blob below onset).

**RESULT — TWO DECOUPLED TRANSITIONS:**

```
          alpha=0 (no memory)         alpha=0.1 (first nonzero)     high alpha
  L=12    acc .01  k*36 pwr10% b1=0   acc .98  k*1 pwr25% b1=3      acc 1.0  k* low  b1>=1
  L=24    acc .01  k*32 pwr 6% b1=0   acc .48  k*2 pwr43% b1=3      acc .99  k* low  b1>=1
```

1. **TOPOLOGICAL SWITCH — sharp & LENGTH-INVARIANT.** At *both* lengths, α=0 is an **incoherent
   blob** (`b₁=0`, dominant-mode power 6–10%, topH1 0.21–0.24 < `τ₁*`); the *first* nonzero α (0.1)
   already gives a coherent low-frequency **ring** (`b₁≥1`, isolated-carrier `b₁=1`, `k*`=1–2,
   power 25–43%, topH1 0.69–1.15 ≫ `τ₁*`). The blob→ring flip, the `k*` high→fundamental snap, the
   coherence jump, and the `b₁` 0→1 jump all happen in **one α-step** and do **not** move with L.
   → **`H_smooth` (crossover) FALSIFIED**; the sharpness + coupled snap the ghost-parity analogy
   called for is **confirmed**.
2. **COMPETENCE THRESHOLD — capacity-limited (moves with L).** α=0.1 → acc 0.975 (L=12) vs 0.478
   (L=24); onset α* (acc≥0.5) moves 0.1→0.2. Longer integration needs stronger recurrence to be
   *accurate*. → **`H_cap` CONFIRMED for accuracy.**
3. **THE RING IS THE SCAFFOLD, not the consequence of competence.** At L=24, α=0.1 the net is only
   **48% accurate** yet carries the **strongest ring of the whole sweep** (topH1=1.151). Topology
   forms as soon as recurrence exists, *before* accuracy; accuracy then fills in as capacity allows.
   (Longer L forces a *cleaner* ring: topH1 ~1.0 at L=24 vs ~0.6 at L=12.)
4. **NO COHERENT GHOST SECTOR.** Sub-onset dominant-mode power is 6–10% — an unstructured blob, not
   a coherent high-frequency carrier. → **`H_snap`'s specific mechanism** (coherent ghosts projected
   out by a parity involution) **FALSIFIED**: there is nothing coherent to project. Devin's
   pre-registered "incoherent blob below onset" **confirmed** at both L.

**REFINED LAW (Leg 3): recurrence is a SWITCH, not a projection.** Any recurrent coupling instantly
selects the smooth `k=1/2` fundamental and opens the `b₁≥1` ring (length-invariant, sharp); task
*accuracy* is a separate, capacity-limited (memory-horizon ~`α^L`) variable. The
"feedforward→temporal-agent phase transition" framing **conflated** these two; the data **separates**
them. The ghost-parity metaphor scores a real **hit on the phenomenology** (first-order sharpness,
coupled frequency-snap/topology-jump) but its **mechanism is not instantiated** — the simpler
account ("recurrence selects the smooth fundamental; accuracy is capacity-limited") fits all data
without an indefinite metric.

**CAVEATS:** single seed (42), two lengths (12, 24); the α=0→0.1 interval is unresolved (the switch
may have sub-0.1 structure) — a finer near-zero grid and seeds 43–45 are the immediate next steps.
The `b₁` exact count (1–4) is the same harmonic-lobe Rips over-count from Leg 1a; isolated-carrier
`b₁=1` and winding ~−1…−2 confirm **one** circular carrier throughout.

## Results (Leg 3b: fine sub-0.1 grid — L=12, seed 42 — 2026-06-22)  [addendum]

Zoomed the α sweep into `[0, 0.1]` at 0.01 resolution to resolve the switch. Log
`phase_transition_L12_seed42_amax0.1.txt`.

```
   alpha:  0.00  0.01  0.02  0.03  0.04  0.05  0.06  0.07  0.08  0.09  0.10
   acc:    .01   .15   .16   .21   .31   .42   .76   .89   .95   .97   .98
   k*:     36    1     1     1     1     1     2     1     1     1     1
   b1:     0     1     1     2     1     1     1     1     2     2     3
   topH1:  .21   .46   .53   .69   .88   .91   .70   .70   .70   .64   .69
   k*pwr%: 10    46    52    53    54    47    29    27    27    23    25
```

**VERDICT (seed 42 @ 0.01-resolution) — the "`α=0` singularity" reading below is CORRECTED by Leg-3c:
there is a FINITE, seed-invariant knee at `α_c≈0.01`, not a step at the pure singularity.**
1. `b₁` jumps 0→1 and `k*` snaps 36→1 between α=0.00 and α=0.01 (smallest step resolved *here*). For
   *every* α≥0.01 the ring is on (`b₁≥1`, `k*`=1–2, topH1 > `τ₁*`). **Seed 42 was not probed below
   0.01**; the decade-finer Leg-3c log-grid (below) finds α=0.001 is still a BLOB for seeds 43–45, so
   the threshold is FINITE (`α_c≈0.01`), not at the singularity.
2. **The ring forms at 15% accuracy** (α=0.01: `b₁=1`, coherence 46%, topH1=0.46, acc=0.15) —
   definitive confirmation that the ring is the coordinate **scaffold**, laid down before the net
   can integrate.
3. **Two decoupled order parameters on one axis:** `b₁` (topological, BINARY) is a discontinuous
   step at α→0⁺; accuracy (functional, CONTINUOUS) rises smoothly, steepest at α=0.05→0.06 (+0.34),
   onset α*(acc≥0.5)=0.06 — far from the topology onset (0.01).
4. **COUNTERINTUITIVE — the ring is PUREST in the LOW-accuracy regime.** Coherence peaks 54% and
   persistence peaks 0.91 at α=0.04–0.05 (~30–42% acc), then both DROP (coherence ~25%, topH1
   ~0.68) as accuracy fills in. The net first lays down an almost-pure geometric ring, then
   *decorates* it with readout machinery for accurate computation, which adds variance and slightly
   degrades the pure-ring signal. **The cleanest scaffold precedes competence.**

**MECHANISTIC NOTE (revised by Leg-3c):** I initially argued the GRU *amplifies* any nonzero `α·h`
so the switch is at 0⁺. The log-grid refutes this: at α=0.001 the GRU does **not** bootstrap memory
(stays a blob), so there is a real minimum coupling `α_c≈0.01` below which training cannot grow the
recurrent weights enough. The first-order step is real, sharp, and seed-invariant — but at a small
**finite** `α_c`, not the singularity.

**CAVEAT (superseded):** the "step at the singularity, bounded to (0, 0.01]" claim was a single-seed
(42) extrapolation; see Leg-3c for the corrected finite-threshold + two-stage result.

## Results (Leg 3c: log-grid hardening + multi-seed — L=12, seeds 43/44/45 — 2026-06-22)  [addendum]

To decide SINGULARITY vs FINITE threshold, swept a decade-finer log grid α ∈ {0, 0.001, 0.002,
0.005, 0.01} across three NEW seeds. Log `phase_hardening_loggrid_L12_seeds43-45.txt`.

```
 seed  a=0.001       a=0.002        a=0.005             a=0.010
  43   blob k*32 b0  k*2  b0(.17)   k*2  77%coh b0(.19)  RING b1=2 (.75)
  44   blob k*34 b0  k*3  b0(.22)   k*1  54%coh b0(.13)  RING b1=2 (.53)
  45   blob k*43 b0  k*3  b0(.16)   k*3  54%coh b0(.26)  RING b1=3 (.90)
```

**VERDICT — corrects Leg-3b; the step is real but at a FINITE, seed-invariant `α_c≈0.01`:**
1. **Finite threshold, seed-invariant.** The ring certifies (`b₁≥1`, topH1 > `τ₁*`) at `α_c=0.01` for
   **all three** seeds; α=0.001 is firmly a BLOB (`k*`=32–43, coherence <8%, `b₁=0`) for all. The
   switch is **not** at the `α=0` singularity — there is a real knee, bounded to (0.005, 0.01], and it
   is identical across seeds 43/44/45 (consistent with 42). The first-order step is real and
   **universal**, just at a small finite coupling.
2. **Two-stage structure: carrier-snap PRECEDES topological certification.** At α=0.005 the carrier
   has already snapped to LOW `k` (1–3) and is HIGHLY coherent (54–77%), yet `b₁=0` (topH1 0.13–0.26
   < gate): a coherent low-frequency carrier exists *before* the persistent loop certifies. The loop
   certifies only at α=0.01 (topH1 jumps to 0.53–0.90). **Frequency-order and topological-order are
   themselves decoupled near threshold** — the smooth-carrier collapse is the leading edge
   (α≈0.002–0.005), the certified `b₁` ring follows (`α_c≈0.01`).
3. This **sharpens** the carrier-frequency law: below α_c, an incoherent high-`k` blob; a thin window
   (≈0.002–0.005) of coherent-but-uncertified low-`k` carrier; then the certified ring at α_c≈0.01.

**METHODOLOGY LESSON:** hardening before sailing was correct — the log-grid overturned a single-seed
over-extrapolation. The corrected claim (sharp, seed-invariant first-order step at finite `α_c≈0.01`
with a frequency-then-topology two-stage onset) is stronger: multi-seed and mechanistically richer.

## Results (Waypoint B: the 2-torus integrator — p=17, L=20, seed 42 — 2026-06-22)  [addendum]

Scaled the recurrent integrator to TWO independent running sums on `Z_17` (two action channels, two
readout heads). Net groks fast (both sums 100% test acc by iter 1000; full 289/289 grid covered).
Script `torus_integrator_grokking.py`; logs `torus_integrator_p17_seed42.txt` (subsample) +
`torus_integrator_p17_seed42_fullskeleton.txt` (full). Since competence forces `b₁≥2`, the entire
test is `b₂`: genuine flat torus T²=S¹×S¹ (`b₁=2, b₂=1`, a 2-void) vs degenerate wedge/figure-8
(`b₁=2, b₂=0`).

**RESULT — GENUINE 2-TORUS (with a sharp methodological lesson on H₂):**

```
  protocol              b1   b2   top-5 H2                         H2 gap
  full skeleton (289)    2    1   [0.582 0.069 0.066 0.065 0.065]  8.4x   <- decisive 2-void
  calibrated subsample   2    0   [0.132 0.120 0.108 0.104 0.091]  1.1x   <- FALSE NEGATIVE
```

1. **Full skeleton certifies the torus.** `b₁=2` (top H1 [0.776, 0.711] ≫ `τ₁*`, then 3.7× drop to
   0.19) and `b₂=1` with a **single isolated 2-void bar 0.582, gap 8.4×** — *stronger* than the
   synthetic calibration torus (0.286, gap 2.9×). The learned representation is an exceptionally
   clean torus.
2. **Footing-independent corroboration (no Rips needed).** 2D Fourier carriers sit ENTIRELY on the
   axes — (0,±1) and (±1,0) at ~20–22% each = **83% axis-power, 0% cross-power** — so the code is
   `f(s₁) ⊕ g(s₂)`, two circular variables in ORTHOGONAL subspaces; each marginal is a clean ring
   (`b₁=1`). A direct sum of two non-intersecting circles **is** S¹×S¹ (b₂=1) by construction; a
   wedge would require them to share a point, which orthogonality forbids. This alone implies a torus.
3. **METHODOLOGY (own correction):** the lab's original "full p² skeleton, no subsampling" instinct
   was **right**; my "correction" to the calibrated 100-pt subsample produced a **false negative**
   (`b₂=0`, all H2 bars ~0.1, gap 1.1×). At small dense N the full skeleton resolves the void; the
   100-pt subsample (a heuristic to keep maxdim=2 Rips tractable on LARGE neural clouds) under-samples
   a 289-grid torus's 2-cell. This is exactly the H₂ fragility flagged in advance — caught in the act.
   The barcode GAP (8.4× full vs 1.1× sub), not the gate, is the robust discriminator.

**CONTROL — full-skeleton validated, b₂=1 confirmed (`torus_h2_control.py`, log `torus_h2_control.txt`).**
Synthetic torus vs figure-8 wedge, sampled identically (17×17 grid, R²⁵⁶, noise 0.03), both protocols:

```
  protocol        synthetic torus (b2=1)   synthetic wedge (b2=0)   learned torus
  full skeleton   gap 12.8x  b2=1          gap  1.1x  b2=0          gap 8.4x  b2=1
  subsample 100   gap  3.2x  b2=1          gap  1.3x  b2=0          gap 1.1x  b2=0
```

1. **Full-Rips does NOT over-count H₂.** The figure-8 wedge full-skeleton gap is **1.1×** (no spurious
   2-void) — so the "full Rips manufactures voids" objection is refuted. Full-skeleton cleanly
   DISCRIMINATES (torus 12.8× vs wedge 1.1×). The learned torus's **8.4×** (bracketed by the clean
   torus's 12.8×) therefore certifies a **GENUINE 2-TORUS**; the subsampled `b₂=0` is a confirmed
   under-sampling FALSE NEGATIVE, not an over-count.
2. **NUANCE — the learned torus is geometrically ROUGHER than ideal.** A clean synthetic torus
   SURVIVES 100-pt subsampling (gap 3.2×, b₂=1), but the learned torus does NOT (gap 1.1×, b₂=0).
   So its 2-void is real but more fragile — residual higher-harmonic "decoration" (the same
   competence-adds-variance effect seen in Leg-3b) distorts the embedding enough that only dense
   (full-skeleton) sampling resolves the void. The net builds a *genuine but wavy* torus.

**FINAL VERDICT (Waypoint B):** the 2-sum integrator builds a **genuine flat 2-torus T²=S¹×S¹**
(`b₁=2, b₂=1`), proven by THREE independent lines: (i) full-skeleton H₂ gap 8.4× with the over-count
null controlled (wedge 1.1×); (ii) separable product-carrier structure (83% axis, 0% cross power);
(iii) clean marginal rings (`b₁=1` each). The carrier-frequency law extends to 2D: independent running
sums → independent low-frequency circular codes in orthogonal subspaces → a product torus.
**CAVEAT:** single seed (42); the torus is genuine but geometrically rougher than an idealized one.

---

## Waypoint B — pre-registered predictions (seeds 43–45) + Lean-pivot decision

**DECISION (2026-06-23):** the four-leg empirical arc is consolidated. We do **not** run the
seed 43–45 sweep now. Rationale (the correction to the "perform the rigor" instinct): the single-seed
danger is a property of *boundaries* (α_c, Leg-3b → 3c, where one seed genuinely lied), **not**
*interiors*. The 2-torus is an interior result resting on a footing-independent algebraic argument
(orthogonal product carriers ⇒ S¹×S¹, no Rips needed) plus a controlled full-skeleton gap, so the
risk that all three lines flip on a new seed is low. The sweep would buy little insight at the cost of
cycles better spent on the Lean moat. We therefore **log the sweep as a pre-registered, falsifiable
claim** — runnable verbatim later (or by the next agent) — and pivot to formalization.

Pre-registered (carrier-scaffold orthogonalization law), to be checked if/when seeds 43–45 run:

| quantity | prediction | confidence | note |
|---|---|---|---|
| test acc, both heads | 100% | ~98% | learnable task; near-certain |
| FFT2 cross-power | ≤ 3% | ~80% | **core claim**: independent sums → orthogonal direct-sum f(s₁)⊕g(s₂) as a stable attractor |
| full-skeleton b₁,b₂ | 2, 1 (gap ≫ 1.1× null) | ~85% | conditional on low cross-power |
| subsample b₂ (N=100) | 0 | ~65% | "roughness tax" — empirical, NOT a law prediction |

**Key falsifier / coupling to watch:** if any seed entangles the two sums (cross-power ↑ above ~10%),
the prediction is that the 2-void pinches shut (full-skeleton b₂ → 0, a topological wedge). Observing
high cross-power *with* b₂=1, or low cross-power *with* b₂=0, would break the orthogonality⇒torus law.

## The Lean moat — what the empirics dock into (ground-truthed 2026-06-23)

- **`SGC.Topology.PadicPathSpace` is ε=0 (axiom-clean).** The keystone `pathSpace_homeo_padicInt`
  (`PathSpace (Fin p) ≃ₜ ℤ_[p]`) and the whole Horner/inverse-system tower are kernel-checked with no
  `sorry` and only `{propext, Classical.choice, Quot.sound}`. This is the symbolic domain of ONE
  p-ary integrator. **NEW (this session):** added `pi_pathSpace_homeo_pi_padicInt`
  (`(Fin d → PathSpace (Fin p)) ≃ₜ (Fin d → ℤ_[p])`) — the honest formal correlate of *d independent
  running sums*, sealed ε=0 by the same axioms. (d=1 ↔ ring, d=2 ↔ torus.)
- **`SGC.Geometry.Manifold.Convergence` holds the continuum half** as the tracked `axiom
  manifold_hypothesis` (Belkin-Niyogi, Mosco-convergence discharge path documented). The empirical
  "representation concentrates on T^d" is the discrete→continuum *image* of the p-adic domain — it
  belongs to THIS axiom layer, not a from-scratch metric proof.
- **Honesty flags (do not credit):** `spectral_convergence_axiom` (Convergence.lean L256) is
  **vacuous** (conclusion `∃ε₀ N₀, ε₀>0 ∧ N₀>0` mentions no eigenvalue); `stability_transfers_to_continuum`
  (L268) merely re-returns `manifold_hypothesis` and proves nothing about stability. Statement-strength
  audit needed before either is leaned on.
