# LB04 uniform asymptotic scan delivery v1

`RiffleLowerV2.Ascent.Asymptotic` now compiles without warnings. It proves the exact conditional implication `uniformGraphScan_of_comparison : Targets.ComponentComparison → Targets.UniformGraphScan` and separate quantitative and eventual uniform null-scan estimates. It does not assert the pending concrete comparison or actual shuffle representation.

## Checked exports

All declarations are in namespace `RiffleLowerV2.Ascent`; exact elaborated types are in `asymptotic_axioms_v1.log`.

- `graph_scan_ge_of_comparison`: under the explicit finite size conditions M>0, 576≤M^delta and 24D≤M^delta, all clipped boundaries at most D sqrt(M), and a successful edge translate, scan success has probability at least `1-exp(-M^(2delta)/144)`. It uses the previously checked `chosenTranslate` and its graph-only success specification.
- `failure_envelope_tendsto_zero`: for a,delta>0, `exp(-N^(a*(2delta))/144) → 0` along natural N.
- `uniformGraphScan_of_comparison`: the exact frozen eventual graph scan follows from the exact frozen finite comparison target, with no changed assumption, constant, or quantifier.
- `scan_threshold_sq_div`: for M>0, `(M^(1/2+delta/2))²/M = M^delta` exactly.
- `null_scan_envelope_tendsto_zero`: for beta>0, `(N+1)exp(-N^beta) → 0`.
- `uniform_null_scan_bound`: from an explicit `Targets.UniformScan`, N>0, a,delta>0, and M=|H0|≥N^a, bounds the null scan probability at threshold M^(1/2+delta/2) by `(N+1)exp(-N^(a*delta))`.
- `uniform_null_scan_eventually`: after fixing a,delta,epsilon>0, produces one N0≥1 such that for all N≥N0 and all integer H0 with |H0|≥N^a, the null scan probability is at most epsilon.

## Uniformity and positivity audit

The graph threshold is chosen only after a,delta,D,epsilon and before N,H0,G. A single eventual natural-N predicate combines N≥1, `N^(a*delta)≥576`, `N^(a*delta)≥24D`, and the failure envelope below epsilon. The returned threshold is explicitly increased to max(N0,1). Positivity of N and N^a implies M>0. Monotonicity in the positive powers delta and 2delta then transfers the size and error bounds from N^a to M, with the exact rpow multiplication identities proved inside the implementation. The use of `chosenTranslate` involves no permutation argument.

The null-envelope proof sets x=N^beta, invokes the registered decay of `x^(1/beta)exp(-x)`, proves `(N^beta)^(1/beta)=N`, and adds the separate exp(-N^beta) limit. The threshold-square identity is checked algebraically through rpow multiplication and addition, not assumed. No M≤N, positive support, diameter, connectedness, or nonempty-clip restriction occurs.

The finite graph helper applies `quantitative_component_failure` to the fixed chosen clip, takes the exact complement of its weak failure event, and embeds that strict successful-clip event into the scan union. Thus the strict scan and weak complement are preserved.

## Verification and dependencies

The owned module imports only `RiffleLowerV2.Ascent.Quantitative` and `RiffleLowerV2.Ascent.Selection`. The former imports the registered pinned `Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics`; no new shared dependency is introduced here. Source-label correspondence is `lem:lalley-comparison`, `lem:uniform-ascent`, and the deterministic conditional-graph portion of `lem:lalley`.

Successful serialized command:

```text
python3 audit/LB04/compile_lane.py RiffleLowerV2.Ascent.Asymptotic
```

Warning-free build log: `build-20261001T155849424555Z.log`, with both additive dependency receipts passing. The read-only `asymptotic_check_v1.lean` check imported the compiled module and printed every type and axiom set, serialized by the common build lock. `asymptotic_axioms_v1.log` records exit status 0 and only `[propext, Classical.choice, Quot.sound]` for all seven declarations.

## Integration boundary

The root lane entry point should specialize `uniformGraphScan_of_comparison` with its concrete `componentComparison`, and specialize the null-scan helpers with its concrete `uniformScan`. The actual graph-mixture law and high-probability graph witness remain separately discharged by the upstream and downstream lanes. Neither is assumed implicitly or presented as proved here.
