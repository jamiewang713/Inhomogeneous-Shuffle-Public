# LB09 independent missing-hypotheses and counterexample review, v1

Reviewed 2026-10-01. Scope: the adopted LB09 prompt, manuscript `lem:cold-geometry`, `lem:finite-relative-endpoints`, `lem:localization`, the exact frozen `Targets.RelativeEndpointTarget`, `Targets.DeterministicColdGeometryTarget`, `Targets.LocalizationTarget`, `Targets.ColdGeometryFromEmpiricalTarget`, and their actual shared definitions. This is a mathematical audit before implementation, not a Lean proof or compilation receipt. Only this new report was written.

## Verdict

No counterexample to the exact frozen targets was found. No additional hypothesis or shared-contract change is requested. Several tempting intermediate statements are false; the explicit counterexamples below identify them. In particular, a proof must retain the ambient fluctuation at the right endpoint, use actual positive mass bounds before logarithm identities, preserve the fixed bridge factors, and obtain extra geometric slack from `H ≤ J`, rather than attempting to perturb the weakest displayed witness inequality.

There is no stochastic independence requirement between reserve counts, between a reserve and the ambient count, or between the localization event and tail columns. The final event must be proved for the actual shuffle law. Neither a target predicate nor the old `localizedKeys` premise is evidence of localization.

## Inputs and source identity

The actual declarations, rather than just historical status summaries, were read. The concrete imports expose:

- `RiffleLowerV2.Thinning.prefixTails : Targets.PrefixTails` and `RiffleLowerV2.Thinning.allPrefixConcentration : Targets.AllPrefixConcentration`, in `Thinning/Prefixes.lean`.
- `RiffleLowerV2.Thinning.prefixFailureUniform : Targets.PrefixFailureUniform`, in `Thinning/UniformError.lean`.
- `RiffleLowerV2.Witness.coldWitness : Targets.ColdWitnessTarget` and `empiricalTilt : Targets.EmpiricalTiltTarget`, through `Witness/Main.lean`.
- `RiffleLowerV2.Types.roundedType : Targets.RoundedTypeTarget`, through `Types/Main.lean`; `Types/Partition.lean` provides the regular-partition existence wrapper.

The early LB02 all-prefix receipt labels its helper conditional. That is accurate for `allPrefixConcentration_of_prefixTails`; the current `Prefixes.lean` discharges the premise with the concrete `prefixTails`. Do not mistake the old helper receipt for the current absence of a concrete result. LB05's final review receipt and LB06's `COMPLETION_v1.md` report the exact frozen exports and standard axiom closure; this review did not independently rebuild those lanes.

Reviewed fingerprints:

| File | SHA-256 |
|---|---|
| Authoritative manuscript | `672f414c9ccd6229c7f496c80cba6cc989c5fd07d93b75e66083456ee6242b1d` |
| `Contracts/v1/WitnessGeometry.lean` | `bbd3f28678e95ace37f07c0d993992f20fd4dc4d565ccbc11d0b8a4f1ba822bc` |
| `RiffleLowerV2/Shared/Geometry.lean` | `cb992d0297bcf75ada15ff6154a146caadfa3d984629aafd70f74feef6bfbb09` |
| `RiffleLowerV2/Shared/Path.lean` | `513afea203a5ad1a3b851fdb8317b4f6473d2c54e1c0466139b349530563acbf` |

## Relative endpoints: degenerate cases and a genuine false simplification

`RelativeEndpointTarget` intentionally quantifies over all natural `k,N,K`, with no positivity hypothesis on `N` or `k`. This is mathematically consistent.

- If `N=0`, `Fin N` is empty, all counts are zero, and every mean is zero because `prefixMean` multiplies by `N`. All identities and the requested nonnegative error bound hold. A generic product-normalization proof must split this case before dividing by `N`; the conclusion itself needs no amended hypothesis.
- If `k=0`, the supplied ambient word `a : Word k K` forces `K=0`. Hence `l=m=0`, there are no side cylinders, and the empty ambient prefix has count and mean `N`. This case is again valid.
- If `k=1` and `N>0`, every actual pile has size `N`; every legal suffix is the unique suffix. The left count and mass-before are zero, the right count and mean are the ambient count and mean, and all fluctuations vanish.
- If `l=m`, the unique suffix has product mass one and mass-before zero. The identities reduce to `0=0` on the left and `C(a)-muA=C(a)-muA` on the right. The requested bound still contains the ambient term even though there are no side cylinders.
- If `muA=0` and `N>0`, some ambient requested pile has zero size. No sample row can carry that prefix; every subcylinder also has zero mean/count. No conditional probability given the ambient prefix is needed or well defined in this case.

**Counterexample to deleting the ambient fluctuation.** Take `N=2`, `k=2`, `K=2`, with both columns having counts `(1,1)`. Choose the legal sample with rows `00` and `11`. Set `a=00` and `l=m=2`. Then `muA=2(1/2)^2=1/2`, `C(a)=1`, and the suffix is empty. Thus

```text
Urel - muA*(t+mass) = 1 - 1/2 = 1/2,
```

while every right-side-cylinder sum is empty and equals zero. The frozen right identity correctly keeps `C(a)-muA`; an identity containing only minus the right-side sum is false.

`sidePrefix` uses `j.val.val+1` and reads only preceding suffix coordinates before the differing digit. Under `l≤m≤K`, this is exactly the first-differing-digit cylinder. The ambient full word after position `l` is merely a representation choice: those trailing coordinates do not affect any prefix count or mass in the identities.

For each of the left and right side families, the cylinders are pairwise disjoint and are contained in the ambient cylinder. Thus the means sum to at most `muA`, and their number is at most `kK`. Cauchy--Schwarz yields each side's `sqrt(kK)*sqrt(muA)+kK` bound. The right ambient fluctuation contributes the additional `sqrt(muA)+1`. This yields exactly the frozen constant, including small positive means; replacing `sqrt(muA)+1` by `sqrt(muA)` is not justified.

## Bridges, zero probabilities, and empty selected blocks

`WitnessSpec` supplies two distinct ordered good bridge columns and `ms≤mu≤mu+bridgeLength≤K`. Hence a bridge of length zero or one cannot satisfy the witness. There is no need to infer availability again from a density hypothesis inside `DeterministicColdGeometryTarget`: density is an upstream witness-construction input.

**Counterexample to using only one binary good column.** With `k=2` and a one-column bridge of law `(1/2,1/2)`, no bridge word has both a strictly smaller and a strictly larger bridge word. A central digit is either `0`, with no smaller digit, or `1`, with no larger digit. The two-good-column condition avoids this obstruction: use the larger digit at the first good column, the smaller at the second, and change only the specified column in each reserve.

At the two distinguished columns every central/reserve word has digit probability at least `chiGood`; all other bridge columns can use a maximal digit with probability at least `1/k`. Therefore the stronger bound `chiGood^2*k^(-(bridgeLength-2))` implies the frozen conservative bound `chiGood^2*k^(-bridgeLength)`. The two constants `chiGood` must not disappear during the conversion to exponent form. With `bridgeLength=ceil(2*rho*log N)`, the precise loss is bounded by

```text
2*rho*log k + (log k + 2*log(1/chiGood))/log N.
```

Positivity follows before taking the logarithm. If `chiGood>1/2`, two distinct good digits cannot exist in a probability simplex, so the witness premise is impossible. This is not a counterexample requiring `chiGood≤1/2` as an extra theorem hypothesis.

Every prefix/tail selected class is nonempty by `TypeDataSpec`. In particular, an empty tail position set has the singleton empty word, mass one, and exponents zero. It must not be represented as an empty selected family. Zero piles elsewhere in the cuts are permitted; the selected support guarantee gives actual probability at least `xi`, and ambient maximal digits have probability at least `1/k`.

The common digit lower bound is exactly `min xi (min chiGood (1/k))>0`, with positivity of `xi,chiGood` and `k≥2` provided in the geometry/localization targets. This bound covers ambient, selected prefix, bridge, and selected tail coordinates. No lower bound on every pile in the model is required.

## Rounded exponents: where the necessary slack comes from

Let `κ=kappa eta`, `κ0=kappa0 eta`, and let the type-approximation budget be `a=min(κ,κ0)/1000`. The frozen approximation bounds are sums of two absolute errors; therefore each individual cost/entropy error is at most `a`. Choosing `xi` sufficiently small and then `N` large makes this budget available by the actual LB06 theorem.

**Counterexample to perturbing only the weakest displayed witness inequality.** The scalar implication

```text
H ≤ b-J-κ,
|J*-J|≤a, |H*-H|≤a
    implies H*≤b-J*-κ
```

is false for any `a>0`: set `H=b-J-κ`, `J*=J+a/2`, `H*=H+a/2`. It remains false if the sum of errors is bounded by `a`. This is an intermediate-proof counterexample, not a counterexample to `WitnessSpec` plus the concrete empirical definitions.

The missing slack is derived from the checked empirical inequality `H≤J` and the witness bound `J≤b/2-3κ`. These imply `H≤b-J-6κ`, so the actual perturbations safely imply `H_p*≤ell_p-κ`. Likewise `ell_p≥b/2+3κ-a≥b/2+2κ`, and perturbing `h≥κ` gives `h_N≥κ/2`.

For the deleted bridge, let `dJ,dH` be the actual empirical cost/entropy on its columns. Nonnegativity and the one-column bounds give `0≤dJ,dH≤d`, where `d=(2rho+1/log N)log k`. With `ellB` the actual central bridge exponent, write

```text
Jp*=J+δpJ, Hp*=H+δpH,
Jt*=Jt-dJ+δtJ, Ht*=Ht-dH+δtH.
```

Every error has absolute value at most `a`. Exact subtraction gives

```text
hN-h = -δpJ+δpH,
(gN-hN/2)-(Γ-h/2)
  = -(3/2)δpJ+(1/2)δpH-2δtJ+δtH+2dJ-dH-2ellB.
```

The source's conservative loss `7a+d+2ellB` is valid. The extra bridge budget `2rho log k≤κ0/100`, followed by a threshold absorbing the fixed `chiGood,k` terms, gives `d,ellB≤κ0/50`. Together with `κ0≤κ/100`, this preserves the frozen `κ/2` collision margin. The same decomposition gives `zN≤κ0+2a+d≤2κ0`. No limiting exponent is substituted for the actual rounded exponents.

The full-family cardinality requires injectivity of `(x,z)↦joinColdWord G x G.central z`; it follows from the disjoint column sets and the witness endpoint order. An image-cardinality equality without this proof would be invalid in general. Product factorization, both strict lower mass-bin bounds, and the exact ambient/bridge identities yield the strict `exp(-2)N^zN` lower bound as stated.

## Integer geometry and rank conventions

For each selected prefix the scaled interval is half open and has length in `(exp(-1)N^ellp,N^ellp]`. Distinct word probability intervals are disjoint, but adjoining intervals need not give distinct connected components of their union. For example `[0,1)` and `[1,2)` are distinct disjoint selected intervals whose integer union is the connected set `{0,1}`. Boundary estimates must use an upper bound by twice the number of intervals, not equality with twice the number of components asserted per word.

Integer-point count differs from length by at most two, uniformly in the location. Summing over the disjoint intervals gives the frozen `exp(-2)N^hN≤M≤2N^hN` after increasing a uniform threshold. The lower bound `hN≥κ/2` then gives `M≥N^(κ/3)` after absorbing `exp(-2)`. The deterministic containment in `[0,N*lambdaA)⊆[0,N)` gives the exact `M≤N`.

Before clipping, the boundary is at most `2N^Hp*`. Clipping a translate to one finite interval adds at most two boundary edges. Since `Hp*≤(hN-κ)/2` and `sqrt M≥exp(-1)N^(hN/2)`, the target `4sqrt M` follows for large `N`, uniformly in `q`. This does not require the translated set to have cardinality `M`; clipping can remove points.

The Lean convention is explicit: `manuscriptRank i=i.val+1`, and `i∈clipTranslate N Hrel q` means `manuscriptRank i-q∈Hrel`. Consequently `q=lowerRank ambient` is the number of preceding rows, exactly as in the manuscript.

**Counterexample to localization without any reserve slack.** Take an exact scaled relative interval `[0,2)`, `q=0`, and a word occupying both one-based ranks `1,2`. The endpoint counts are exactly `L=0,U=2`; nevertheless rank `2` is outside `Z∩[0,2)`. Exact endpoint concentration alone does not resolve the half-open convention.

With endpoint errors at most `e` and both reserve counts at least `e+2`, every central-word rank `i` satisfies

```text
q+L+Cminus+1 ≤ i ≤ q+U-Cplus,
q+ell+3 ≤ i ≤ q+r-2.
```

This is more than enough to put `i-q` in `[ell,r)`. Two units are sufficient, rather than claimed to be a minimal possible constant. The argument applies to every tail word on the same event, since lexicographic bridge ordering is decided before any tail coordinate is inspected.

## Uniform probability and threshold audit

On `allPrefixEvent (κ/4)`, the finite relative endpoint estimate gives

```text
eN=N^(κ/4)[(2sqrt(kK)+1)N^(b/2)+2kK+1].
```

`typeJ≥0` and `ellp≥b/2+2κ` give `b≥4κ`. With `K≤T log N`, dividing by `N^(b/2)` bounds the remaining bracket by a function of `k,T,log N` alone, at most a constant times `log N+1`. Hence `eN≤N^(b/2+κ/2)` after a threshold independent of the cuts, witness, and rounded classes.

Every reserve mean is at least `N^(b/2+κ)≥N^(3κ)`. For a fixed witness there are at most `2k^K≤2N^(T log k)` reserve prefixes. The concrete `prefixTails` theorem therefore bounds the probability that any reserve count is at most half its mean by

```text
2 N^(T log k) exp(-chernoffConstant*N^(3κ)),
chernoffConstant=(1-log 2)/2>0.
```

This tends to zero uniformly. At a further threshold, half each mean is at least `eN+2`. No independence is used in this union bound. If one deliberately asks for a common event across all possible witness lengths, the all-prefix count is `(K+1)k^K`, rather than just `k^K`; the additional logarithmic factor is harmless but should not be silently omitted. The frozen target requires a uniform probability bound for every witness, not an extra simultaneous-across-witnesses assertion.

An alternative valid route is available: the same all-prefix event already controls each reserve. Its error `N^(κ/4)(sqrt(mu)+1)` is at most `2N^(κ/4)sqrt(mu)` because `mu≥N^(3κ)≥1`. Dividing by `mu`, this is at most `2N^(-5κ/4)≤1/2` once `N^(5κ/4)≥4`. Thus one can obtain both endpoint and reserve bounds on the one common all-prefix event, whose failure bound already contains the polynomial union cost. This alternative introduces no tail independence premise and no new stochastic assumption.

The exact quantifier orders are feasible:

- Deterministic geometry: fix `k,T,eta,rho,chiGood`; choose `xi`, then a regular partition `P`, then `N0`; all cuts and all supplied finite witnesses follow. The cell count of the chosen partition is fixed before the LB06 rounding threshold is selected.
- Localization: fix the displayed positive parameters, arbitrary `P`, and the probability tolerance; choose `N0`; then quantify over cuts, witnesses, and geometry data satisfying the actual specifications. Regularity of `P` is not needed again for localization, because its relevant outputs are already in `GeometrySpec`.
- Concrete empirical target: choose `xi,P` before the requested probability tolerance; for each tolerance take the maximum of the deterministic geometry, upstream witness, concentration, reserve, and asymptotic thresholds. All of those depend only on allowed fixed parameters.

Neither selected words, actual cut arrays, the value of `b`, the realized sample, nor the tail word can enter `N0`. Small `N` and invalid logarithmic scales are excluded only in the asymptotic targets by `N0≥2`; the finite endpoint target remains total.

## Remaining proof obligations versus obstacles

The old `RiffleLower.localized_collisions_supply_edges` proves a finite combinatorial implication from localization. It does not prove localization. Once actual rank membership is established, distinct repeated full words have disjoint constant-word blocks, so choosing the first internal edge gives the required injective assignment. The old edge representation uses pairs of adjacent positions, while the frozen V2 representation uses the left index in `Fin (N-1)`. Adapting or reproving that finite lemma is an API task; there is no mathematical obstruction.

Other representation work remains substantive but routine in principle: first-differing-digit finite partitions, conversion between `columnSet` finite sums and grid empirical integrals, integer half-open interval counts, boundary subadditivity/clipping, product factorization, and logarithm/rpow identities under proved positivity. This review supplies no placeholder assumptions for those obligations. Completion still requires checked concrete exports and their axiom/build audit; the present verdict certifies only that the inspected frozen statements survived these counterexample and hypothesis checks.

The coordinator's `INTERFACE_PROPOSAL_v1.md` was also read before finalizing this report. Its exact planned exports, unchanged frozen assumptions, six-unit entropy slack, single all-prefix event, and no-new-independence decisions agree with this review. No interface amendment is requested; obtaining the required LB00 acknowledgement remains the coordinator's separate gate before dependent proofs.
