# LB09 independent final endpoint review v1

Reviewed 2026-10-01. Verdict: **approved against the exact unchanged `Targets.RelativeEndpointTarget`**. No mathematical defect, extra final hypothesis, omitted ambient fluctuation, hidden positive-mean premise, or circular target assumption was found. No proof source was edited by this review.

The reviewer authored the separate Words/Bridge/RankBarriers modules and the pre-proof hypotheses audit, but did not author the reviewed endpoint modules. This review read every file below, the actual frozen target/shared definitions, and the completed endpoint build/axiom records. It did not infer correctness merely from a target name.

## Exact target and proof scope

The exported declaration is literally

```lean
RiffleLowerV2.Localization.relativeEndpoint :
  RiffleLowerV2.Targets.RelativeEndpointTarget
```

Its proof introduces `k,N,K,cuts,a,l,m,hlm,hm,x,omega` in the frozen order. It first supplies both exact identities, then introduces the quantified positive real `A` and the bound for every actual prefix. No extra requirement `N>0`, `k≥2`, positive ambient mean, nonempty suffix, or selected-type regularity appears in the final theorem. The coefficient is exactly

```text
A * ((2*sqrt(k*K)+1)*sqrt(muA) + 2*k*K+1).
```

This is the finite deterministic implication requested by `lem:finite-relative-endpoints`. It does not assume or attempt to prove a stochastic high-probability event; the lane's localization assembly supplies the actual simultaneous-prefix theorem separately.

## Exact identities and source correspondence

`Endpoints/Partitions.lean` proves that a function differs first from a given function at at most one coordinate. The abstract relation `R` must imply unequal digits; both left (`d<x_j`) and right (`x_j<d`) relations satisfy that requirement. `sum_sideMatch` proves a pointwise indicator partition, and `weighted_side_partition` interchanges only finite sums. Thus disjointness is proved, rather than encoded as an unverified family premise.

`Endpoints/Coordinates.lean` proves that the actual frozen `sidePrefix` cylinder is exactly the ambient prefix equality together with equality before its first differing suffix coordinate and the prescribed differing digit. Its use of `j.val.val+1` matches the zero-based stored column and one-based prefix length. The inequalities `l≤m≤K` establish every truncation bound; no irrelevant coordinate after the side prefix enters the event.

`Endpoints/Counts.lean` applies the indicator partition to the actual rows with weight one. It obtains the left count as a sum of side counts. On the right it proves

```text
Urel + relativeGreaterCount = C(a),
```

using the exhaustive alternatives `suffix≤x` and `x<suffix` inside the ambient cylinder. No replacement of `C(a)` by its mean occurs.

`Endpoints/ProductWeights.lean` derives cylinder products by summing all unrestricted finite coordinates and using their normalization. `Endpoints/Means.lean` identifies each frozen `sidePrefix` product with the ambient product times the side weight, then derives the left and right mean decompositions. In the positive-population case the suffix law sums to one by the actual column totals. The central word mass is retained in `relativeMass_total`; no equality event is dropped.

The final identities are consequently exactly

```text
Lrel-muA*t = sum_left(C(side)-mu(side)),
Urel-muA*(t+mass) = (C(a)-muA)-sum_right(C(side)-mu(side)).
```

The right ambient term is present both in `relativeEndpoint_identities` and in the final exported target. The pre-proof counterexample remains a useful direct check: with `N=2,k=2,K=2`, both columns having counts `(1,1)`, sample rows `00,11`, ambient `00`, and `l=m=2`, the right fluctuation equals `1/2` despite an empty right side sum. The implementation yields that `1/2` from its explicit ambient correction.

## Finite square-root bound

`finite_weight_error` proves a general finite sum estimate by:

1. Applying the triangle inequality to the sum of signed errors.
2. Applying the supplied individual error bound to every included member.
3. Applying the trusted finite Cauchy--Schwarz square-root inequality to `sum sqrt(mu_i)`.
4. Replacing the family cardinality and total mean by their proved bounds.

All `mu_i` are required nonnegative; this is discharged for the actual prefix means by their product definition. No division by a mean or by its square root occurs. Empty families and zero means are therefore covered directly.

`side_error_bound` indexes the family by actual pairs `(side column,digit)` satisfying `R`. Its finite cardinality is at most `(columnSet K l m).card*k≤K*k=k*K`. The disjointness-based total-mean bound is supplied by `sideMean_sum_le`, which comes from the same normalized finite product law and unique-first-difference partition. The concentration premise is instantiated with the actual side prefixes.

The final theorem applies this bound once to each side. It adds the ambient error `A*(sqrt(muA)+1)` only on the right and uses `abs_sub` with the correct direction. Ring normalization yields precisely the frozen coefficient, including the `+1` that protects zero and small means. There is no dependence of the constant on the chosen ambient word, suffix, cuts, sample, or mean.

The generic helper's nonnegativity parameters `M,D` are syntactically unused because the square-root monotonicity facts already suffice for those intermediate inequalities. They are nonetheless concretely discharged, and this does not add a final assumption or conceal an exceptional case.

## Edge-case audit

- **`N=0`.** The final mean identities and final error theorem explicitly branch on population positivity. In the zero branch every prefix mean has the factor zero, and every row-count finset is over empty `Fin 0`. All endpoint errors vanish; the requested right-hand side is nonnegative because `A>0`. Normalization by `N` is never asserted in this branch.
- **`k=0`.** A supplied ambient `Word 0 K` forces `K=0`; otherwise it cannot exist. The proof does not need this as a new hypothesis or special axiom. All universal finite sums/products are well typed in the empty case. With `K=l=m=0`, the empty ambient prefix has count and mean `N`, while the empty suffix has mass one.
- **`k=1`.** The unique suffix cannot have either a smaller or a larger digit. Both side families are empty; column normalization and the actual ambient term remain valid. No proof invokes `k≥2` or `log k>0`.
- **`l=m`.** The selected-coordinate type is empty, with one empty function word and empty product one. The left identity is zero; the right identity is exactly the ambient fluctuation. The empty-cylinder Cauchy bound is valid and the ambient error is still included.
- **`muA=0`, `N>0`.** Some ambient coordinate has zero product mass, or the relevant finite product is zero. The algebraic side-mean factorization and nonnegativity imply zero total side mean. The proof neither conditions on the zero-mass ambient cylinder nor divides by `muA`. Its concentration assumption handles the ambient count directly.
- **Small positive means.** No mean cutoff is used. Every summand retains `sqrt(mu)+1`, so the final expression is valid uniformly down to zero.
- **`m=K` and `l=0`.** Prefix-at truncations are protected by the provided endpoint bounds, and the ambient empty-prefix case requires no special stochastic assumption. The exact side-prefix construction includes the terminal column when appropriate.

## Trust and build evidence

The reviewed `Endpoints/Check.lean` contains an `example` with literal frozen target type, plus checks of the concrete export and its dependency closures. The completed `endpoints-axioms-v1.log` prints the exact type and reports only `propext`, `Classical.choice`, and `Quot.sound` for the final theorem, its identities, the count decompositions, side-mean product theorem, total-mean bound, finite error theorem, and word-order helper. It ends with `LB09 BUILD_OK`. `endpoints-build-dev04.log` also ends with `LB09 BUILD_OK`.

Every inspected endpoint compiled output is newer than its corresponding reviewed source. This review inspected the existing compiler outputs and logs rather than unnecessarily rebuilding unchanged files. The final coordinator audit remains responsible for binding the complete lane's export inventory and all private/generated declarations.

No proof token or premise restates the desired endpoint result. Imports of the frozen target definitions are used to state the result; they are never counted as evidence for it. The endpoint proof requires no endpoint anti-concentration, upper first-moment estimate, large-block density, localization theorem, or tail-column independence.

## Reviewed fingerprints

| Reviewed file | SHA-256 |
|---|---|
| `Localization/Endpoints.lean` | `bce799292af3cc5ed224dd25758075d1e85cb79303814c9b160e1054fbeda8c1` |
| `Localization/Endpoints/Partitions.lean` | `5fd701406a6895dd80cc33613a6c3ad4b5c6f66a0fb8d41ea22686299101a5be` |
| `Localization/Endpoints/Coordinates.lean` | `c86d33a9afbe3386b70a5c1d4167c02fd1de1fddb18efea2a938646618b0d10c` |
| `Localization/Endpoints/Counts.lean` | `c5cd41df45ff7fe05faebe67d3c90bdcd5269de748325e781a0cc1724b3548fc` |
| `Localization/Endpoints/ProductWeights.lean` | `eb975dc64e1fe3032c6aba074456aa1d42da3df049e1975c9809b3751c99c6dd` |
| `Localization/Endpoints/Means.lean` | `d28f66f39b536f32a7472797aaef4ce5a316511675cc133c6a806c7fddfbe86e` |
| `Localization/Endpoints/Error.lean` | `a97ee48e804080dd2dabec18550a60189c00c6bb7ab8d27495a943aa008ed73c` |
| `Localization/Endpoints/Check.lean` | `1f1740677f6c0f0c06ae7aee6e00eb10de49d98f72696e09611b3c150bac837a` |
| `Localization/WordOrder.lean` | `f65785e9ac187c4ba0f4d67f87e01a99166808fa481f801d07e55488a0b9f7ef` |
| `Contracts/v1/WitnessGeometry.lean` | `bbd3f28678e95ace37f07c0d993992f20fd4dc4d565ccbc11d0b8a4f1ba822bc` |
| `audit/LB09/endpoints-axioms-v1.log` | `20467a697c8af916e805146e60c3f162b2d1c187af3ebcecdf8bef555f96713f` |
| `audit/LB09/endpoints-build-dev04.log` | `67729882fcc4f3125f94185d01d8dd4a1f220022094e5c35e9992c8fbc488061` |

No correction is requested. All endpoint-specific mathematical, representation, and hypothesis findings from this independent review are resolved.
