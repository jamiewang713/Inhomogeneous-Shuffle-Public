# A05 implementation and declaration coverage

Implemented file: `RiffleProfiles/CountLimits.lean`.

SHA256: `70a5765d1e89df357438c6ae53a5bfadf2a48174c85a909bc60eeb877c1465c7`.

This implementation was written only after the A01–A06 contract and
three compared helper reviews were frozen. The frozen contract hash is
`7074bcb2888043662af650e8c390e3a7c36edba602c13786a9604d1397fcefb1`.
No earlier F/S/T statement, source definition, dependency, or other
agent's module was edited.

## Declaration coverage

All names below lie in `RiffleProfiles`.

| Declaration | Frozen coverage |
| --- | --- |
| `countErrorExponent` | Exact reviewed expression `3*T*k/sqrt u + C*log u/u + log u/(2*sqrt u)`. |
| Private `common_z_parameters` | For `u≥1`, the common parameter `z=1/sqrt u` satisfies `0<z≤1` and `log z=-log u/2`. |
| `countErrorExponent_tendsto` | For fixed natural `k`, `T≥0`, and `C>0`, the exact error exponent tends to zero as real `u→+∞`. The frozen sign premises are retained, even though this limit proof itself would not need them. |
| `exists_countErrorExponent_cutoff` | For every positive `eta`, provides `U≥1` such that the same exponent is at most `eta` for every `u≥U`. |
| `fixed_polynomial_le_rpow` | For `c≥0`, `T≥0`, natural `m`, and `eta>0`, provides natural `N0≥2`, uniformly for all natural `N≥N0` and `K≤T*logScale N`, with `c*(K+1)^m≤N^eta`. |
| `common_z_count_product_le_rpow` | The two boundary counts and one exceptional count are bounded by `N^E`, with the exact reviewed logarithmic exponent `E=3*T*log(1+k/sqrt u)+C*log u/u+log u/(2*sqrt u)`. Domains are precisely natural `N,K,k`, `N≥2`, `T≥0`, `C>0`, `u≥1`, and the depth bound. |
| `count_product_le_error_rpow` | The same finite product is bounded by `N^(countErrorExponent k T C u)`, using `log(1+x)≤x` and no extra premise. |
| `descriptor_count_le_rpow` | Frozen A05 in its exact natural-count cast, including `k^2`, `(K+1)^(d+2)`, the squared boundary `lowCount`, and the exceptional `lowCount`. |

## Exact A05 choices and thresholds

The public theorem takes fixed `k:Nat`, `T,C,epsilon:Real`, with
`k≥2`, `T≥0`, `C>0`, and `epsilon>0`. It returns

`exists chi0>0, chi0<min(1,1/k), forall chi in (0,chi0),
  forall d:Nat, exists N0:Nat, N0≥2,
  forall N,K:Nat, N≥N0 -> K≤T*logScale N -> [A05 bound]`.

The `chi0` cutoff is selected from the vanishing count exponent before
introducing `chi` or `d`. The natural `N0` is selected only after `d`
is fixed. The proof divides the positive target exponent equally
between the sparse-count product and the fixed polynomial factor.

The thresholds remain exactly
`Nat.floor ((C / chiLog chi) * TimeProfile.logScale N)` and
`Nat.floor (exceptionalAllowance chi * TimeProfile.logScale N)`.
The full descriptor product uses natural arithmetic before being cast
to real. The common-z helpers expose the equivalent real product of
the same natural counts; cast identities in the final theorem connect
the two layouts without changing the counts.

Neither the helpers nor A05 require positive `T`, positive `K`,
positive `c`, positive `m`, or thresholds below `K`. The frozen
`k≥2` premise belongs only to A05; the finite common-z helpers still
allow `k=0`. There is no new probability, time-measurability,
independent-row, integral, partition-dimension, or analytic-model
hypothesis.

## Verification

The pinned Lean 4.19.0 / mathlib `c44e0c8` check completed with exit
code zero and warnings treated as errors:

`python3 lean_formalization/check_lean.py lean_formalization/RiffleProfiles/CountLimits.lean`

The module imports only `Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics`
and the proved project module `RiffleProfiles.AsymptoticFinite`.
The proof uses trusted mathlib logarithmic little-o and real-power
limits, the already proved A02 generating bound, and finite arithmetic.

An explicit `#print axioms` audit of the definition and all six public
theorems returned exactly `[propext, Classical.choice, Quot.sound]` for
each declaration. In particular, the final theorem transitively checks
the private parameter helper as well. No additional axiom, unproved
declaration, or placeholder is used.

The independent source-family injection and continuous analytic target
connection remain separate obligations; this module establishes the
frozen descriptor-count consequence only.
