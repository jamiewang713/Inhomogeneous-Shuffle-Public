# LB06 truncation implementation delivery v1

Date: 2026-10-01. Status: the retained-law construction, explicit omitted mass/cost/entropy bounds, and both actual-cell transfer estimates are proved and checked. Rounded integer counts, exact multinomial cardinalities, deterministic mass bins, and the final `roundedType` assembly belong to the other implementation components; this delivery does not independently certify those components.

## Owned source and provenance

Source: `RiffleLowerV2/Types/Truncation.lean`.
SHA-256: `43f19d9366f2cc8608da41158d38be6b1d2d6f115509ccd7857fba828bfea346`.

The module imports only `RiffleLowerV2.Shared.Geometry`. It does not import LB05, an old package, a compatibility port, or a temporal approximation theorem. All new helpers are proved in this file. The source implements the first two paragraphs of the proof of manuscript `lem:type-estimates`, along with the explicit normalized-law and boundary-case obligations in the adopted LB06 brief.

Proof work began after `audit/LB00/LB06_INTERFACE_ACK_v1.md`; the exact v1 statement and all shared definitions remain unchanged. The additive dependency checker was also run after the dependency receipt and returned `LB06-v1 DEPENDENCIES_OK`, although this particular module uses none of the newly registered imports.

## Principal exported interfaces

Every name below is in namespace `RiffleLowerV2.Types`. Exact Lean output for the principal types is in `truncation-check-v1.log`.

- `retainedTilt_denominator_pos hk P hxi hxiK i`: strict positivity of the denominator used in the frozen `retainedTilt` definition. Here `hk : 2<=k`, `hxi : 0<xi`, and `hxiK : xi<1/(4k)`. It holds for every real `alpha`, with no regularity or eventual-N assumption.
- `retainedTilt_nonneg P xi alpha i l`: every retained weight is nonnegative.
- `retainedTilt_sum hk P hxi hxiK i`: the sum of the retained weights equals 1.
- `retainedTilt_eq_zero_of_omitted P xi alpha i l hl`: `prob (P.rep i) l <= 2xi` implies the retained weight is zero.
- `retainedTilt_pos_of_retained hk P hxi hxiK i l hl`: a retained digit has positive weight.
- `retainedTilt_le_one hk P hxi hxiK i l`: every retained weight is at most 1.

Define the checked constants

```
truncationCostConstant k C = C + 8*C*exp(C) + 18*k^5,
truncationEntropyConstant k C = 4*truncationCostConstant k C + 4*C + 9*k^5.
```

For both transfer theorems the argument list is

```
hk P hxi hxiK hC hreg ha i p hp
```

where `hC : 0<=C`, `hreg : P.IsRegular xi C`, `ha : alpha in [2,4]`, and `hp : P.classify p=i`.

`retainedTilt_cost_transfer` proves

```
|sum_l retainedTilt P xi alpha i l * digitCost (prob (P.rep i) l)
  - tiltedCost p alpha|
<= truncationCostConstant k C * xi * log(1/xi).
```

`retainedTilt_entropy_transfer` proves

```
|shannonEntropy (retainedTilt P xi alpha i) - tiltedEntropy p alpha|
<= truncationEntropyConstant k C * xi * log(1/xi).
```

These are uniform over every admissible cell, representative, actual simplex point, and tilt. Specialization to actual columns takes `p=cuts.profile hN j`, `i=P.classify p`, and `hp=rfl`.

## Explicit omitted contributions

`omittedSum r p xi alpha` is the sum of actual powers on coordinates with representative probability at most `2xi`. `omittedCostSum` is the corresponding unnormalized power-weighted digit cost. `omittedEntropySum` is the entropy contribution of the *full normalized tilted law* on those omitted coordinates, with an explicit zero-weight guard.

Under `k>=2`, `alpha in [2,4]`, and the representative-to-actual omission premise

```
forall l, prob r l<=2xi -> prob p l<=3xi,
```

the following are checked:

```
omittedTiltedSum_le:
  omittedSum r p xi alpha / powerSum p alpha <= 9*k^5*xi^2.

omittedTiltedCost_small:
  omittedCostSum r p xi alpha / powerSum p alpha
    <= 12*k^5*xi^2*log(1/xi).

omittedEntropySum_bounds:
  0 <= omittedEntropySum r p xi alpha /\
  omittedEntropySum r p xi alpha <= 48*k^5*xi^2*log(1/xi).
```

The mass bound assumes `xi>=0`. The cost and entropy bounds assume `0<xi<1/8`, implied by the lane's cutoff hypotheses. For actual columns, the omission premise is exactly `P.IsRegular.exceptional_digit`; for a representative compared with itself it follows from `xi>=0`.

The sharper cost proof uses the elementary identity

```
log(1/x) = log(1/xi) + log(xi/x)
```

and `log y<=y-1`, so it needs no derivative or monotonicity proof for `x^2 log(1/x)`. The entropy contribution is nonnegative and at most four times the omitted tilted cost, with zero probabilities handled explicitly. A coarser `omittedTiltedCost_le` bound by `3*k^5*xi` is used internally in the final transfer estimate; the sharper bound is an additional proved export.

## Proof dependency and boundary audit

| Obligation | Checked result |
|---|---|
| Nonempty retained support | A maximal simplex coordinate is at least `1/k>2xi` |
| Positive retained normalization | `retainedTilt_denominator_pos`, `restrictedSum_pos` |
| Uniform full denominator | `powerSum_card_lower`: `1<=k^4*powerSum` |
| Retained normalization and support | The six `retainedTilt_*` interfaces above |
| Supported logarithmic entropy identity | `entropy_eq_cost_log`, `restrictedEntropy_identity`, `tiltedEntropy_identity` |
| Coordinate-weight comparison | `restrictedWeight_cell_error`, bounded by `(exp(8Cxi)-1)` times the actual retained law |
| Linear exponential estimate | `exp_cell_error`: `exp(8Cxi)-1<=8C exp(C) xi` |
| Cost loss on omission | `restrictedCost_truncation_error`, coefficient `18k^5` |
| Representative logarithmic denominator | `restrictedLog_rep_error`, coefficient `9k^5 xi^2` |
| Entropy transfer | Uses the proved cost transfer and frozen regularity's `psi_oscillation` |
| Source-scale omitted cost/entropy | The sharper bounds displayed above |

There are no assumptions that an omitted-probability upper estimate is less than one-half. The algebra uses exact mass decompositions and positive denominators. Zero probabilities are excluded only inside logarithmic formulas whose support has been proved positive, and all zero contributions are retained as zero in finite sums. No hidden lower bound on cell occupancy or selected-block length occurs anywhere in the file.

## Verification

Successful command:

```text
python3 scripts/lane.py LB06 RiffleLowerV2.Types.Truncation
```

`truncation-build-v3.log` records `LB06 BUILD_OK` with no warnings. Its SHA-256 is `769c2d7058ee67a6885e3c04b1112c5a555cd2541271eff2d04ad1beb35b6216`. The preserved v1/v2 build logs record only shared lane-lock contention, not proof failures.

The independent audit entry point `audit/LB06/truncation-check-v1.lean` was executed with the pinned compiler, `LEAN_PATH` set to `.build/lanes/LB06/lib/lean`, and `-DwarningAsError=true`. It printed exact types and axiom closures for the seven principal normalization/transfer/omission exports. All closures are exactly `propext`, `Classical.choice`, and `Quot.sound`. The successful output is `truncation-check-v1.log`, SHA-256 `edab1458c08c72398e02194a32d2292fceca7a7a422724b886a8aa161dbe2170`.

The separately requested independent review of the coordinator's `WordEstimates.lean` and `Rates.lean` is recorded with source fingerprints in `truncation-integration-review-v1.md`. It found no mathematical or interface defect in the reviewed versions.
