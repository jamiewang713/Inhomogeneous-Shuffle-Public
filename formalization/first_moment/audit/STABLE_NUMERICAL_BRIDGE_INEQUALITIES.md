# Stable-block to numerical-data bridge: adversarial integration review

This is a read-only mathematical/interface review of the authorized article and the current project Lean sources. It does not freeze a new statement, change an existing assumption, or certify a new build. In particular, the scalar conclusions in `TimeProfile.SourceNumerical` are not a proof of the disputed stochastic edge-density estimates.

## Conclusion

The list-based stable blocks can supply the stopping, crossing, legality, and prefix-order premises of the existing numerical theorems without a new model assumption. Several exact representation/expectation identities still need to be proved. The ambient exponent approximation and the horizon relation are genuine source inputs: neither follows from `Riffle.Setup` or `Riffle.Model` alone. Terminal singleton pairs must remain a separate branch. The existing theorem `Riffle.gamma_first_crossing` already supplies the strict length inequality needed for `TimeProfile.ParentCrossing` in the non-singleton branch.

## Data and exact identities needed

Write `m = A.w.length`, `v = (Riffle.join y z).length`, `n = x.length`, and let `omega : Fin D.K → Fin D.k` extend the legal list word `x`.

1. **Columns.** Define the finite cut array by `cuts.count j a = D.n j.val a.val`. Its `sum_count` follows from `D.sum_counts` and `Fin.sum_univ_eq_sum_range`. Prove the real probability identity
   `TimeProfile.prob (cuts.profile hN j) a = (Riffle.prob D j.val a.val : ℝ)`.
   The positivity conversion is supplied on each side by `Riffle.prob_pos_iff` and `TimeProfile.Cuts.profile_pos_iff`. `D.one_lt_N` and `D.two_le_k` supply the numerical theorem's `2 ≤ N` and `2 ≤ k`.

2. **List/full-function words.** A legal list has a legal full extension by `Riffle.full_extension`; a full list has its unique `FullIndex` representative by `Riffle.fullList_of_full`/`fullList_existsUnique`. Using `Riffle.digit_prefix` and `fullList_digit`, prove that an extension representative agrees with every list digit below `n` and satisfies `TimeProfile.LegalPrefix (cuts.profile hN) omega n`. No positivity of an arbitrary padded tail is needed for a theorem using only `LegalPrefix ... n`. If full legality is wanted, use the existing full-extension theorem rather than padding by digit zero: zero piles are permitted.

3. **Finite intervals.** Identify the natural interval `Finset.Ico a b` with `TimeProfile.positions D.K a b` whenever `b ≤ D.K`, preserving sums, products, cardinalities, and finite suprema. Both are zero-based half-open intervals. The paper's column `j` is Lean coordinate `j - 1`; the paper's range `M_w < j ≤ M_x` becomes `[m,n)`. `TimeProfile.columnTime N j` is `(j.val+1)/log N`, while a prefix of length `n` has time `n/log N`.

4. **Cost.** For `A.w <+: x`, prove
   `Riffle.cL A x = TimeProfile.cL D.N p omega A.b m n`.
   The digit identity is `log(N/n_i) = digitCost(n_i/N)`; the summands and normalization are otherwise identical. The same identity at `parent x` uses length `n-1` and agreement below that length. `Riffle.cL` divides the whole sum, as does `TimeProfile.cL`.

5. **Cylinder expectation.** Prove
   `(Riffle.expectedCount D (Riffle.Cylinder D x) : ℝ) = TimeProfile.prefixMass D.N p omega n`.
   The existing `Riffle.expectedCount` is a finite product-marginal sum, not yet an integral of a matrix row count. Illegal full words have weight zero by `Riffle.weight_eq_zero_of_not_legal`; consequently filtering to `Full` cannot change the product cylinder sum. Summing the unrestricted suffix gives one by the column normalization. The actual fixed-column stochastic identity is independently available as `TimeProfile.expected_prefix_count`; matching the row predicate then identifies these two expectations.

6. **Side-piece expectation.** For `m ≤ i < n`, prove that the Riffle piece event is the full-row predicate “all digits before `i` agree with `omega`, and the digit at `i` is smaller/larger.” Use `Riffle.pieceEvent_iff`, which also handles the ambient-prefix constraint. Later columns are unrestricted; do not accidentally impose the later digits of `x`. Then prove
   `(Riffle.expectedCount D (Riffle.PieceEvent A s x i) : ℝ) = TimeProfile.sideMass D.N p omega m side i`.
   The left/right stochastic versions already exist as `TimeProfile.expected_left_side_count` and `expected_right_side_count`, with the exact premise `m ≤ i`. This is a maximum of expectations, not an expectation of a maximum and not a variance.

7. **Fluctuation.** Using the finite-supremum reindexing, nonnegative side masses, and the common `sqrt`/zero-log convention, identify Riffle `sideMaximum`, `sideFluctuation`, `cFAt`, and `cF` with the TimeProfile quantities. The equality must hold in `WithBot ℝ`, including a zero side. `TimeProfile.expected_side_maxima_eq` and `expected_cF_eq` already identify the TimeProfile deterministic quantities with its fixed-column expectations; they do not by themselves identify the separate Riffle datatypes.

8. **Continuation invariance.** Riffle already proves `pieceEvent_continuation`, `sideMaximum_continuation`, `sideFluctuation_continuation`, and `cFAt_continuation`. TimeProfile proves `sideMass_prefix_eq` and `cF_prefix_eq`. These make the `cF` obtained using a full extension of `x` equal to the one obtained from a full extension of `join y z`. Prefix mass at `m`, costs at any length at most `n`, and profile data through `n` must likewise be shown independent of the selected extension. Thus a single ambient approximation and a single real fluctuation value work uniformly for all continuations.

The Riffle stable-block package currently has no separate `cE` definition to identify. The source tail exponent can be represented directly by `TimeProfile.cE D.N p n`; any new list-facing alias should be separately reviewed rather than presented as an existing theorem. It depends on `n` and the columns only, and `TimeProfile.cE_terminal` gives its value zero at `n = D.K`.

## Crossings: what follows, and the terminal distinction

For a nonterminal `RawPair A y z`, `Riffle.boundary_nonterminal` gives a genuine left crossing at `i = y.length - 1` and a genuine right crossing at `j = z.length - 1`, both after the ambient prefix. `rawPair_prefix_join` and `stable_desc` transport the digits to `omega`. `leftIndex_mem`/`rightIndex_mem` give mass at least `A.chi` to an alphabet digit strictly on the appropriate side. The corresponding side probability is at least that one summand. Therefore both witnesses lie in `positions K m v`, proving `TimeProfile.Crossings p omega m v A.chi`.

This needs no `LocalGood` assumption, no admissibility-budget bound, and no extra retained/finite-fluctuation assumption. `AdmissiblePair` supplies `RawPair` through `admissiblePair_rawPair`. Moreover `rawPair_retained`, `admissiblePair_retained`, `rawPair_cF_ne_bot`, and `retained_nonterminal_finite` are already proved. `TimeProfile.cF_lower_bound_of_crossings` gives the quantitative lower bound after the ambient error is supplied; Riffle positivity alone is not that quantitative inequality.

Do not infer `Crossings` from an arbitrary retained pair. For example, take one column with two equal positive piles, empty ambient prefix, and `y=z=[0]`. The left boundary is its no-crossing fallback, the right boundary crosses at the final column, the pair is admissible and terminal, and its left side mass is zero. Hence `cF = ⊥` and the left `Crossings` witness does not exist. Conversely, with one uniform ternary column and `y=z=[1]`, both sides genuinely cross at the final column. Terminality does not mean “no genuine crossing.” Both are valid terminal singleton cases.

Genuine crossing at the final coordinate is correctly included: its index is `K-1`, which is less than the prefix length `K`. It must not be dropped by replacing the source range `M≤K` with `M<K`. The numerical definitions allow `n=K` and `v=K`. Nonterminality is used to guarantee two crossings from the boundary construction, not because the scalar inequalities fail at the terminal index.

## Stable/parent premises and branch order

`TimeProfile.StableAt` is the relaxed inequality `cL-F ≤ delta`. The source and Riffle stop test is strict. Once `cF = ↑F`, `Riffle.stop_iff_sub_lt` gives `cL-F < delta`, which implies `StableAt`. The converse is false at equality and must not be used to redefine the original stopping family.

For the non-singleton branch assume `¬Terminal D y z` and `¬Stop A y z (join y z)` and then split membership in `Stable` into `Gamma` or `Lambda`. In the Gamma branch, `Riffle.gamma_first_crossing hp hroot hx` already proves

- `v < n`, hence `0<n` and `v≤n-1`;
- legal ambient descent of `parent x`;
- `¬Stop A y z (parent x)`.

Together with `not_stop_iff_sub_ge` and the cost identity at `parent x`, these are exactly `TimeProfile.ParentCrossing`. No new parent-size hypothesis is needed.

It is invalid to claim `ParentCrossing` from unrestricted Gamma membership. A concrete example is `N=9`, `K=2`, three equal piles in both columns, `w=[]`, `b=1`, `chi=0.1`, `delta=0.3`, and `y=z=x=[1]`. Then `cF=1/4`, `cL(x)=1/2`, and `cL(parent x)=1`. Thus `x∈Gamma`, but `x=join y z` and `v≤n-1` is false. Here the stable definition uses its stopped-root singleton branch, precisely as it should.

Do not equate “non-singleton branch” with a cardinality condition `card Stable>1`. A later stopping family can have only one legal continuation. The relevant distinction is the branch of the source definition: terminal or stopped root versus a proper first crossing/fallback.

## Terminal fallback and singleton route

For a nonterminal pair and `x∈Lambda`, `Riffle.lambda_full` supplies a full legal word. Nonterminal boundary crossings provide the TimeProfile `Crossings` premise. Under the existing source analytic inputs, ambient approximation, and its explicit error budget, `TimeProfile.source_no_terminal_fallback` gives a real `F` with the correct `cF` and the strict inequality `cL(K)-F<delta`. Through the exact `cL`/`cF` maps this contradicts Lambda's `¬Stop`. This proves exclusion; it must occur before asserting that every nonterminal stable word satisfies `StableAt` or belongs to Gamma.

The no-fallback theorem needs full legality, positive `delta`, and its own budget. These are supplied respectively by Lambda/full extension, `A.delta_pos`, and the source parameter choice. It does not require the exceptional-profile cutoff or admissibility budget. Any separate real `F` already selected from the same `WithBot` equality is equal by injectivity of coercion; an additional equality assumption is unnecessary.

Terminal pairs have `Stable={join}`, even when `cF=⊥`. The stopped-root nonterminal branch also has `Stable={join}`. `TimeProfile.source_singleton_margin` is the correct scalar entry point for both: it requires no `Crossings`, finite `cF`, ambient mass error, stable predicate, or exceptional-profile bound. It concludes `cL(v)+cE(v)≤-eta/2`; multiplying by two supplies the exponent used by the singleton square-density estimate. This does not itself prove that probabilistic density estimate. At a terminal singleton, `v=K` by `Riffle.terminal_iff_join_length`, and `cE(K)=0` exactly.

The ambient-full case `m=K` remains valid: `Riffle.stable_ambient_terminal` gives the singleton `{w}` and both side maxima are zero. No extra assumption `m<K` or `K>0` should be introduced merely to avoid it.

## Genuine source inputs that cannot be derived from the setup

`Riffle.Setup` stores an arbitrary real `b`; it contains no relation between `b` and the product mass. The exact identity is

`log(prefixMass(n))/log N = cL(n) + (log(prefixMass(m))/log N - b)`.

It is proved as `TimeProfile.cL_exact_mass_exponent`, and its actual stochastic version is `cL_expected_mass_exponent`. For `w=[]`, the actual ambient exponent is one, whereas Setup permits `b=0`; setting the offset to zero would already fail at the empty prefix. An adapter must retain the source finite bound `abs(log expectedCount(Cylinder w)/log N-b)≤eb`, or derive it eventually from the source's ambient assumption `E|I(B_w)|=N^(b+o(1))`. It must not replace `A.b` by the exact logarithm, because that would also change the stopping family and the variational hypothesis.

Similarly, Setup contains no nominal time `r`; the source gives `abs(m/log N-r)≤er` eventually. `AmbientApproximation` is precisely the pair of these finite bounds. Since every relevant word extends the same `w`, the same bounds apply to all continuations after proving prefix-mass invariance. Pointwise errors for individually chosen ambient blocks are not automatically uniform over an additional varying family of ambient blocks.

`Riffle.Model` permits an arbitrary depth `D.K`, but all `source_*_margin` theorems take `Cuts k N (horizonDepth N T)`. Use a model constructed from those cuts, or transport along the explicit source equality `D.K=floor(T log N)`. Do not silently add extra columns, truncate legal words, or assert this equality for a general Model. The terminal scaled time is `K/log N`, not literally `T`; its discrepancy is less than `1/log N` by `horizonDepth_error`.

The source prose asserts `r≤s≤u`, although its ambient condition is only `m/log N=r+o(1)`. The implemented numerical theorems correctly use `max r (v/log N)` and `max r (n/log N)` internally and absorb the discrepancy. An adapter should retain their conclusions and budgets rather than invent the stronger inequality `r≤v/log N`.

There are two unrelated constants named `C`: `A.C` is the boundary-admissibility budget constant, whereas `P.IsRegular chi C` uses a regular-partition oscillation constant. Their equality is neither needed nor established. Keep them distinct in any combined statement.

## Profile and uniformity inputs to the large/small margins

The profile encoder permits arbitrary fixed position cells and digit-dependent goodness. To apply `source_large_margin`/`source_small_margin`, instantiate these with the same `P`, `chi`, column profile, and time-class function as the TimeProfile profile: the combined cell is `(timeClass j, P.classify(p j))`, and good means `2*chi < prob(P.rep(P.classify(p j))) digit`.

The source exceptional range is exactly `[v,n)`. For legal words the profile-word real cutoff `#exceptions≤alpha*log N` gives `TimeProfile.profileR≤alpha` by division by positive `log N`. Do not replace the original real cutoff by a floor predicate when `alpha<0`; the counting construction deliberately retains the real predicate. The numerical application chooses the source's nonnegative `alpha`, and its scalar theorems state that premise explicitly.

An exact entropy identification is also needed: with the combined cell reindexing, `typeEntropy(profileKeyCounts key)/log N = TimeProfile.profileH ... v n` on that realized fibre. Counts are raw naturals in the first-moment package and normalized by `log N` in TimeProfile. Exceptional positions and their values, boundary codes, and length are fixed by the key; arbitrary unreached keys need not represent any source profile. No exact `cL(x)` constancy follows from a key, since actual column probabilities can vary within the same regular partition cell. The numerical conclusions must be applied uniformly to every represented word, or with a proved common upper bound; they must not substitute a representative's exact `cL` throughout the fibre.

`source_large_margin` requires `StableAt` and gives `4cL-F+2cE+H≤-eta/2`; it does not mathematically need the probabilistic route's lower size threshold. `source_small_margin` requires `ParentCrossing` and gives `-F+2cE+H≤-eta/2`. The latter scalar result remains valid even though the previously audited printed small-density input is false. The uniform parameter theorem chooses its thresholds before the cut arrays and words; replacing its explicit budgets by a newly assumed “small error” would lose that quantifier order.

## Remaining obstruction after these bridges

Once these identities are proved, actual retained stable words can instantiate the existing scalar and entropy theorems without strengthening the model. This does not supply the missing localization/multiplicity estimate or valid large-block probability bound. In particular, identifying the side maxima with expected side counts does not identify them with conditional hypergeometric variance. Deterministic endpoint counterexamples to that inference, and to the printed large/small density estimates even under the variational margins, remain applicable. The fixed-count moment results and the proposed small-block first-moment-square route can be used separately; a valid large-block stochastic argument is still required for the final expected common-edge theorem.

