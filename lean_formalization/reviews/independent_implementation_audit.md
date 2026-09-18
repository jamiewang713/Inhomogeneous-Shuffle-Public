# Independent implementation audit: F01–F15

Reviewer: the mathematical reconstruction agent, distinct from the authors of
`RiffleProfiles/Estimates.lean` and `RiffleProfiles/Entropy.lean`.

Scope: read-only inspection of those implementations against
`FROZEN_FINITE_CONTRACT.md`, the independent reconstruction report, and the
three authorized mathematical sources already read. No implementation was
edited. Compilation and kernel-axiom reports are separate checks; this report
addresses theorem meaning, assumptions, edge cases, and coverage.

## Verdict

The 28 public theorem declarations inspected are mathematically sound and
match the finite roles in the frozen contract. I found no unauthorized
strengthening of a source-model assumption, no hidden full-support premise,
and no incorrect use of real logarithms at zero. F09 and F15 are delivered by
composable finite theorems, rather than a single fully specialized statement.
The exclusions in the contract remain real exclusions: these modules do not
formalize the integral/asymptotic or shuffle-model bridges.

There is one export-level coverage distinction for F07: the final specialized
blocking estimate is public; its preceding generic triangle bound is proved
through local facts inside that proof and existing public finite-sum
inequalities, rather than exported under its own theorem name. This is not a
false statement or a new assumption, but a declaration inventory should not
list that generic form as a separate public result.

## Estimates.lean: declaration-by-declaration review

| Public theorem | Frozen role | Audit |
|---|---|---|
| `cost_eq_log_inverse` | F01 | Requires `p>0`, exactly where the source logarithm is interpreted. `-log p = log(1/p)` is proved using nonzero division. |
| `cost_nonnegative` | F01 | Requires `0<p<=1`; does not infer a logarithmic cost for a zero-mass legal digit. |
| `cost_antitone` | F01 | Requires `0<p<=q`; positivity of q follows. The inequality direction is correct. No unnecessary upper bound on q is imposed. |
| `good_digit_bounds` | F02 | Membership uses the strict representative threshold `2chi<q_j`; result is the strict actual bound `chi<p_j` and the exact regularity error. |
| `exceptional_digit_bound` | F02 | Membership is the complement of that strict threshold. Equality `q_j=2chi` is correctly exceptional and gives `p_j<=3chi`. |
| `sum_error_bound` | F03 | Exact finite absolute-sum estimate, including an empty set. |
| `normalized_sum_error_bound` | F03 | Requires `L>0` and the pointwise epsilon error. Cardinality is cast to real and divided by L correctly. No nonempty-set premise is added. |
| `good_exceptional_split` | F04 | The two filters are complementary, so the identity is exact. Allowing arbitrary L is harmless for this algebraic identity; analytic error bounds separately require positive L. |
| `exceptional_cost_nonnegative` | F04 | Uses `LegalOn` and `L>0`, precisely the positivity and upper mass bounds needed for Q to be nonnegative. It imposes no positivity on representatives of exceptional digits. |
| `profile_cost_decomposition` | F04 | Proves the exact good/exceptional error bound from regularity. Only good costs are approximated; actual exceptional costs remain untouched. Its purely algebraic validity does not require an additional legality premise. |
| `length_exponent_split` | F05 | Requires disjoint finite prefix/extension position sets. The subtraction signs and normalizations are correct. |
| `length_exponent_profile` | F05 | Combines the disjoint split and F04 with the correct sign reversal inside the absolute value. The bound counts good extension positions only. |
| `cell_regrouping` | F06 | Counts each position in its unique finite cell, without assuming those counts approximate any measure. All cells, including empty cells, are present in the finite sum. |
| `cell_replacement` | F06 | Contains both required errors: `card(s)*epsilon/L` and `sum_i |v_i| delta_i`. The target masses m_i remain arbitrary finite data. No cell-count factor is dropped. |
| `interval_blocking` | F07 | The empirical/target totals are literally displayed as whole-block sums plus remainder masses. Requires both remainder masses nonnegative and both explicit upper bounds. It proves `4rho+Tphi+(B+2)/L` exactly. The generic triangle inequality is a local intermediate result. |
| `tail_cell_replacement` | F08 | Negates both empirical and target expressions; the same absolute error is retained. No sign assumption on the representative costs is introduced. |
| `maximal_pile_domination` | F09 | Requires positive selected masses and pointwise domination by maximal masses. The negative-log antitonicity is used in the right direction. Positive L is retained. |
| `maximal_pile_target` | F09 | Correct finite algebra: combine `bound<=b-actual` and `|actual-target|<=e` to obtain `bound<=b-target+e`. F06 can supply exactly its explicit error expression; this theorem does not assume an integral approximation. |
| `side_mass_ge_continuation` | F10 | Contracts a nonnegative earlier mass by a finite product of factors in `[0,1]`, including the crossing factor when that factor is in the selected position set. The hypothesis `side>=chi*earlier` is exactly the frozen finite premise. No independence or actual-variance premise is asserted. |
| `fluctuation_log_comparison` | F11 | Retains all five frozen positivity premises for L, chi, M, U, V. Both log arguments and the product chi*M are proved positive before log monotonicity and product expansion. Divides by positive `2L` and takes the minimum in the correct direction. |
| `parent_crossing_good_cost` | F12 | Retains Q>=0, the absolute decomposition error, the parent threshold, delta>=0, and the final-step bound. Linear arithmetic gives exactly `Sx<=base-F+e+d`; no unreviewed condition on d or positivity of parent exponents is introduced. |

The structural definitions also match their finite contract roles:

- `LegalOn` is exactly selected actual mass in `(0,1]`.
- `RegularDigits` stores chi positivity and the two source digit clauses.
- `exceptionalPositions` is expressed as a negated strict filter rather than
  set difference, but is extensionally the same complement within the finite
  position set.
- `lengthExponent` is b minus the actual normalized logarithmic cost. It is
  not silently redefined as a representative-cost exponent.
- `normalizedSum` is total as a Lean real expression, but every estimate
  requiring a nonzero/positive normalization proves or assumes the reviewed
  positive-L condition.

## Entropy.lean: declaration-by-declaration review

| Public theorem | Frozen role | Audit |
|---|---|---|
| `finite_gibbs_inequality` | F13 | The probability vector is nonnegative and sums to one on the finite index set. Weights are nonnegative on the full set and positive only on positive-probability support. The positive normalizer is the full weight sum, not a truncated support sum. The proof bounds omitted weights in the correct direction. |
| `profileEntropy_eq_zero_of_sum_eq_zero` | F14 zero case | Under nonnegative counts and total zero, each count is proved zero; entropy therefore vanishes. Empty sets are included. |
| `entropy_le_tilted_cost` | F14 | Retains nonnegative counts and representatives, support positivity, theta>0, and positive full tilted normalizer. Both zero-total and positive-total branches are proved. No hypothesis `sum p=1` or full support is added. The unused theta-positivity binder remains in the theorem statement exactly as frozen. |
| `profile_entropy_le` | F15 cellwise entropy | Sums F14 over finite cells and keeps each cell's total-count multiplier and full tilted normalizer. The sign of `-psi` is correct. No count or representative cell is silently removed. |
| `exceptional_cost_identity` | F15 deletion identity | Requires the exceptional set to be a subset of the position set. The difference between the full and retained normalized costs is exactly the exceptional cost. Arbitrary L is valid for this algebraic identity; it does not replace positive L in the following estimate. |
| `exceptional_cost_bounds` | F15 deletion bound | Requires L>0 and `0<=psi<=M` on all positions. Both nonnegative loss and upper loss `M*card(E)/L` are proved. No separate M>=0 assumption is needed: the pointwise premise already suffices, including empty sets. |
| `entropy_error_of_replacement` | F15 final finite composition | From the entropy bound, deletion loss, and an explicit absolute replacement error, obtains `H<=theta*S-target+error+loss`. The signs are correct. F06 supplies the complete cell-count-dependent error unchanged; the argument makes no assertion that the target is an integral. |

## Real-zero semantics

Lean's `Real.log 0 = 0` and division-by-zero convention do not substitute for
the source's legal-word positivity in any exported semantic theorem here.

1. The finite definition `cost p=-log p` is total, as frozen. Its meaningful
   inverse-log, monotonicity, and nonnegativity properties use explicit
   positivity where required. A caller cannot use `cost_nonnegative` to
   certify an impossible zero-mass legal coordinate.
2. `profileEntropy` filters to strictly positive counts before dividing by
   them. Under nonnegative counts, a positive count implies positive total.
   The positive-total proof uses this fact and separately proved positivity
   of the representative and tilted weight at each such coordinate.
3. The final F14/F15 cross-entropy sum is syntactically over all coordinates,
   rather than filtered. This is semantically equivalent to the frozen
   support-only cross entropy: private proved helper `sum_positive_mul`
   removes precisely zero-count terms, and the zero-total branch separately
   proves the full sum is zero. Thus zero representatives outside support
   contribute zero by multiplication, not a false logarithmic identity.
4. Every use of `log(p^theta)=theta log p` in the positive-total branch has
   `p>0`. Real powers at zero outside the support are only used as
   nonnegative normalizer terms; the full normalizer has its frozen
   positivity premise.
5. Empty digits in F13 are incompatible with the probability-total-one
   premise, as expected. Empty digits in F14 are incompatible with its
   positive-normalizer premise, exactly as in the frozen statement. The
   separately exported entropy-zero theorem remains available without a
   positive normalizer.

## Coverage boundaries

No mathematical gap was found within the finite statements that these
declarations claim. The following are not exported as complete source-model
results and must stay visible in any completion report:

- The finite interval-blocking theorem consumes endpoint remainder bounds;
  it does not prove the lattice-count/grid decomposition that supplies them.
- The finite replacement target is a finite representative sum. No theorem
  identifies it with `A`, `B_theta`, or `B_2` from the paper.
- The finite side-mass lemma does not prove the fixed-column expected-count
  identity, the lexicographic side-cylinder identity, boundary crossings, or
  the maximum defining c_F. Nor does the log lemma establish endpoint
  anti-concentration or repair the deterministic-first-column issue.
- The parent-crossing theorem consumes previously derived parent and final
  step inequalities. The full stopped-word construction is outside this
  module, as explicitly stated in F12.
- F15 is a composition of the cellwise entropy theorem, deletion bounds,
  F06, and `entropy_error_of_replacement`. There is no exported theorem that
  itself constructs digit-profile counts or proves their normalized
  regrouping against the actual good-position sum.
- The shorthand R=`card(E)/L` and ambient logarithmic discrepancy are not
  separately bundled structures in these files; their concrete expressions
  are sufficient for the finite inequalities, but no ambient-block or
  asymptotic assertion follows merely from those expressions.

These are already excluded bridges or declaration-level composition facts,
not suggested contract changes. This audit approves the implementation as a
finite library and does not certify the complete macroscopic profile-estimate
or bad-profile-reduction lemmas from the paper.
