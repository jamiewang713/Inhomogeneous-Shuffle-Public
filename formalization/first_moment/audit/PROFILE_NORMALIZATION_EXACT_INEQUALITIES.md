# Exact profile-normalization candidate: adversarial sign-off

**Approve the exact two definitions and PN1–PN8 without corrections.**

Reviewed candidate: `audit/PROFILE_NORMALIZATION_STATEMENTS.md`, SHA-256 `73ad2a8eed5d8938daab619c740891b806cb1ff48c01ec028d8d0774bf641f7d`. I reread the authorized article's normalized good-count, exceptional-set, entropy, and within-class counting passages and checked the actual project definitions, including the current `asProfile`/`legalVector` definitions and the nested `ProfileWord` proof fields. This report is a pre-freeze interface review, not a claim that new declarations have been compiled. No code or contract was changed.

## Definition and interface decisions

| Item | Decision and exact check |
|---|---|
| `sourceCell` | Approve. It combines precisely `timeClass j` and `P.classify (asProfile D j)` using `finProdFinEquiv`. Its codomain is `Fin (R*P.cellCount)`, so the later cell/digit key dimension is `(R*P.cellCount)*D.k`. |
| `sourceGood` | Approve. The existential bound on the natural digit creates exactly the corresponding `Fin D.k` digit. An arbitrary real `chi` is valid identity data; no statement equates it with `A.chi` or claims regularity. |
| PN1 `sourceGood_fin_iff` | Approve. Forward direction uses equality of finite digits with the same natural value; reverse direction uses `l.isLt`. Its listed data are exactly `D P chi j l`; there is no setup, time class, legality, or regularity premise. |
| PN2 `exceptionalPositions_source_eq` | Approve. Both filters use `join.length≤j.val<x.length`. At such a coordinate `legalVector_digit` and PN1 identify the good predicate. The legal-prefix bound excludes padding. No relationship between `y,z` and `x` is required for this literal set equality. |
| PN3 `digitCount_source_eq` | Approve. The triple is right-associated, so `a.1`, `a.2.1`, and `a.2.2` are respectively the time cell, simplex cell, and digit. Injectivity of `finProdFinEquiv` identifies the two cell conditions. The natural numerator and the positive logarithmic denominator match exactly. |
| PN4 `profileR_source_eq` | Approve. It is PN2 under cardinality and the existing `profileR` definition. It introduces no alpha or positivity-of-count assumption. |
| PN5 `profileH_source_eq` | Approve. The proposed proof-local normalized-count identity, followed by the outer joint-cell equivalence, yields precisely the existing `typeEntropy` divided by `log N`. No analytic or support-positivity hypothesis is missing. |
| PN6 `profileWord_profileR_le` | Approve. PN4 and the actual real cutoff `p.property.2.2`, divided by the logarithm whose positivity follows from the model, give the conclusion for any real alpha. Neither a route nor timeClass is involved. |
| PN7 `profileWord_profileH_key` | Approve. PN5 at the actual triple and the proved function equality `profileKeyCounts_encode` rewrite the natural counts to the exact realized key. The cardinal dimension and the key projection are correct. Arbitrary fixed route data cause no issue. |
| PN8 `profileFibre_card_le_rpow_profileH` | Approve. The existing PF4 applies to the printed actual fibre at `keyp`; PN7 rewrites its exponent. Its domain is the same `ProfileWord A (sourceGood D P chi) alpha` as the route and `p`. No finite instance, count compatibility, or separate nonemptiness premise has been inserted. |

## Derived legality and proof projections

For the exact existing subtype `p : ProfileWord A (sourceGood D P chi) alpha`:

- `p.val.1`, `p.val.2.1`, and `p.val.2.2` are the left boundary, right boundary, and stable word.
- `p.property.1` is their `Riffle.AdmissiblePair` proof.
- `p.property.2.1` is the stable-word membership proof.
- `p.property.2.2` is the original **real** exceptional-count cutoff.

Thus `Riffle.admissiblePair_rawPair p.property.1` supplies exactly the raw pair needed by `Riffle.stable_desc`. The latter returns membership in `Desc D (join ...)`, whose first field is legality. The candidate's displayed `hpLegal` term has exactly the required type, without adding a new proof argument. Its `Xp`, `vp`, and `np` use the actual stable word and actual join endpoints. `keyp` is the existing encoder at the same cell map, good predicate, alpha, route, and word. No projection correction is needed.

## Normalization schema

The proof-local schema is valid for arbitrary natural counts, including incompatible counts and `d=0` or `k=0`. Let `L>0`, `n_l` be a cell's natural counts and `T=sum_l n_l`. Positivity of `n_l/L` is equivalent to `n_l>0`. In that branch `T≥n_l>0`, so cancellation gives

`(sum_q n_q/L)/(n_l/L) = T/n_l`,

and the logarithm quotient identity has its required positive arguments. Multiplying by `n_l/L` and summing gives `(T log T - sum_l n_l log n_l)/L`. Zero counts give zero terms; if `T=0` every count in that cell is zero. The complete normalized formula follows by finite distributivity.

The hypothesis `L>0` belongs only to this generic algebraic fact and is already derived as `Real.log_pos` from `D.one_lt_N` in PN5. No new model premise appears. There is no unexplained `log L` term: that scale cancels in each ratio. The arbitrary sign of chi does not enter any step of this normalization.

The product-index reindexing is also exact. TimeProfile sums over `Fin R × Fin P.cellCount`, while `typeEntropy` sums over `Fin (R*P.cellCount)`. The reviewed equivalence is between those two types. The digit remains a separate `Fin D.k` index. No equality between `Fin ((R*P.cellCount)*D.k)` and `Fin (R*(P.cellCount*D.k))` is assumed.

## Edge and adversarial cases

- **Arbitrary chi:** if chi is negative, representative coordinates of value zero may count as good; both definitions use the same strict threshold, so the identities still hold. If chi is large, all positions may be exceptional; the identities then have zero good counts and zero H. Neither case invokes a cost logarithm at a representative coordinate.
- **Digit-dependent goodness:** PN2 and PN3 compare each word with its own digit. No common good-position set is asserted across unrelated words. In PN8, the existing fibre result already fixes exceptional supports and labels through key equality.
- **Negative alpha:** the real cutoff is impossible for negative alpha because the exceptional count is nonnegative and `log N>0`. PN6 is a theorem for an element of that domain, so it remains valid without a sign premise. Replacing the cutoff by its zero natural floor would be invalid, but the proposed statement does not do so.
- **Zero counts/cells:** zero-count branches agree exactly with the zero-weight convention in `typeEntropy`; no positive total is silently assumed. Arbitrary empty or unrealized natural count arrays in the proof-local schema are harmless.
- **Empty intervals:** when the join length is at least the word length, all counted sets are empty. PN2–PN5 remain valid even for arbitrary incompatible boundary words. Terminal and stopped-root profile words give the familiar `H=R=0` instance.
- **Empty horizon or zero R:** a time-class map into `Fin 0` has data only when its domain is empty. No additional `0<R` premise is needed. Empty function/count types give zero entropy. An actual source mesh may later supply a positive R, but it is irrelevant here.
- **Padding/zero piles:** no filter includes a coordinate at or beyond the legal list length. The possibly illegal padded zero suffix is never counted.
- **Realized fibre:** PN8 evaluates the fibre at the actual encoded key `keyp`, so it does not try to assign a TimeProfile word entropy to an arbitrary unrealized key. Its explicit `p` is data, not an extra assumed nonemptiness field. PF4 continues to cover arbitrary empty fibres separately.
- **No hidden source strengthening:** the finite identity layer may use chi independently of the stable setup's boundary threshold. Setting chi to `A.chi` in the source application specializes valid identities; it is not a missing equality premise. No exact cL constancy, density estimate, or conditional variance assertion follows from PN1–PN8.

The candidate's helper schemas and all eight interfaces are valid with exactly the stated binders. I request no correction before freeze.

