# Independent adversarial review of the expectation interface

Status: unfrozen mathematical review; no Lean implementation for this interface was made. This is a proposed finite probability bridge for the assigned ambient/cF objects, not a measurable-kernel proposal or an anti-concentration theorem.

## Source law and the representation choice

The unified TeX first specifies that S is uniform among all N-by-K matrices having the prescribed counts in every column (around lines 386–390). Its detailed first-moment setup describes each column as a uniformly permuted multiset (around lines 443–455). The deterministic model in 2510 Section 2.2 says the same thing explicitly: choose a shuffle matrix uniformly from the full set of matrices satisfying every column-count constraint, then sort its rows. The iid digits in the homogeneous 2103 model are not a permissible replacement for this fixed-count model.

For a fixed cut array, the admissible matrix set is a finite Cartesian product of the admissible column sets. Uniformity on that full product therefore supplies independence of columns. Rows in any one column are generally dependent. No independence assumption on random pile-size vectors is relevant here; the cut array is fixed. If a random pile sequence is later sampled, the present law is its conditional fixed-cut law.

I recommend the direct representation

    ColumnAssignments(cuts,j)
      = {a : Fin N -> Fin k | for every l, card{row | a(row)=l}=count(j,l)},
    Omega(cuts) = product_j ColumnAssignments(cuts,j),
    law(cuts) = uniform finite probability law on Omega(cuts).

This is exactly the source's constrained matrix set in column-major notation. It avoids a separate pushforward-uniformity theorem. Finiteness comes from the ambient finite function types. Nonemptiness must be constructed from Cuts, not passed as a new premise: for each j,

    card (Sigma l : Fin k, Fin(count(j,l))) = sum_l count(j,l) = N.

Choose an equivalence from Fin N to that dependent sum and take its first projection. Its l-fiber has the required cardinality. This works with zero pile sizes and introduces no full-support condition. Finite choice gives a full matrix. The normalized-profile conclusions use N>0; the logarithmic conclusions already use N>=2.

The alternative permutation representation is also mathematically valid:

    Omega_perm = (Fin K -> Perm(Fin N)),
    matrix(j,row) = base_j(sigma_j(row)).

However, each base_j must be constructed internally with the given counts. To identify this law with the source's uniform matrix law, it is not enough that sigma is uniform: one must prove that every admissible assignment has equally many preimages, namely the product over labels of count(j,l)!, or prove equivalent invariance/transitivity facts. Choice of base must also be shown irrelevant to the induced law. The direct ColumnAssignments model dispenses with that entire detour.

## Concrete counterexamples and required distinctions

1. **Correct one-column laws alone do not suffice.** Let N=2, k=2, K=2 and both columns have one zero and one one. Choose a fair random balanced column and repeat that same column twice. Each individual column is uniform with the right counts, but the number of rows equal to 00 is always one. The claimed independent-column product mass is 2*(1/2)^2=1/2. Thus the law must be uniform on the full product, not a coupling having only uniform marginals.

2. **There is no row independence.** With one balanced column and N=2, the probability that both rows have digit zero is zero, not 1/4. First moments use linearity of expectation across rows, which needs no row independence.

3. **The row marginal applies before sorting.** With that same single balanced column, the first lexicographically sorted row is always zero. Its digit probability is not 1/2. Exchangeability and the one-row product argument must be applied to the original labelled rows. Transfer to the source's sorted interval cardinalities uses invariance of occupancy cardinality under a permutation of rows.

4. **Later digits of a lexicographic side piece are free.** Take N=4, two balanced binary columns, ambient length zero, x=(1,0), and split at the first column. The source left piece includes all rows whose first digit is zero, so its size is exactly two. Requiring the later digit to agree with x would instead select the prefix 00 with expected size one. The existing sideMass equals two and matches only the source's unconstrained suffix.

5. **The side index must follow the ambient prefix.** With N=4 and a balanced first column, take ambient length w=1, x[0]=1, and incorrectly choose zero-based side index j=0<w. Extending the ambient prefix and having digit less than one at that same column are mutually exclusive, so the event has count zero. Yet the existing sideMass expression is (ambient mass two)*(left probability 1/2)=one. The source restriction M_w<i becomes exactly w<=j.val and is essential.

6. **Ambient restriction is not a new conditional law.** The source b refers to the unconditional expected cardinality of a fixed ambient prefix. The side event counts global rows that satisfy the ambient restriction as well as the later side condition. Replacing that count by a conditional probability given one row belongs to the ambient block, or by a process with a fixed realized ambient size, loses the ambient probability factor. A later conditional-exploration theorem is a different interface.

7. **Maxima and nonlinear operations stay outside expectation.** The source cF uses the maximum of expected side counts, then square root and logarithm. It is neither the expectation of a random side maximum nor the expectation of a random cF. Those operations cannot be interchanged.

8. **Random-pile mixing does not remove dependence.** If random columns have correlated pile sizes, the unconditional cylinder mean is the average over cuts of N times the product of their normalized probabilities. It is generally not N times the product of the averaged one-column probabilities. This interface should stay conditional on the deterministic cuts.

## Exact derivation

For a fixed column j, precomposition by any row permutation is an equivalence of ColumnAssignments(cuts,j), preserving the count constraints. Uniform measure on that finite type is invariant under this equivalence. A swap sends any designated row to any other, so for every label l all labelled-row indicators have the same expectation q_l. The count constraint holds pointwise:

    sum_row 1{column(row)=l} = count(j,l).

Taking expectations and dividing by N>0 gives

    Pr(column(row)=l) = count(j,l)/N.

More generally, for any finite label set D, its one-row probability is the sum of count(j,l)/N over l in D. Zero-count labels have probability zero, without an extra hypothesis.

Uniformity on the finite dependent product gives, for arbitrary real functions g_j on the column assignment types,

    E(product_j g_j(omega_j)) = product_j E(g_j).

This can be proved by finite Cartesian-product summation and the product formula for cardinality; no external independence premise is necessary. All finite functions are integrable under the discrete uniform law. The arithmetic average should be connected to the actual PMF/measure expectation, for example using the trusted finite uniform integration theorem, rather than merely naming an unconnected average an expectation.

Let x be the existing complete digit array and 0<=M<=K. Define the prefix occupancy as the number of original labelled rows agreeing with x at every column j.val<M. For each row its event probability is the product over those columns of p_j(x_j). Thus

    E(prefixOccupancy(x,M))
      = N * product_{j in positions(K,0,M)} p_j(x_j)
      = prefixMass(N,p,x,M).

No legality premise is needed for this expectation identity: an impossible selected digit gives both sides zero. Legality is needed later for positivity and a real logarithm, exactly as in the existing finite contract. At M=0 the empty condition counts every row and the mean is N; at K=0 this is the only source prefix length.

For the source side family at zero-based index j, with w<=j.val<M<=K, the event for a labelled row is:

* it agrees with x on columns before w;
* it agrees with x on columns h with w<=h.val<j.val;
* its digit at j is less than x_j for the left side, or greater than x_j for the right side;
* all columns after j are unconstrained.

The first two conditions are compatible because the same digit array represents the ambient prefix and its extension. They are exactly agreement on all columns before j. Therefore

    E(leftSideOccupancy(x,w,j))
      = N * product_{h< w} p_h(x_h)
          * product_{w<=h<j} p_h(x_h) * sum_{l<x_j} p_j(l)
      = sideMass(N,p,x,w,leftProbability,j),

and the right formula uses the sum over l>x_j. Future columns contribute one, so the quantity is independent of M once j<M. Empty left/right label sets give zero. If an earlier selected coordinate is zero, both sides are zero. No full support, crossing, or positive-side premise is needed.

Every digit that actually appears in a valid column has positive prescribed count, witnessed by the row itself. Thus every sampled full row is a legal full string. This bridges the event formulation above to the source's side families of legal prefixes: imposing legality adds no restriction on the sampled rows.

For any property of full rows, its occupancy cardinality is invariant under an arbitrary row permutation. This finite statement transfers the preceding equalities to the lexicographically sorted representation used by the source's |I(B)|. It does not claim sorted labelled rows themselves have the original marginal law, and it does not require an order-statistic distribution theorem. If an actual lexicographic sorting function is not part of this layer, the contract should explicitly expose row-permutation cardinality invariance and avoid claiming to have formalized sorting or the shuffle graph law.

## Consequences for the already-frozen objects

Substitute the prefix expectation identity into the existing exact mass-exponent theorem. For N>=2 and a legal extension w<=M<=K,

    log(E(prefixOccupancy(x,M)))/log N
      = cL(b,w,M) + (log(E(prefixOccupancy(x,w)))/log N - b).

This makes the existing explicit ambient approximation precisely the source's expected-size approximation; it does not add an asymptotic assumption.

For each j in positions(K,w,v), substitute the two side expectation identities into the finite side maxima. Since all expected cardinalities are nonnegative, NNReal coercion loses nothing. The source's max-of-expectations, square roots, and extended logarithms then agree with the existing cF definition. The empty index case w=v gives both maxima zero and cF=bottom. One-sided zero cases likewise retain bottom. No positivity hypothesis is needed for the extended-valued identification.

This exact identification will not repair anti-concentration. In particular, the previously reported deterministic-first-column counterexample persists after the expectation bridge is proved; the source quantity really has that value.

## Proposed bounded inventory for three-way comparison

1. Internally construct nonempty admissible column types from Cuts; form the finite uniform dependent-product matrix law and prove its column counts.
2. Row relabeling equivalences preserve the constrained column types and uniform averages; derive one-row label/set probabilities from count conservation.
3. Prove finite-product factorization for the defined full matrix law; no column-independence hypothesis is passed by the caller.
4. Prove the prefix occupancy expectation equals prefixMass, including empty and zero-probability cases.
5. Prove sampled rows are legal, and that occupancy cardinality is unchanged by arbitrary row permutation.
6. Prove the two source side occupancy expectations equal sideMass under the exact side-index bounds, with suffixes free.
7. Identify the source ambient expected-mass exponent and the extended cF expression with the existing definitions, preserving empty/zero maxima and the exact frozen errors.

These are sound source-supported targets. They can be frozen without a measurable-time-law assumption, full support, independence across rows, an arbitrary base-column premise, or a change to any earlier definition. I will review the exact proposed Lean-facing contract before implementation.

## Verdict on the exact P01–P08 draft

I read every definition and every item of `EXPECTATION_EXTENSION_DRAFT.md`, then re-read it after the observed-row legality and noncircular P02/P03 order were added. **The exact P01–P08 inventory is mathematically approved. No new scientific hypothesis or repair is required.**

* **P01 approved.** The column-type construction covers all natural k,N,K for which Cuts exists, including zero piles and empty rows/columns. Uniform probability is concrete. Positive count for an actually observed digit is witnessed by that row in the finite fiber. The existing normalized `LegalPrefix` formulation uses N>0; this is either stated for that projection or derived from an existing row i:Fin N. Finiteness/nonemptiness of the sample law itself needs no N>0 restriction.
* **P02 approved.** Column marginal expectation for an arbitrary real g follows by row-swap symmetry and count conservation, without any sign or boundedness premise because the sample type is finite. All count/N ratios are real normalized profile probabilities. The full-matrix marginal may follow after P03. No assertion is made for sorted row positions.
* **P03 approved.** Uniform dependent-product factorization is exact, including the empty product. It derives column independence from the defined law, with no extra field. The separate column-law expectations avoid a circular appeal to a full-matrix marginal.
* **P04 approved.** The row-event indicator factors across columns, and summing over rows uses expectation linearity only. Empty digit sets give zero; an empty column family imposes no row condition and gives N. Zero-count labels remain allowed.
* **P05 approved.** The expected-prefix identity requires no legality; the logarithmic corollary uses precisely D04's existing N>=2, ordered lengths and legality. It preserves the signed ambient exponent discrepancy and adds no b>=0 condition.
* **P06 approved.** The newly defined side row sets match the source once w<=j.val. Their definitions leave all later columns unrestricted. The identity is unconditional and includes zero sides. The lack of a separate M parameter is legitimate: the source occupancy is independent of M for every j.val<M<=K, because observed row suffixes are legal and unrestricted.
* **P07 approved.** It compares deterministic maxima of expected row counts with sideMaximum, then applies the same square-root/extended-log operations. The empty and zero cases are retained. No positivity or variance premise has been added.
* **P08 approved.** Cardinality equality holds separately for each sample and each row permutation, so the permutation may depend on the sample. This is exactly what is needed for the sorted interpretation and does not require an independent sorting permutation. The statement correctly stops short of a shuffle-graph or localization theorem.

The exact draft includes all the traps identified above. I checked the subsequent explicit N>0 typing clarification for normalized observed legality; it is now present in P01. The corrected draft is approved for a separate freeze. No Lean implementation preceded this approval.

## Implementation check after the expectation freeze

I independently read the actual `FixedCountModel.lean` and `FixedCountMoments.lean` implementations against frozen P01–P04. The finite probability law is the uniform law on the dependent product of exact prescribed-count subtypes. Nonemptiness is constructed from the count sum, all real functions are proved integrable, and the finite average is explicitly identified with the ordinary measure integral. The row marginal uses a swap equivalence and pointwise column count conservation. Product factorization uses the Cartesian-product sum and cardinality formulas. Expected box occupancy sums labelled-row indicators and factors each one-row event across columns. No row independence, full support, auxiliary base-column premise, time measurability, or extra positivity premise is present. The source-law interpretation passes the adversarial audit.

I implemented P05–P07 in `ExpectedMass.lean` only after the separate expectation freeze and the three independent reviews. Its complete module compiled successfully against the proved P04 identity. The prefix formula permits impossible cylinders; the logarithmic corollary preserves D04's exact legality and ordered-prefix assumptions; both side formulas explicitly require `w <= j.val` and leave all later digits free. Expected side maxima use the existing nonnegative supremum convention and extended logarithm. No random maximum is moved through expectation. The source-domain premises `M <= K` and `w <= v <= K` remain in the public statements even where the finite algebra proves more. The independent Lean-design reviewer and parent separately approved these public statements and definitions.

These identities close the previously identified expected-mass semantic obligation for `prefixMass`, `sideMass`, `cL`, and `cF` under the fixed-cut source law. Row-permutation cardinality invariance is the separately owned P08 bridge to the source's sorted representation. None of these results changes or repairs the unrelated source anti-concentration counterexample, the missing two-sided time-integral regularity, or the loss of exceptional digit values in the unified coarse profile.
