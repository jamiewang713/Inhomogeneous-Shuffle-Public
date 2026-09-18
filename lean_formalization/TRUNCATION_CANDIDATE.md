# Candidate finite truncation and model connections

This batch applies unchanged F16–F20 to the actual boundary definitions and
the existing independent fixed-column sampling law. It does not resolve the
pending time-measurability question or change any existing frozen definition
or assumption. These statements require three independent reviews and a
separate freeze before implementation.

Use the existing `Riffle.Model`, `Setup`, `Boundary`, `Admissible`, `selected`,
`FullIndex`, `fullList`, `weight`, and `expectedCount` from
`formalization/stable_blocks`. Let

- `p_D(j,a) = (Riffle.prob D j.val a.val : Real)`;
- `tau(A) = A.C / log(1/A.chi) * log(D.N)`;
- `bad(A,left,j) = {a : Fin D.k | a.val < leftIndex A j.val}` and
  `bad(A,right,j) = {a | rightIndex A j.val < a.val}`;
- `discarded(A,side) = {x | x in Cylinder D A.w and
  selected A side x not in Admissible A side}`.

All model and setup fields remain exactly as defined. In particular, N>1,
k>=2, column counts summing to N, ambient legality, positive C and delta,
and `0<chi<1/k` are existing source data, not new assumptions.

## T01: product functional and normalized columns

Prove coordinate nonnegativity and `sum_a p_D(j,a)=1`; prove
`coe(weight D omega)=wordWeight p_D omega` and, for every set E of words,

`coe(expectedCount D E)`
` = N * sum_omega (if fullList omega in E then wordWeight p_D omega else 0)`.

These are exact identities, without a stochastic interpretation being
assumed. Construct `modelColumnProfile D j : TimeProfile.Simplex D.k`
with coordinates `p_D(j,a)` using those normalization facts.

## T02: finite bad-event bound

For any finite bad-digit family, natural threshold h, nonnegative a, and
coordinate bad mass at most a, let E be any set satisfying
`fullList omega in E -> h<=badCount bad omega` for every full index omega.
Then

`coe(expectedCount D E) <= N * tailWeight D.K h a`.

This is the existing finite F18 estimate after a proved event inclusion.
Neither column independence nor row independence is added as a premise.

## T03: actual inadmissibility implies many small digits

Prove `0<tau(A)`. Every digit in `bad(A,side,j)` has mass `<A.chi`.
For every full index omega with `fullList omega in discarded(A,side)`,

`Nat.floor(tau(A))+1 <= badCount (bad(A,side)) omega`.

Use the actual selected prefix, prefix digit equality, and containment of
its violation positions in the full set of positions. The strict real
threshold becomes floor+1; terminal and empty ambient extensions are included.

## T04: boundary truncation

For each side,

`coe(expectedCount D (discarded(A,side)))`
` <= N * tailWeight D.K (Nat.floor(tau(A))+1) (D.k*A.chi)`.

The union of the two discarded events has at most twice that bound.
No unweighted high-tail counting claim is used. No negative-power asymptotic
conclusion is asserted in this finite statement.

## T05: actual admissible boundaries and their descriptors

Construct an injection from `{x : Riffle.Word // x in Admissible A side}`
into `BoundaryDescriptor D.K (Nat.floor(tau(A))) D.k`, preserving the frozen
descriptor convention: relative extension length, final digit (zero for an
empty extension), and labelled violations strictly before that final digit.
The ambient prefix is fixed. The first-crossing definition forces every
other pre-final digit to equal the appropriate extreme large-pile digit.

Consequently, with `B = D.k*(D.K+1)*lowCount D.K (Nat.floor(tau(A))) D.k`,
the actual admissible boundary subtype is finite and has cardinal at most B.
The subtype of pairs satisfying `AdmissiblePair A` has cardinal at most B^2.
Do not count unrestricted natural-number lists or unused full-word suffixes.

## T06: exceptional-prefix truncation

Let `p : Fin K -> TimeProfile.Simplex k`, a specified partition P with
`P.IsRegular chi C`, `chi>0`, `N>=2`, and `alpha>=0` be given. The endpoints
`v,M : (Fin K -> Fin k) -> Nat` may depend arbitrarily on the full word.
For omega let E(omega) be exactly the source exceptional positions:

`{j in TimeProfile.positions K (v omega) (M omega) |
  not P.IsGoodDigit chi (p j) (omega j)}`.

Then the product-word mass of
`alpha < card(E(omega))/TimeProfile.logScale N`
is at most

`tailWeight K (Nat.floor(alpha*TimeProfile.logScale N)+1) (k*(3*chi))`.

Prove the event inclusion into the full-word bad-digit count and obtain
the per-digit `3*chi` bound from source regularity. No legality/full-support,
deterministic-endpoint, or extra order assumption is introduced. Clipped and
empty position sets are handled by the existing position definition.
Multiplying the inequality by N is a finite consequence. The source
asymptotic choice of alpha is a later limit substitution.

## T07: uniform fixed-column marginal

Use the existing `Shuffle.Histogram (Fin N) k`, `FixedColumn`, and uniform
`columnLaw` definitions. For N>0, any row r and digit a,

`columnLaw(h).prob(fun f => f.val r=a) = (h.count a : Real)/N`.

Prove the uniform law is invariant under row permutations. Sum the identical
row marginals, using the exact histogram count in every column outcome.
No marginal formula is assumed, and no positivity is required for a digit
with zero prescribed count.

## T08: full-word marginal and actual expected row count

Construct each histogram from the existing integer counts of D. Use the
existing `Shuffle.fixedMatrixLaw`, whose columns are sampled independently
and uniformly with their prescribed counts. A matrix row is a full index
`omega : Fin D.K -> Fin D.k`.

Prove that every row's full-word probability equals `wordWeight p_D omega`.
For every set E of natural-number words, prove

`fixedMatrixLaw(D).expect(fun matrix =>
   card {r : Fin D.N | fullList(rowWord matrix r) in E})`
` = coe(expectedCount D E)`.

This is an identity of an actual expected cardinality under the explicit
sampling law. Derive it by finite summation and the column-product law;
independence of different rows is neither true nor assumed.

## T09: truncations for the actual matrix law

Combine T08 with T04 to bound the expected number of rows with an
inadmissible selected boundary, for one side and for their union. Combine
T08 with T06, instantiated by `modelColumnProfile D`, to bound the expected
number of rows whose specified prefix has too many exceptional positions.
These conclusions have exactly the finite tail bounds displayed above.
Any connection to a particular sorted shuffle-graph edge set and all
ordered-limit conclusions remain explicit subsequent obligations.
