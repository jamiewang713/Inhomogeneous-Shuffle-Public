# Independent reconstruction of P01–P05

Candidate reviewed: `lean_formalization/PROFILE_SOURCE_CANDIDATE.md`,
SHA-256 `c68c9f8a5b34671e45813e297ea009a17c59187cc41faf891fd8fbfd47c34e7b`.
This is a preimplementation review; no mathematical source, Lean module,
or frozen contract was edited.

**Verdict: approve every P01–P05 statement.** For P03, I explicitly
approve the root's notation clarification: `p=modelColumnProfile D` and
`chi=A.chi`, with `v=(Riffle.join y z).length`. These are the existing
model and setup data. The exact three Analysis compatibility repairs
listed below are also approved, with no declaration-header or
definition-body change. This review does not treat an uncompiled source
module as already checked.

## Authorized sources reread

* TeX lines 699–746: the actual profile comprises the normalized good
  counts and exceptional **positions**. Lines 728–745 define `S,Q,R,H`.
* TeX 868–881 and 933–942: representative replacement on good digits and
  exact retention of exceptional digit costs in the `cL` decomposition.
* TeX 1009–1036: cellwise Gibbs comparison and the later, separate
  representative/time-integral approximation.
* TeX 1113–1118: counting truncated data after the mesh and partition are
  fixed.
* 2510.22783v1, Definition 4.7 and Lemma 4.8 on PDF pages 23–24, and the
  proof of Proposition 4.2 on pages 32–33: the old profile stores
  `(position,digit)` exceptional data and counts it with the lower
  binomial partial sum. Its representation must not replace the new
  position-only profile.
* 2103.05068v3, entropy definition on page 16, the KL argument (4.19) on
  page 27, and the final profile count on page 28: zero-total entropy,
  total-weighted Gibbs comparison, and a fixed power of `log N`.

The Lean interfaces inspected were the source `Analysis`, `Digits`,
`DigitEstimates`, checked `Base`/`Ambient`, and existing finite-count,
boundary, source-replacement and word-extension interfaces. No further
mathematical source was used.

## P01: raw counts and literal data — approved

For `Key = Fin R × Fin P.cellCount × Fin k`, define

`rawCounts(a) = card {j in goodPositions p omega P chi v M |
                       digitKey p omega P timeClass j = a}`.

This is the exact numerator in `TimeProfile.digitCount`
(`Digits.lean:30`). The fibre is a subset of `Finset.univ : Finset
(Fin K)`, so `rawCounts(a)<=K`, including empty, reversed, and clipped
intervals. This needs no endpoint ordering or logarithmic positivity.
The identity `digitCount(a)=(rawCounts(a):Real)/logScale N` is
definitional for every natural `N`, including zero and one.

The data type is exactly

`(Key -> Real) × Finset (Fin K)`,

and the datum is `(digitCount function, exceptionalPositions)`. Equality
of these pairs is, by product extensionality, precisely
`TimeProfile.SameCoarseProfile` (`Digits.lean:60`) for the fixed endpoints.
No exceptional labels are added to this type.

`sourceExceptionalPositions p P chi v M omega` from T06 is
definitionally the source `exceptionalPositions p omega P chi (v omega)
(M omega)` (`Digits.lean:21`). Thus the equality is pointwise for
arbitrary word-dependent endpoint functions. Taking constant functions
gives the fixed-endpoint version. The zero-based source interval is
`v <= j.val ∧ j.val < M`; no shift of either endpoint is introduced.

## P02: finite image of arbitrary input data — approved

Keep all candidate quantifiers, including `N>=2`, arbitrary index type
`I`, and arbitrary endpoint functions. No `Finite I` instance is needed.
Let `S` be the set of realized coarse data from indices satisfying `Q`.
Use the finite code type

`SparsePattern K h k × (Key -> Fin (K+1))`.

Its decoder sends a code to the normalized raw-count function, together
with the sparse pattern's support, forgetting all labels. Its cardinal
is exactly

`lowCount K h k * (K+1)^(R*P.cellCount*k)`.

For each `i` with `Q i`, the exceptional-card premise supplies a sparse
support of size at most `h`; its label at each position is the **actual**
digit of `word i`. The bound in P01 puts every raw count into `Fin(K+1)`.
Decoding this code gives the exact realized datum. Hence `S` is contained
in the finite decoded range, establishing finiteness first and the
`Nat.card` bound afterwards. This is a finite-range containment proof,
not an assertion that the input family or the source data map is
injective.

The construction handles `k=0` correctly: any used exceptional position
already supplies its label from the given function `Fin K -> Fin 0`.
There is no need to choose a default digit or assert `k>0`. When `K=0`
the support is empty and the unique empty count function is decoded in
the usual way. Empty `I`, empty `Q`, `R=0`, zero cell count, and `h>K`
cause no new requirement. The source objects may make some combinations
uninhabited; the theorem does not impose a separate nonemptiness axiom.

The stated `N>=2` is retained even though this range-containment proof
does not have to invert `logScale N` or recover raw counts from a real
datum. Counting many-to-one decoded values is enough.

## P03: actual pair/profile data and source prefixes — approved

Use the actual subtype

`Pair A = {yz : Riffle.Word × Riffle.Word //
             Riffle.AdmissiblePair A yz.1 yz.2}`.

T05 already proves this type finite and bounds its cardinal by

`B^2`, where
`B=D.k*(D.K+1)*lowCount D.K (floor(boundaryThreshold A)) D.k`.

The input type may be `Pair A × FullIndex D × Nat`, with any predicate
`Q`. Use `p=modelColumnProfile D`, `chi=A.chi`, start endpoint the length
of the pair's join, and final endpoint the input's `M`. Apply P02 to the
entire input type with the conjunction of `Q` and exceptional-card
bound. This bounds the union `U` of all realized coarse data by

`lowCount D.K h D.k * (D.K+1)^(R*P.cellCount*D.k)`.

The pair/data image is contained in `Pair A × U`. Multiplying its two
finite cardinal bounds and using the elementary natural-power identity
`(K+1)^2*(K+1)^d=(K+1)^(d+2)` gives exactly P03's displayed formula.
The natural input endpoint and different full extensions disappear
under the image map; no factors for either are needed. This argument is
valid for arbitrary `Q`, including predicates mentioning retention or
stopping, without assuming those predicates hold outside its domain.

For the source-prefix consequence, the relevant already proved source
interfaces are:

* `Riffle.full_extension`, `Words.lean:197`: every `Legal D x` has a
  full legal extension. The proof uses `exists_positive_digit`, derived
  from the model's nonzero total column count; it does not assume that
  every digit has positive count.
* `Riffle.fullList_of_full`, `Words.lean:173`: a full word is represented
  by a `FullIndex D`.
* `Riffle.digit_prefix`, `Words.lean:8`, and
  `Riffle.fullList_digit`, `Words.lean:141`: prefix digits equal the
  corresponding full-index digits.

If `x` is legal and `join y z` is a prefix of `x`, set
`M=x.length` and `v=(join y z).length`. Every `j` in `positions K v M`
has `j.val<x.length`. Thus two full-index extensions of `x` agree at
all positions that enter good-position membership, exceptional-position
membership, and `digitKey`. Their raw counts, normalized count
functions, and exceptional sets are equal. This proves independence
of the full extension, including `x=join y z`, terminal `x`, and empty
prefixes. Existence is obtained from the two source theorems above,
not inserted as a new premise.

Consequently each permitted source triple contributes its data to the
previous pair/profile image using any obtained extension. The condition
`exceptional card<=h` is independent of the extension as well. The
source family may be arbitrary; data can be defined by choice of a
proved existing extension or relationally by existence, with the
independence lemma identifying the values. This finite result does not
claim that legal source prefixes themselves form an injective profile
encoding. Applying it to a particular stable family still requires the
already proved legality/join-prefix facts for that family.

## P04: exact source cost decomposition — approved

The source declaration `TimeProfile.profile_cost_replacement` begins at
`Digits.lean:176`. Its complete parameters are `N,p,x,P,timeClass`, real
`chi,C,b`, natural implicit `w,v,M`; its premises are exactly

`N>=2`, `chi>0`, `C>=0`, `P.IsRegular chi C`,
`w<=v`, `v<=M`, `M<=K`, and `LegalPrefix p x M`.

Its conclusion is a conjunction of two bounds on the same error

`abs(cL N p x b w M -
       (cL N p x b w v - profileS N p x P timeClass chi v M
                        - profileQ N p x P chi v M))`:

first `C*chi*card(goodPositions)/logScale N`, then
`C*chi*(M-v)/logScale N`. Preserve every listed binder, including
`LegalPrefix`, even where an intermediate finite identity is valid more
generally. The ambient endpoint is the actual natural `w`, not a floor
of a macroscopic time. `b` is an unrestricted real.

The exact finite identifications with F04–F06 are obtained by setting

`J=TimeProfile.positions K v M`,
`pActual(j)=TimeProfile.prob (p j) (x j)`,
`pRep(j)=TimeProfile.prob (P.rep (P.classify (p j))) (x j)`,
`L=TimeProfile.logScale N`.

Then:

1. The source good and exceptional filters equal the frozen filters on
   `J,pRep,chi`, by unfolding `IsGoodDigit`.
2. `source_digitCost_eq_cost` already proves equality of the two real
   cost definitions for **every** real argument, including zero.
3. Finite fibre regrouping for `digitKey` gives
   `profileS = goodCost J pRep chi L`; the exceptional formula gives
   `profileQ = exceptionalCost J pActual pRep chi L` directly.
4. Unfolding `cL` gives the corresponding frozen `lengthExponent` on
   `positions K w M`. Ordered endpoints give the disjoint split into
   `positions K w v` and `J`.
5. `source_regularDigits` supplies the frozen replacement hypotheses
   with error `C*chi`; `logScale_pos hN` supplies the positive divisor.
   F06 gives the cardinality error, up to commuting the three scalar
   factors. The interval-cardinality identity and the good-set subset
   give the coarser error, using the existing `C>=0` and `chi>0`.

No integral, approximation of `w`, or equality of limiting times is
needed. There is no assertion that `profileQ` or actual `cL` is constant
on the position-only coarse profile.

## P05: exact entropy and exceptional correction — approved

`TimeProfile.profile_entropy_bound`, `Digits.lean:247`, has parameters
`N,p,x,P,timeClass,chi,v,M`, with only `N>=2`, `chi>0`, and
`theta in [3,4]`. There is **no** regularity, legality, or endpoint-order
premise. Preserve this exact domain. Each cell's digit counts are
nonnegative. Positive count produces an actual good position in its
fibre, proving representative probability `>2*chi>0` via
`positive_count_support` (`Digits.lean:83`). Thus finite Gibbs applies
to the positive-count support without full support of the simplex.
Summing the cell inequalities yields exactly

`profileH <= theta*profileS
             - sum_a digitTotal(a)*psi(P.rep(a.cell),theta)`.

The zero-count branches are explicit. A zero-total cell has every count
zero by nonnegativity and contributes zero. A positive-total cell
cancels that total in each positive-count summand; zero coordinates are
omitted. This reconstructs the zero-aware source formula.

When reusing `TimeProfile.profileH_source_formula` in
`DigitEstimates.lean:16`, its complete existing binder list must remain:
`N,p,x,P,timeClass,chi,C,v,M`, `N>=2`, `chi>0`,
`P.IsRegular chi C`, and `LegalPrefix p x M`. Although the latter
premises are not required for the elementary entropy identity, this
batch does not remove them from that source declaration or add them to
the distinct, weaker-domain entropy inequality.

`TimeProfile.exceptional_psi_error`, `DigitEstimates.lean:56`, has
parameters `N,p,x,P,timeClass,chi,v,M`, with exactly `k>=2`, `N>=2`,
and `theta in [2,4]`. In particular it adds no `chi>0`, regularity,
legality, or endpoint-order premise. Regrouping the good fibre sum and
splitting the full finite interval leave the exact exceptional sum

`sum_{j in exceptionalPositions} psi(P.rep(P.classify(p j)),theta)
 / logScale N`.

The existing `psi_bounds` gives every summand in `[0,4*log k]`;
division by the positive logarithmic scale gives exactly the interval
`[0,4*log(k)*profileR]`. This is the finite deletion correction before
any integrated-time approximation. It is also a direct source
specialization of the frozen finite exceptional-cost identity/bounds.

## Exact Analysis compatibility changes — approved

I read the original `Analysis.lean` and the complete read-only Lean 4.19
error report at
`/private/tmp/riffle-profile-source-review/RiffleTimeProfile/Analysis.log`.
The three listed changes are precisely justified as follows.

1. At original lines 111–113, in `finite_gibbs`, retain `field_simp`
   and add `ring` immediately afterwards. The displayed residual goal
   in the log is
   `c*(C*p^theta-c*Z)*Z = (C*p^theta-Z*c)*(c*Z)`.
   This is a commutative-ring identity. All nonzero denominator facts
   were already supplied in the original branch (`c>0`, `Z>0`). No
   new support or positivity premise is required.
2. At original line 150, replace only
   `apply continuous_finsetSum` by `apply continuous_finset_sum`.
   The latter is the finite-sum continuity theorem in pinned mathlib
   4.19 (generated by `to_additive` from `continuous_finset_prod` in
   `Mathlib/Topology/Algebra/Monoid.lean:846`). The remaining `intro l _`
   and termwise `rpow` continuity proof have the same mathematical
   domain. No continuity assertion is postulated.
3. At original line 239, replace only
   `let : Fintype I := Fintype.ofFinite I` by
   `letI : Fintype I := Fintype.ofFinite I`. The original anonymous
   declaration syntax triggers the displayed parser/typeclass failure.
   `I=Set.range raw` is a subtype of the finite type
   `Fin k -> Fin m`; its finiteness already follows from that type.
   The replacement installs the very same `Fintype.ofFinite I` value
   as a local instance for the following `equivFin`/cardinality uses.
   It creates no new hypothesis, mathematical axiom, or data definition.

All three changes occur inside proofs. The declaration statements and
the bodies of every source `def` must stay verbatim. They may be made
only in a compatibility copy, leaving the original untouched. This
approval is confined to the listed three repairs; any further error
needs its own exact-diff review. Analysis, Digits, and DigitEstimates
must compile completely and undergo the transitive foundation check
before their theorems are registered as checked dependencies.

## Derived helper coverage to include in the freeze

The following are the precise intermediate obligations reconstructed
above, with the same local object data as their parent statements:

* Raw fibre subset/cardinality bound and its normalized-count identity.
* Product-data equality iff the existing `SameCoarseProfile`; pointwise
  equality of the old T06 and source exceptional filters.
* A finite code decoder, its exact cardinality, a realized-code witness
  for every restricted input, and inclusion of the realized image in
  the decoded range. No injectivity of source data is required.
* For words agreeing on `positions K v M`, equality of good filters,
  exceptional filters, raw-count arrays, normalized counts, and coarse
  data. Endpoints may be arbitrary naturals in this local statement.
* Prefix/full-index digit agreement, existence of a full-index
  extension of a legal prefix, extension independence of its coarse
  data, and inclusion of a source-prefix family image in the actual
  pair/profile image.
* Product-image cardinality monotonicity and the exact power/product
  rearrangement yielding the stated pair/profile count.
* Source/frozen good-filter, exceptional-filter, cost, good-cost,
  exceptional-cost, and length-exponent identities, including finite
  fibre regrouping and the ordered interval split; cardinality of a
  source interval with `v<=M<=K` is `M-v`.
* The literal zero-aware entropy formula, good-fibre regrouping for
  representative `psi`, and exact exceptional deletion identity, with
  the original source theorem binders retained whenever those theorems
  are reused.

These helpers do not add premises to P01–P05. They implement finite
counting, extensional equality, and the source statements' existing
arithmetic domains. No mathematical correction to the candidate is
requested. Remaining time-integral/limit identifications and constancy
claims excluded by the candidate remain excluded.
