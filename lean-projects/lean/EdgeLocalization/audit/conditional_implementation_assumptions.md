# Independent implementation audit: conditional model and split

I inspected `Conditional/Model.lean` and `Conditional/Split.lean` against `audit/frozen_conditional_contract.md`. I independently checked their compiled signatures and axiom dependencies and reran Lean 4.24.0 on both current files. Both compile without errors or warnings. I did not edit any implementation or frozen record. My implementation ownership was the separate Counts module, not either file reviewed here.

**Verdict: the three definitions and O.01–O.03 faithfully match the freeze. No extra assumption, unproved interface, or hidden restriction was found.**

## Definitions

`prefixCounts` has precisely the frozen initial-segment map using `Fin.castLE hM`. It takes neither population N nor feasibility hn, since it only restricts the count array.

`suffixCounts` uses the original absolute coordinate M+t.val, with its bound proved from M≤K and t<K−M. The suffix length uses natural subtraction. It also correctly omits N and hn. Neither count-array definition inserts, deletes, rescales, or conditions a column count.

`splitMatrix` takes explicit N and no feasibility or probability argument. Its forward map is literally the pair of coordinate restrictions specified by the freeze. Its inverse explicitly splits on j.val<M and takes the corresponding prefix or suffix column. The suffix branch proves M+(j.val−M)=j.val before transporting the histogram identity. Both inverse laws are proved through function and subtype extensionality; no inverse, gluing, or coordinate law appears as an assumed field.

These constructors do not require any nonempty alphabet, row type, prefix interval, or tail interval. Even if a particular collection of count arrays has no matrix sample, the dependent-product equivalence is valid without assuming one exists.

## Theorems

| Statement | Fidelity and proof audit |
|---|---|
| O.01 `matrix_expectation_split` | Exact argument order n, hn, hM, f, with arbitrary real-valued f. The three laws use the same N and inherited count-sum proofs. The proof derives the product cardinality from the actual split equivalence, derives factorization of uniform weights from already proved C.17, reindexes the finite sum through the inverse equivalence, and distributes the weights. No independence, weight identity, positivity, integrability, or boundedness premise was added. |
| O.02 `tailCollisionFactor_suffix` | Exact all-N algebraic identity with explicit N and no hn. The finite product bijection maps a suffix coordinate to M+t.val; injectivity, surjectivity, and the inverse subtraction bounds are proved. The summands are the same original-population factors. |
| O.03 `prefix_occupancy_glue` | Exact samplewise occupancy identity with n, hM, x, p, t and no hn. The proof derives prefix-coordinate equality from `splitMatrix.apply_symm_apply`, then proves prefix-membership equivalence for each actual original row label using the existing row-prefix theorem. It proves equality of the occupied finite sets before taking cardinalities. It does not infer label membership from a cardinality equality. |

O.01 applies to signed integrands because it is an identity of finite real sums. Its proof uses no monotone convergence, expectation inequality, nonnegative-integrand lemma, or implicit positivity condition on f. Its local weight identity comes from the actual model's uniform weights and finite cardinalities; it is not a newly assumed conditional-law interface.

O.03 explicitly separates natural positions i<N from positions outside the row range. The latter are excluded by both finite-set filters, so no padded row value is used to infer actual occupancy.

## Empty and degenerate cases

- **N=0 or N=1:** no N≥2 premise occurs in any reviewed declaration. The model split is purely by columns. O.01 uses the existing constructed laws on empty/single-row matrices and makes no division by N(N−1). O.02 only reindexes the core's total factors. O.03 treats the actual label set, which is empty or a singleton.
- **M=0:** the prefix factor is the unique empty coordinate family. There is no evaluation at a nonexistent prefix coordinate. O.01 reduces to integration over the full tail, and O.03 states the correct empty-prefix occupancy equality.
- **M=K:** the suffix coordinate type is empty. No inverse branch evaluates a suffix column when a full index lies in the prefix interval. O.02 equates two empty products, both 1.
- **K=0:** M≤K forces M=0. Both restricted coordinate families are empty; `splitMatrix` is the actual equivalence between the one empty array and the pair of empty arrays. O.01's finite sums retain normalized one-point laws for every N.
- **k=0:** the split never chooses a default digit. Where a nonempty column index exists, hn forces N=0; where no column exists, arbitrary N remains allowed. A positive-length vector prefix into Fin 0 cannot be instantiated, while the empty prefix is represented normally.
- **Zero piles or impossible prefixes:** no positivity or legal-word premise is introduced. The pointwise prefix equivalence remains true, and the subsequent occupancy may be zero.
- **Null occupancy slices:** the reviewed split theorem does not define or divide by a conditioning-event probability. Its arbitrary-integrand domain permits the later event-indicator argument without any new positive-probability assumption.

The population remains N throughout. Fixing prefix columns determines prefix-label membership, but does not replace the tail population by the size of that subset. These files assert neither independence among prefix columns after an occupancy condition nor preservation under an arbitrary exploration reveal.

## Signature, dependency, and declaration checks

The compiled `#check` outputs match all frozen argument conventions, including explicit N for `splitMatrix` and O.02, absence of hn from the pure definitions/O.02/O.03, and arbitrary signed f for O.01.

The files contain exactly the three selected definitions and the three allocated theorem declarations. All auxiliary coordinate, count, and weight facts are proved local steps. There are no new named instances, probability laws, gluing helpers, or Fubini helpers.

Compiled dependency checks report:

- `prefixCounts`: no axioms;
- `suffixCounts`: only `propext` and `Quot.sound`;
- `splitMatrix` and O.01–O.03: only trusted `propext`, `Classical.choice`, and `Quot.sound`.

There is no `sorryAx`, custom axiom, prohibited placeholder, unsafe proof escape, or `native_decide` use. No correction is requested. This audit certifies the allocated split definitions and finite split/prefix identities; the final occupancy-slice estimates and their independent review remain separate from these files.
