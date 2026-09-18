# Independent algebra reconstruction of the actual profile-fibre entropy bridge

Decision: **APPROVE** the exact proposed `PROFILE_FIBRE_CONTRACT.md`, containing two definitions and PF1--PF4, without additional hypotheses or changes to the conclusions. Its reviewed SHA256 is `a90fa7f7a0679465139c1c74be4ec9237a01dc6fde3c012a85dd513732622727`. I compared that exact document after completing the reconstruction below; all definitions, binders, conclusions, arbitrary-key cases, and exclusions match the reconstructed argument.

The earlier statement candidate is also approved; its SHA256 is `764d0311f897eb7622922b2b366b400b1191ecd8e214bcd023a8ad5449bdb24e`. The labels F1--F4 below refer to precisely PF1--PF4 in the exact proposed contract.

This is a pre-freeze mathematical and dependency review. No Lean implementation, frozen contract, or earlier review was changed. The mathematical source comparison is with the authorized TeX's space-time profile definition and first-moment aggregation, and the permitted papers' finite type-counting argument. The now-proved `ProfileClasses` and `FirstMoment.Entropy` declarations supply the project interfaces used below.

## Exact public data

`profileKeyCounts` reads the natural value of the existing flat vector at `finProdFinEquiv (a,l)`. The count vector has length c*k; the unflattened domain is exactly `Fin c -> Fin k -> Nat`. No positivity or compatibility predicate belongs in this definition.

`ProfileFibre` is the subtype of the **actual** `ProfileWord` domain on which the existing encoder equals the supplied key. It retains admissibility, actual Stable membership, and the original real exceptional bound. It does not replace these by abstract words with matching counts. The key need not be realized.

The four statements therefore need only the existing model/setup and the deterministic `cell`, `good`, `alpha`, and `route` data, followed by the proposed word/key binders. Neither a domain finiteness instance nor a nonempty-fibre witness is a premise. The existing model fields derive N>1 and k>=2.

## Reconstruction of F1

For a word p, encoder coordinate h is defined by unflattening h with `finProdFinEquiv.symm` and recording the corresponding `goodDigitCount`. Evaluating `profileKeyCounts` at (a,l) therefore gives exactly the count at

    finProdFinEquiv.symm (finProdFinEquiv (a,l)) = (a,l).

Function extensionality twice proves the stated function equality. No source specialization of `cell` or `good` is used.

## Fixed data in an inhabited fibre

For F3, choose a witness p0 only after splitting on nonemptiness of the actual fibre. Write its triple as (y0,z0,x0), and put

    v = join y0 z0,
    M = x0.length,
    Q = exceptionalPositions A good y0 z0 x0,
    J = {i : Fin K | v.length <= i.val < M and i not in Q}.

For every other fibre element p, its key equals the same key as p0. Applying the already proved `encodeProfile_eq_data` gives:

1. y=y0 and z=z0, so the literal join word is v;
2. x.length=M;
3. each natural good-digit count is the corresponding fixed key count;
4. its exceptional support equals Q;
5. at every i in Q, its actual digit equals x0's actual digit.

Separately, `stable_desc (admissiblePair_rawPair ...) ...` gives both `Legal D x` and the literal list-prefix relation `v <+: x`. This supplies the prefix itself, not merely its length. It also gives M<=K and legal alphabet values at every position before M.

Consequently, for every i in the common extension interval,

    i not in Q <-> good i (digit x i.val).

This remains valid when goodness depends arbitrarily on the digit. Equality of the exceptional support, together with its original definition for each word, is exactly what fixes the good-position set. No independence assumption on `good` is necessary.

## Injection into the correct type class

Use the proof-local equivalence

    e : Fin J.card ≃ J := J.equivFin.symm.

The finite-set equivalence exists in the pinned mathlib (`Data/Fintype/EquivFin.lean`). Define `cellJ j=cell (e j).val`. For each fibre word p, let `w_p j` be the actual digit of x at position `(e j).val`, regarded as `Fin k` using legality.

For every cell a and digit l, reindexing through e proves

    #{j | cellJ j=a and w_p j=l}
      = goodDigitCount A cell good y z x a l
      = profileKeyCounts key a l.

The first equality is an exact finite-set bijection: the right-hand filter is supported in J because it asks for a good digit in the extension; conversely every selected J position has the same goodness property for p. The second equality follows from F1 and the fibre equation. Thus

    w_p belongs to typeClass cellJ (profileKeyCounts key).

The domain length is J.card, not K or M. Fixed prefix positions and labeled exceptional positions do not incur an entropy cost again.

This map is injective on the actual fibre. If two restricted functions agree, first recover equal boundaries and lengths from their equal keys. At any position i<M:

- if i<v.length, both digits equal the digit of v, by `Riffle.digit_prefix`;
- otherwise, if i is in Q, the already stored exceptional labels give equality;
- otherwise i belongs to J, and surjectivity of e plus equality of restrictions gives equality.

These three cases exhaust all positions. Apply `List.ext_getElem` with the common length; unfolding the totalized `Riffle.digit` is justified only after establishing i<M. Equality of x and equality of y,z give equality of the triples, followed by subtype extensionality twice. Proof fields do not create extra fibre elements. This argument proves injectivity of the **restriction within a fixed key fibre**, not injectivity of the profile encoder.

## F2: genuine finiteness

The same injection establishes `Finite ProfileFibre` in the inhabited case, because its target is a subtype of a finite function space. The empty case is finite immediately. Thus F2 is valid with the exact proposed hypotheses.

There is also a simpler proof-local alternative for F2 alone, avoiding duplication of the type-class construction. Map every fibre element to its padded digit function `Fin K -> Fin k`, using actual digits before its length and 0 afterwards. Legality supplies actual digit bounds, and k>=2 supplies the padding digit. Equal keys already fix the stable-word length and the two boundaries; equality of padded functions therefore recovers the stable word and the entire fibre element. This injects directly into a finite function type, including when the fibre is empty. Either proof preserves the exact F2 statement and adds no public declaration.

The derived F2 is useful to install local finite instances later. It must not be replaced by reliance on `Nat.card` returning zero for infinite types.

## F3: exact cardinal bound

If the fibre is empty, its natural cardinal is zero and the claimed inequality follows from strict positivity of `Real.exp` for every real input. No count compatibility has to be proved for an unrealized key.

Otherwise, the injection above and `Finite.card_le_of_injective` give

    Nat.card ProfileFibre
      <= Nat.card (typeClass cellJ (profileKeyCounts key))
      = (typeClass cellJ (profileKeyCounts key)).card.

The pinned mathlib lemma `Nat.card_eq_finsetCard` gives the displayed equality directly; `Nat.card_eq_fintype_card` and `Fintype.card_coe` are an equivalent route. Cast this natural inequality to the reals and apply the already proved

    type_class_card_le_exp_entropy
      (K := J.card) (k := D.k) (d := c)
      hk cellJ (profileKeyCounts key),

where hk follows from `D.two_le_k`. This gives exactly

    (Nat.card ProfileFibre : Real) <= exp(typeEntropy(profileKeyCounts key)).

There is no asymptotic loss, multiplicative constant, or exceptional-position factor. The latter data have already been fixed by the key. The existing type-class theorem itself does not assume count compatibility; an impossible count vector simply yields an empty type class.

## F4: exact power normalization

`D.one_lt_N` gives `(1:Real)<D.N`, so both the base and its logarithm are positive. For every real h,

    (D.N : Real)^(h/log D.N)
      = exp(log D.N * (h/log D.N))
      = exp h.

Use `Real.rpow_def_of_pos` and cancellation of the nonzero logarithm. This conversion works for all h; no nonnegativity or compatibility premise on the entropy is required. Rewriting F3 gives the exact proposed F4 conclusion.

## Source entropy and integration boundary

For natural counts n(a,l), put nTot(a)=sum_l n(a,l). The source normalized counts are n(a,l)/log N. For a cell with positive total, its contribution to the source entropy is

    sum_{l:n(a,l)>0} [n(a,l)/log N] * log(nTot(a)/n(a,l))
      = [nTot(a) log nTot(a) - sum_l n(a,l) log n(a,l)] / log N.

Cells with zero total and zero-count terms contribute zero under the source convention. Summing yields precisely `typeEntropy n / log N`. This proves the mathematical normalization used by F4; a formal identification with another package's named `profileH` still needs the concrete joint-cell and source-good-predicate mapping. It is correctly absent from the proposed four statements.

The count theorem is precisely what the first-moment proof needs at the point where it claims that a fixed refined class contains at most N^H words (TeX lines 1872--1876). Exact size exponents may vary between words in that class; neither F3 nor F4 asserts constancy. The final edge/numerical aggregation must retain per-word data or establish a uniform upper bound separately.

## Edge cases and proof-local obligations

No missing mathematical hypothesis was found. The following are implementation obligations, all proof-local:

1. Transport the literal join word, stored length, and exceptional support from key equality before comparing positions.
2. Prove membership in J is the actual good-position predicate for every fibre word, not merely for the chosen witness.
3. Construct the finite-set bijection identifying the restricted counts with the original good counts, including equality of `Fin` digits versus equality of their natural values.
4. Prove the three-case digit reconstruction and then list/subtype equality.
5. Establish F2 explicitly, and use a finite target in the cardinal inequality.
6. Derive k>0 and log N!=0 from the existing model fields.

Unrealized keys, invalid stored boundary codes, incompatible count vectors, and negative real cutoff values do not require extra well-formedness assumptions: their actual fibres are empty whenever unrealizable. At K=0 or J.card=0 the restriction is the unique empty function; a realized fibre has at most one element and entropy zero. When c=0, the supplied `cell : Fin K -> Fin 0` already forces the corresponding empty-position situation. Unused cells and zero counts are handled by the existing zero-aware entropy. Terminal and fallback Stable words are included exactly as in `ProfileWord`; no numerical exclusion is silently built into this bridge. Arbitrary routing can only reduce a fibre.

The exact two definitions and F1--F4 are ready for comparison with the other independent reports and then an explicit supplemental freeze. No implementation should infer additional public helpers or hypotheses from this audit.
