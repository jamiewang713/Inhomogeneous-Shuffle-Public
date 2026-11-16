# Final contract audit: profiles, words, and prefix trees

**Verdict: passed.** The final `Basic.lean`, `Profiles.lean`, `Words.lean`, and `PrefixTree.lean` match the frozen definitions and all P01–P14, W01–W14, and T01–T15 statements. I found no added hypothesis, weakened conclusion, altered definition, additional named theorem, or unsupported project input. No files owned by the implementation authors were edited during this audit.

The contract SHA-256 is `2d48b42c85f7946ddb308efc21d47a4e6b596b497d5c8e447f4ae9ac1062dfd0`, matching `FREEZE.md`. Final source hashes and direct project dependencies are recorded in `profile-tree-dependencies.json`.

## Definition semantics

| Definition group | Audit result |
| --- | --- |
| `PileProfile` | Exactly natural column counts, N>0, k≥2, and each column sum N. There is no assumption of all counts positive, K positive, profile regularity, randomness, or asymptotics. |
| `countAt`, `probAt` | The prescribed count at indices below K and zero at other natural indices; real count divided by N. |
| `NormalizedProfile`, `normalized` | Exactly real coordinates in [0,1] summing to one, with `normalized` using the actual normalized counts and P04/P05/P07 proofs. |
| `Word`, order, `Prefix` | Fixed-length list vectors, with ordinary list lex order inherited by the subtype. Prefix is `List.IsPrefix`, with no coordinatewise order substitution. |
| Empty/truncate/append | The empty vector, list `take m`, and list append of one digit, respectively. Bound proof fields do not change list values. |
| `Legal`, `mass` | Exactly the depth bound and positive selected counts; product of selected normalized counts, at every natural depth. |
| `RawPrefix`, `Node`, `FullWord` | A finite dependent pair of depth≤K and a vector, then the legal subtype; full words are exactly legal depth-K vectors. |
| Node projections/order | The depth, word, list, and ordinary list-prefix relation of the prescribed representation. |
| `root`, `parent` | Root is the legal empty word. Parent is truncation to depth−1. At depth zero, this is the same empty node as root, including the dependent/subtype proof fields by proof irrelevance. There is no extra nonroot assumption. |
| `Child`, cylinders | Child means prefix plus exactly one greater depth. Cylinders contain precisely full legal extensions. |
| Antichain, cover | Antichain is the asymmetric prefix condition forcing equality, for every pair of members. Cover is the independent requirement that every full legal word belongs to some listed cylinder. |

## Statement-by-statement matching

Every ID below was matched to its actual final declaration type, not only to a comment or declaration name.

| IDs | Final match and boundary checks |
| --- | --- |
| P01, P02 | Correct below-K and at-or-above-K branches of extended counts. |
| P03 | Single column count ≤N; no extra summability or digit-positivity assumption. |
| P04, P05, P06 | Nonnegativity, upper bound, and positivity equivalence at every natural time index, including indices≥K. |
| P07, P08 | Exactly the frozen j<K condition for normalization and existence of a positive digit. |
| P09, P10, P11 | Empty product, nonnegative mass, and mass≤1 at all natural word lengths. |
| P12 | Exactly m≤K as the additional displayed condition; positivity iff the existing `Legal` predicate. |
| P13 | Exactly m≤K; sum over all fixed-length words, including zero-mass illegal words. |
| P14 | Product append identity without a new depth assumption. |
| W01, W02, W03, W04 | Reflexivity, transitivity, length monotonicity, and equal-length prefix equality. |
| W05, W06, W07 | Empty prefix; truncation prefix; equality with truncation iff prefix, with the frozen m≤n bound. |
| W08 | Comparability of arbitrary-length prefixes of a common word. |
| W09 | Truncation monotone on arbitrary lists under ordinary lex order, not restricted to equal lengths. |
| W10 | Convexity of the prefix cone on arbitrary lists, with exactly the two order inequalities and two prefix assumptions. |
| W11, W12 | Legal truncation and legal empty word, with no new positivity restriction. |
| W13 | The entire biconditional: legal append iff legal original word, m<K, and positive next count. |
| W14 | Existence of a full legal extension for every legal word; the proof chooses positive digits from P08 without adding a hypothesis. |
| T01, T02, T03 | Tree prefix reflexive/transitive/antisymmetric; equality is actual dependent legal-node equality. |
| T04, T05, T06, T07 | Root prefix, parent prefix, parent depth, and strict decrease only under positive depth. |
| T08, T09 | Child exists under depth<K; every legal-node cylinder is nonempty. These do not assert an empirical matrix occupancy. |
| T10, T11 | Cylinder nesting and overlap iff comparable tree prefixes. Both directions of T11 are proved. |
| T12, T13 | Pairwise disjoint cylinders for distinct antichain nodes; exactly one containing antichain node when cover is separately supplied. |
| T14 | Children cover precisely the parent cylinder at a nonleaf, as the frozen biconditional for each full legal word. |
| T15 | A proved `Finite (Node P)` instance, one of the two forms explicitly allowed by the frozen contract. |

There are exactly 14 profile theorem declarations, 14 word theorem declarations, 14 tree theorem declarations, and the T15 finite instance: 43 frozen IDs in these modules. Constructor definitions and existing-data instances are as permitted by the contract; no extra named helper theorem was introduced.

## Proof and trust checks

The implementation author confirmed final `Words.lean` and `PrefixTree.lean` compilation with no warnings or errors, and `Profiles.lean` was compiled cleanly earlier. I independently imported the final compiled `PrefixTree` interface and executed `#print axioms` for all 43 P/W/T declaration names. All names resolved. The only reported axioms were standard trusted Lean foundations `propext`, `Classical.choice`, and `Quot.sound`; some elementary word lemmas reported fewer or none. No `sorryAx` or additional axiom appeared.

The four source files contain no `sorry`, `admit`, `axiom`, or `unsafe` declaration. The finite constructors carry proved fields, not new hypotheses. In particular, W14 uses classical choice of an already proved positive digit in each column, and T15 uses trusted finiteness of finite vectors, dependent sums, and subtypes.

The dependency JSON distinguishes direct references in final proof scripts from mathematically sufficient prereview dependencies. For example, P13 proves normalization through the trusted vector/function equivalence and finite product-of-sums identity, so it does not depend on P14; W14 fills all remaining coordinates directly, so it does not call W13. This is a change of proof, with the frozen statements and definitions preserved.

## Whole-proof map and article index

`PROOF_MAP.md` covers the active upper-bound chain, the active matching lower-bound chain, and the random-pile-size extension. It correctly excludes the commented obsolete lower overview and distinguishes the active random upper theorem from the future random lower proof obligations. It explicitly records why simply averaging deterministic lower TV bounds is insufficient and why a common union test with exponentially small uniform false positives is needed.

I checked `article-reference-dependencies.json` against the active article after removing its comment environment: all 70 active labelled definition/lemma/theorem/proposition/corollary entries appear exactly once, no obsolete entries remain, and every recorded line number matches. Thus the declaration coverage is complete for those labelled environments.

The JSON is a lexical citation index, as `PROOF_MAP.md` already explains, and should not be represented as an exact mathematical DAG. Its source-window attribution attaches some later discussion or delayed proofs to the preceding result. For example, the lower theorem's final proof references appear under `prop:cold-lower`, and there are four self-reference records. There is also one comma-joined reference string (`def:first-moment-margin,def:recursive-first-moment-margin`) rather than two separate labels. These indexing limitations do not affect the Lean statements or the reviewed mathematical dependency tables. The active upper/lower/random architecture is accurately covered by the table and index together.

## Scope of this approval

This audit approves the frozen finite profile/word/tree content only. It does not certify the unformalized analytic sketches, any probabilistic matrix law, the graph representation of an inverse shuffle, or a cutoff theorem. The zero-count and K=0 cases remain included exactly as frozen.
