# Independent implementation audit: overlap

I compared the current `Overlap/FiniteLaw.lean` and `Overlap/Edges.lean` with `frozen_overlap_contract.md`, inspected all proof bodies, and independently ran the module build and Lean signature/axiom queries. I changed no implementation, source, frozen contract, or hashed pre-freeze report.

**Verdict: accepted. S.D01 and S.01–S.06 implement the frozen signatures and meanings without additional assumptions or declarations.**

## Definition and statement fidelity

- **S.D01:** `FiniteLaw.prod` has exactly the two finite laws as explicit inputs. Its weight is definitionally `w.weight z.1 * v.weight z.2`; an independent Lean `rfl` check passed. Nonnegativity uses the two input-law fields, and normalization is proved by the finite product-sum identity and the two total-weight equalities. No normalization or independence fact is an added input.
- **S.01:** `prod_expectation` retains every real-valued integrand without sign or boundedness hypotheses. Its proof rearranges finite sums and multiplication only. The compiled signature has independent universes for the two sample types.
- **S.02:** `prod_probability` retains arbitrary separate-coordinate events with no public decidability argument. The proof locally supplies classical decisions and explicitly handles all four truth combinations of those events. It never divides by an event probability.
- **S.03:** `expected_card_intersection` retains the arbitrary element type with only decidable equality, both finite laws, both random sets, and both pointwise support inclusions. The proof actually uses the two inclusions to contain the intersection in s, applies the existing expected-cardinality identity, and derives rectangle membership probabilities from S.02. It does not assume the desired factorization.
- **S.04:** `edgeDensity_eq_expected_shared_internal_edges` uses exactly the same law, N, row map, prefix, and absolute edge positions in both product coordinates. The support is the unchanged `range (N−1)`. Its proof specializes S.03 and identifies the product of equal marginal probabilities with the defining square.
- **S.05/S.06:** both actual-matrix statements retain the exact fixed-column data and argument order. They rewrite the left side by S.04 and apply the existing C.54/C.55 respectively, preserving the population N, the fourth-power coefficient 1/4, and all original finite cases. No concentration, conditioning, smallness, or positivity premise was added.

The bound outcome symbol `ζ` is an alpha-renaming of the report's prose symbol `λ`; it changes no binder dependency or term. The compiled declarations have no extra universe identification, nonempty instance, or hidden section parameter. The two modules declare exactly one definition and six theorems, with the frozen names and namespaces, and no further named helper, abbreviation, or instance.

## Empty cases and coordinate meaning

The finite-sum proofs cover empty support and zero-weight outcomes without selecting an element or conditioning. Normalized input laws already exclude an empty outcome type; no extra nonempty assumption appears. When N=0 or N=1, both deck edge sets are empty by the existing support definition, so the generic identity includes those cases directly. The actual matrix bounds inherit the already proved treatment of empty columns, empty/full prefixes, empty alphabets when feasible, zero piles, and zero tail collision factor.

S.01–S.03 permit different laws and different sample types; only S.04 specializes to two copies of the same random edge set. No independence across different edge locations within a deck is assumed. The product constructor independently samples entire outcomes, and the intersection compares the same absolute left edge index. The code performs no sample-dependent recentering, does not use the diagonal coupling, and does not identify an exploration-conditioned or shared-cut coupling with its product law.

## Independent verification

`lake build EdgeLocalization.Overlap.Edges` completed successfully. A separate Lean import checked all seven complete signatures, including explicit universe display, and verified the defining product weight by reflexivity. `#print axioms` for the constructor and all six theorems returned only `propext`, `Classical.choice`, and `Quot.sound`. The source scan found no `axiom`, `sorry`, `admit`, unsafe declaration, or unproved placeholder.

The imports and proof bodies use earlier proved project statements and trusted mathlib finite-sum facts. The result formalizes the exact independent-copy overlap step and its two inherited finite bounds. It does not claim the source's missing spatial saving, asymptotic first-moment margin, stable-block decomposition, or conditional exploration estimates.
