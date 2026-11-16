# Independent review of uniform asymptotic density estimates

I independently read every theorem signature and proof in `Asymptotic/Estimates.lean` and compared A.03–A.07 with `frozen_asymptotic_contract.md`. **All five statements and proofs preserve the frozen meanings and quantifier order. I found no mathematical defect, added premise, extra declaration, or loss of the promised uniformity.** No implementation or frozen report was edited.

Reviewed source SHA256: `0b1db2065de328d80b16e4cb7bac2446da31a658d05f0c857a494ff89186a0fe`.

Frozen contract SHA256: `659ee8a94a40e3c4cd7b607409d42297f0d0d41fe41c6414d9a3d9ca30aff8a8`.

The root reported that this module compiled on its first build at the default compiler limits. After the independent source comparison, the root reported the full asymptotic verifier passed at 22:47:36 UTC: all seven frozen theorem statements and the one definition matched, all twenty-five prior implementation modules and the source/contract/pre-review hashes were unchanged, and axiom dependencies were confined to `propext`, `Classical.choice`, and `Quot.sound`. This full-verifier result is root-reported; I did not rerun it. I authored the separate Error module and compiled/inspected its two theorems, so those implementation checks are not claimed as an independent review of Error here.

## Common signature fidelity

Every theorem has exactly the explicit ordered family parameters k, K, A, n, hn, hA, w, b, the HasSizeExponent hypothesis, and positive requested accuracy epsilon. The hypothesis remains on actual expected sorted occupancy under the existing original-N matrix law. It is not changed to a hypothesis on prefixMean, a computed error, a conditional law, or the desired density bound.

Every conclusion first chooses a natural N0 with 2<=N0, then quantifies over N and its threshold proof. All child lengths, length proofs, words, extension relations, and legality proofs occur afterward. In the two small-case theorems, delta is also universally quantified after N0 and N's threshold proof, before the child data. No prefix sequence or child is chosen before the threshold. The density in each conclusion uses the actual samplewise ambientLeft of the fixed ambient word at that N, with the original population and unchanged relative-coordinate model.

The named proof binders hprefix, hx, and hsmall occur in the frozen forall conclusions and are introduced and used by their proof bodies. A linter warning that such a binder name is unused in the proposition's subsequent syntax is not an omitted assumption or a reason to remove it. Their exact frozen binders are preserved.

## A.03: uniform fourth-power exponent

The proof obtains A.02's error cutoff at tolerance epsilon/4 before introducing N or any child data. Positivity of this tolerance follows locally from positive epsilon. The resulting cutoff and its bound two are retained directly. Thus it cannot depend on M, x, either length proof, the extension relation, or legality.

At an arbitrary allowed child, N>=2 is derived by transitivity. The upper side of the proved absolute ambient error bound gives `error<=epsilon/4`; the family ambient length proof hA(N) and the child's derived proof hAM.trans hM agree by proof irrelevance. There is no new identity premise and no child-dependent error function.

The existing finite relative theorem R.14 supplies the exponent `4*(L+error)+2*E`. The sole final linear input is the proved error upper bound, which gives the desired `4*L+2*E+epsilon`. Positive-base real-power monotonicity and division by four preserve the bound. The conclusion retains the exact coefficient 1/4. No sign on the error, tail exponent, or child size exponent is assumed.

## A.04 and A.05: joint uniformity in delta and every child

Each proof obtains the A.03 threshold at the requested accuracy before introducing delta. Its introduced argument order is exactly N, threshold proof, delta, M, hM, hAM, x, hprefix, hx, hsmall. The same A.03 threshold therefore works simultaneously for all real delta and every legal child at that N.

A.04 changes `4*L+2*E+epsilon` to `2*E+8*delta+epsilon`; A.05 changes it to `2*L+2*E+4*delta+epsilon`. Both linear comparisons use only the strict source cutoff L<2*delta. Neither replaces it by a cutoff on L plus the ambient error or demands a sign for delta. Both retain the divisor four, the exact tail coefficient two, and the single requested accuracy epsilon. No stable-singleton predicate or negative fluctuation saving has been inserted into the singleton-shaped theorem.

## A.06 and A.07: uniform mean and terminal estimates

A.06 obtains its error threshold at tolerance epsilon before introducing all child data. It takes the proved upper side of the ambient error estimate, applies the existing R.17 relative mean exponent bound, and compares L+error with L+epsilon. There is no denominator, extra tail term, factor four, smallness assumption, or child-dependent cutoff. It may use a different ambient-only cutoff from A.03, as the exact separate existential statement permits; each conclusion retains its promised uniformity.

A.07 first obtains the uniform A.06 threshold, then introduces an arbitrary full-length legal child. It specializes M to K(N), hM to the reflexive inequality, and hAM to hA(N). The conclusion is exactly the frozen terminal expression. No new terminal-size, singleton-family, or tail-positivity hypothesis occurs. The already proved X.13 still supplies E=0 at full length without adding another declaration.

## Boundary cases and interpretation

The finite model data remain total at N=0 and N=1, but the conclusions themselves prove an eventual cutoff at least two. The proof does not assume low-N legality or positivity. It relies on the separately proved A.02 consequence of the two-sided actual-occupancy size hypothesis, whose lower bound derives eventual positivity. Empty/equal/full-length prefixes, variable K(N) and A(N), valid empty-column/alphabet cases, selected singleton piles, and zero fixed-count tail factors remain covered by the unchanged finite inputs.

The family w(N) is deterministic and fixed as input, though its length and digits may vary with N. The obtained threshold is uniform over all children of that family and, in the small cases, all real delta. It is not asserted uniform over an additional collection of ambient families, random exploration histories, or retained profile classes without their own uniform argument. No convergence rate or profile approximation is introduced.

Exactly five new theorem declarations occur in the reviewed module; all other proof facts are local. The implementation turns the precise ambient expected-size assumption into the intended eventual relative small and terminal numerical bounds. It does not establish the stronger minus-cF spatial estimate, stable-family classification, endpoint windows, or the remaining first-moment aggregation.
