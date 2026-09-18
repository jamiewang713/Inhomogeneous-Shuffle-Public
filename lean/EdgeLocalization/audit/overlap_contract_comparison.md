# Root comparison before the overlap freeze

The root reread the exact shared-edge identity in the permitted TeX at lines 1837–1841 and the fixed-column paper's Lemma 4.13 before comparing all three independent reports. The selected inventory is exactly S.D01 and S.01–S.06 in `overlap_contract_statements.md`, with their displayed parameter order and conclusions. No additional named helper is selected. The module layout is `Overlap/FiniteLaw.lean` for the constructor and S.01–03, and `Overlap/Edges.lean` for S.04–06.

| Role | Independent finding | Comparison decision |
| --- | --- | --- |
| Reconstruction | Expected same-position intersection is a sum of products under two independent laws; the self-copy case gives the density square sum. All six proofs follow from the proposed product weights and existing finite/cardinality/density results. | Accepted. Construct the product law and prove its normalization rather than assuming an intersection formula. |
| Statement design | One literal-weight product constructor and six complete signatures suffice. The support type needs only decidable equality, the sample laws may differ, and the real integrand is unrestricted. | Accepted exactly. Use the listed names, order, fields, and module layout. |
| Hidden cases | Squares require the same law and observable in both copies. Empty supports, all deck sizes, null events, and zero factors do not require extra premises. Separate random recenterings need not preserve overlap. | Accepted. S.04 uses the same N, row map, prefix, and absolute edge labels; S.05–06 use the actual deterministic-count self-product law. |

The generic support hypotheses in S.03 are pointwise finite-set containment, not shuffle hypotheses or concentration assumptions. Both are retained exactly as specified. S.04 discharges them with the already proved internal-edge support theorem. Its sample type need not be separately assumed nonempty; a normalized law is already given. No positivity, uniformity, edgewise independence, integrability, sorting-independence, or conditional-preservation premise is introduced.

The source's expected common-edge quantity is distinguished from both the square of the expected edge count and the second moment of the edge count. The first is bounded by the second expression via the existing collision estimate, but they are not defined to be equal. Only independence of complete copies is needed for the proposed overlap identity; locations within a copy may be dependent.

The comparison does not alter the three earlier freezes, the 98 existing theorem statements or their proofs, or any permitted mathematical source. It does not turn the printed spatial `−c_F` claim into the collision bound and does not infer equality of absolute and randomly recentered densities. It selects an exact proof of the interpretation itself plus two consequences of the already proved finite estimates.

All three reviewers were asked to compare their independent reports with the complete exact signature report and append final acceptance before hashing. The freeze must include those final report versions and this comparison. No Overlap Lean file has been written before this comparison.
