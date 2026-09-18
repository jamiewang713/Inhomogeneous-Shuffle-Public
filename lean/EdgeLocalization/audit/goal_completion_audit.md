# Completion audit against the full original goal

## Current update: finite collision, occupancy, overlap, exponent, and recentering dependencies verified

The whole-source reread has now led to actual Lean implementation. A separately reviewed contract froze the collision definitions and 58 theorem statements before code; `collision_freeze.json` records the timestamp and hashes. All 58 theorem declarations and their constructed finite model compile. Subsequent independent reviews and freezes selected seven occupancy-slice statements, six independent-copy overlap statements, fifteen exact source-exponent statements, and eighteen ambient-relative coordinate statements, all now verified. Together with the unchanged original 33 declarations, the project has 137 verified finite theorems. The verifiers permit only the standard foundational logical dependencies. Root reviews are recorded in `collision_implementation_review.md`, `conditional_implementation_review.md`, `overlap_implementation_review.md`, `exponent_implementation_review.md`, and `relative_implementation_review.md`.

The new work constructs the independent uniform fixed-column matrix law, proves exact one-/two-label probabilities, implements lexicographic sorting of original labels, transports occupied and collision counts through sorting, and proves the exact collision expectation. It then proves `E[internal edges] ≤ μ²q/2`, `edgeDensity ≤ μ⁴q²/4`, and `edgeDensity ≤ μ`, including N=0/1. These are model-specific finite results, no longer merely universal inequalities for an unspecified law.

The occupancy addendum proves the exact indicator identity `E[C 1_{Z=q}] = choose(q,2) Q P(Z=q)` and the corresponding internal-edge inequality for every q. It retains the original population N in every suffix law and pair factor. Fixed prefix-label membership is proved pointwise before summing pair probabilities; null slices require no division.

The overlap addendum constructs the product law and proves that squared edge density is exactly expected same-coordinate edge intersection under two independent copies. It transfers the existing finite density bounds to that expectation. No independence among positions within one copy is assumed.

The exponent addendum proves the source-preserving identity `μ_x=N^(c_L+ε_w)` with computed signed `ε_w=log_N μ_w-b`, identifies the square-proportion tail product with `N^c_E`, and converts the density bounds exactly. It proves the small coarse exponent `2c_E+8δ+4ε_w`, the singleton-shaped exponent `2c_L+2c_E+4δ+4ε_w`, and the terminal exponent `c_L+ε_w`. No error rate or spatial saving is assumed.

The relative addendum defines the actual ambient cut, proves it lies before every internal child edge, and proves exact count preservation under recentering. Its generic arbitrary-shift bounds use expected cardinalities; they do not equate absolute and relative densities. The exact independent-copy relative-overlap identity and all five exponent consequences now hold in the source coordinate convention.

The full goal remains active and incomplete. Uniform asymptotic conversion, entropy summation, full stable localization/cardinality, endpoint windows/smoothing, the large-block claim, and exploration-conditioned residual laws remain outstanding. The stronger printed small non-singleton statement has not been replaced or declared proved. The next bounded review concerns deriving the vanishing ambient error from the source's actual expected-size asymptotic, with a threshold uniform over child prefixes. This is meaningful progress, not another unchanged blocked turn. The older status tables below describe earlier stages and should be read as historical.

## Update after the user's whole-source reread instruction

The user answered the proposed-contract-change question by asking for a reread of the entire TeX and an identification of the result's true meaning. This is not approval to change the frozen contract. The root and all three independent agents have now reread all 5,221 lines. Their interpretation and the resulting mathematical progress are recorded in `whole_tex_reread.md` and its three independent companion reports.

The reread narrows the earlier diagnosis. The printed small non-singleton factor `N^(-cF)` expresses a conditional random-translation gain, but the final proof only needs decay of the entropy-weighted small-block class contribution. An exact fixed-column collision-pair bound supplies `D_x <= mu_x^4 q_x^2 / 4`. The existing parent-crossing, entropy, and tail-size inequalities then make that contribution decay without endpoint anti-concentration. This also recovers the printed small-singleton exponent and the terminal estimate's finite content. It does not prove the stronger printed small non-singleton inequality or complete the large-block and exploration arguments.

No Lean code, source theorem, or frozen statement changed during this reread. All nine recorded hashes for the three permitted sources, the frozen contract, and the five verified Lean modules were checked and remain unchanged. The verified theorem count remains 33. The newly identified mathematical route has not yet been implemented in Lean.

The earlier consecutive-impasse count below is historical. The user's new direction led to substantive progress; it should not be treated as an unanswered approval request or another unchanged blocked turn.

## Earlier audit, before that instruction

The goal remains the complete assigned formalization, not the 33-statement finite subset. The previous goal turn made progress by producing independent source audits, the full proof map, a frozen finite subset, compiler-checked proofs, and logical-dependency records. It did not achieve the original goal.

The present continuation re-read the current source statements and compared current source/Lean hashes with the freeze and verification records. All three permitted source hashes, the frozen contract hash, and all five implementation module hashes match. All five compiled module objects exist. No live external job is being awaited. The approval request concerns a change to mathematical statements, not completion of an existing build.

| Original requirement | Authoritative evidence | Completion verdict |
|---|---|---|
| Structure of entire upper/lower/random-pile proof | whole_proof.md; source_declarations.json; all three independent reports; 70 active and 11 inactive declarations | Completed as a source dependency audit, not as Lean proof of the whole paper |
| Dependencies of definitions and lemmas | whole_proof.md's 70-row conceptual dependency table; exact declaration catalogue | Completed as a source audit; unresolved inputs are labelled |
| Identify concentration/stable-block inputs | whole_proof.md final input table; independent reports | Completed; several required inputs are false or insufficient |
| Multiple independent agents reconstruct/design/audit each planned lemma, compare before implementation | Three reports; comparison.md; frozen contract timestamp; F01–F33 reviews | Completed for every implemented lemma; no full analytic target has been implemented without review |
| Freeze before code; preserve assumptions; no extra hypotheses or new axioms | frozen_contract.md and matching SHA; implementation_review.md; verification.json; logical_dependencies.log | Verified for the finite subset |
| Per-edge stable localization | Deck.localize_internal_edge proves prefix containment only; source coverage statement omits ambient/truncation event | Full target incomplete; printed coverage false as stated |
| Bound on relevant stable blocks | No such Lean declaration; reports identify missing quantitative parent separation and K=0 handling | Incomplete; existing endpoint tail does not prove the bound |
| Endpoint-window bounds | No Lean window theorem; reports distinguish repairable window gaps from false atom theorem | Incomplete; exact ambient conditioning/centering needs specification |
| Large-block edge-density bounds | No Lean asymptotic theorem; independent reports provide direct counterexamples | Contradicted under original definitions |
| Small non-singleton bounds | No Lean asymptotic theorem; exact_density_obstruction.md supplies an exact-probability contradiction | Contradicted under original definitions |
| Small singleton bounds | Direct collision-moment decomposition identified; full fixed-column moment/product model absent | Incomplete, although mathematically recoverable |
| Terminal singleton bounds | Density.internal_density_le_expected_occupancy is the exact finite core; source mean/exponent wrapper absent | Partial, not completion of the requested source theorem |
| Internal shuffle-graph edge estimates | Deck injects adjacent edges into colliding pairs; Density proves expectation domination | Partial; conditional fixed-column tail-collision product remains unimplemented |
| Every case distinction explicit | N=0/1, empty ranges, equal-row containment, balanced-column empty piles and zero slack handled in Lean | Verified for the finite subset only; analytic branch coverage is incomplete |
| Ask multiple agents for different decomposition if stuck | Independent alternate F12 decompositions; source-preserving alternate-decomposition reports; current exact blocker cross-check | Completed where invoked; no alternate proof can prove the contradicted conclusion |

## Impasse recorded before the whole-source reread

The original analytic collection includes a false assigned conclusion under its own fixed-column law and good-profile/margin hypotheses. A sound Lean proof of every requested statement with the same definitions therefore cannot exist. The finite subset cannot be counted as success, and adding an assumed concentration/collision interface would not resolve this.

The frozen implementation has no unfinished proof bodies. New corrected analytic definitions/statements require a separately authorized, independently reviewed freeze. An explicit user choice has been requested; elapsed time or another automatic continuation is not authorization to change the mathematical contract.

Blocker audit: this is the second consecutive goal turn observing the same condition (original source statements contradicted while contract changes are not authorized). The first turn also made substantial formalization progress. The goal has not been marked complete or blocked at this point; the three-turn blocked threshold has not yet been reached.
