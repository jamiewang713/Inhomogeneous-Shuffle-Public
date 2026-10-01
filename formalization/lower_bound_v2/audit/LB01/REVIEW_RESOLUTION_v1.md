# LB-01 pre-proof review comparison and resolutions

The mathematical, Lean representation/orientation, and hypotheses/counterexample reviewers independently inspected the raw source and the frozen targets before implementation. Their findings were delivered to the lane owner on 2026-10-01 and are retained in the respective *_review_v1.md reports. All agree the frozen eight targets are mathematically sound with their existing quantifiers. No target or shared definition is changed.

| Finding | Resolution for implementation |
|---|---|
| Exchangeability alone must be connected to the particular componentSort representation | Prove a deterministic row-relabel/stable-sort identity and average over an independent uniform permutation. Prove that componentIndex equality is exactly sorted-word equality. |
| Uniform assignment conditioned on a full multiset requires an actual argument | Use an unconditional joint finite-sum identity with an arbitrary multiset test. Prove the product-factorial stabilizer/fiber cardinality separately. No target proposition is evidence. |
| Same-sample physicalInverse=stableSort is false (N=2; columns (0,1),(1,0)) | Prove a triangular column-pullback equivalence, then pass to its uniform pushforward. Never assert the false pointwise identity. |
| Earlier/later priority can change laws (N=3; cuts (2,1),(1,2), mass 2/9 versus 1/9) | Retain chronological forward fold, reverse chronological inverse steps and earlier-column lexicographic priority exactly. |
| Uniform pi marginal alone does not imply independence from G | Keep the explicit nested independent PMF bind/map of the frozen graphMixtureLaw. |
| Canonical source graph adapters require positive N and k≥2, unlike the frozen targets | Prove generic finite ordered-key helpers valid in the degenerate cases directly; use restricted adapters only when their premises are discharged. |
| Finite testing is evidence against mistakes, not proof | Exhaustive checks (33,300 samples, 1,775 profiles, 5,078 multiset fibers, 2,142 graph/permutation pairs) are labeled sanity checks. Kernel-checked proofs and axiom closure are separate delivery requirements. |

The coordinator acknowledged INTERFACE_PROPOSAL_v1.md in the new, immutable audit/LB00/LB01_INTERFACE_ACK_v1.md. It requires no contract amendment and preserves all eight exact exported targets. The lane uses the original CONTRACT_READY v1 plus that acknowledgement as its input receipt. Local helpers live only under Model/; builds use the frozen lane entry point, serialized by audit/LB01/compile_lane.py. No completed-input receipt is issued until every acceptance obligation, including the physical bridge, is proved and reviewed.
