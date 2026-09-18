# Independent statement-design sign-off

Reviewed the exact proposed `MODEL_BRIDGE_CONTRACT.md` on 2026-09-17, after independently reading the authorized unified TeX boundary definitions and counting argument, the current `Riffle` definitions/proofs, the frozen `FirstMoment.Counting` interfaces, and the relevant trusted mathlib finite-type/floor API.

**Decision: approve without corrections.** This approves the proposed seven definitions and B1–B7 for the root agent's freeze procedure. It does not itself freeze the document or introduce an implementation.

The exact namespace, separate module, actual admissible subtype, floor budget, and fixed-budget total decoder are suitable. No added model hypothesis or modification to the original 29 interfaces is needed.

## Statement checks

* **B1:** The sole bound `x.length ≤ D.K` suffices to reindex the existing natural violation set into `Fin D.K`. No legality assumption is needed for cardinality preservation. The support includes every outward digit after the ambient prefix, including a final outward digit in fallback.
* **B2:** The real inequality already stored in `Admissible` implies the natural-floor inequality by trusted `Nat.le_floor`. No new integer-budget or sign premise is required.
* **B3:** The decoder reconstructs ambient digits directly, outward digits from the sparse labels, a genuine final crossing from the tag, and every remaining digit from the fixed extreme large-pile index. Before a crossing, “not crossing and not outward” forces equality with that index. The final crossing cannot itself be outward.
* **B4:** Apply the total decoder to equal codes and use B3 and subtype extensionality. This avoids proving equality of dependent sparse-label functions directly.
* **B5:** The target `BoundaryCode` is finite using the already frozen `SparseAssignment` instance and product instances. After B4, `Fintype.ofInjective` supplies a local finite enumeration of the actual source subtype. `Nat.card_eq_fintype_card`, `Fintype.card_le_of_injective`, and `card_sparseAssignment` give exactly `(K+1)*(k+1)*sparseCount K k budget`.
* **B6:** Equality of the pair codes gives equality of the two admissible words by B4, hence equality of the original pair subtype. Existing compatibility remains in the domain and requires no additional encoding.
* **B7:** The product-code cardinality is the square of the B5 target cardinality. As in B5, finiteness is derived from the proved injection, not assumed and not inferred merely from the default value of `Nat.card` on infinite types.

## Exact edge-case checks

The tag predicate `w.length < x.length ∧ Cross ... (x.length-1)` is essential and correct. A first crossing at length `K` retains its actual digit. A fallback at length `K` uses the sentinel and records an outward final digit if present. If the ambient prefix already has length `K`, the tag is the sentinel and the decoder uses ambient digits throughout. For `K=0`, the word and support are empty and no positive-depth assumption is needed. The first column after the ambient prefix is included. Zero piles cause no missing hypothesis: actual admissible words already satisfy `Legal`, which supplies the digit bound needed for each stored `Fin k` label; the reconstruction does not require all piles to be positive.

The side and ambient word are fixed parameters. No claim is made that a varying side or varying ambient prefix can be recovered from a code lacking those fields. The pair encoder fixes the left/right order explicitly.

## Scope and dependencies

The existing `Riffle.admissible_mem_boundary`, `Riffle.boundary_mem_desc`, and `Riffle.digit_prefix` supply the main projection/prefix facts. Reconstruction must use the full `BoundaryCut` disjunction; the nonterminal-only theorem cannot handle a crossing at `K`. Proof-local finite reindexing and list-element facts suffice for the remaining details. No additional exported helper theorem is needed beyond B1–B7.

The proposed contract correctly limits its conclusion to actual boundary encodings and pair counting. It does not claim an injection of every stable word into `ProfileKey`, nor any probability estimate. The supplemental count can later be used as a component of the actual profile-class encoding without changing the frozen counting definitions.

No Lean implementation, contract edit, additional assumption, or additional axiom was made during this review. The fuller independent design is recorded in `BOUNDARY_ENCODING_INTERFACE_CANDIDATE.md`.
