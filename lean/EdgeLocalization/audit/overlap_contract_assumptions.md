# Independent assumptions audit: shared-edge overlap

This is a pre-code audit of the proposed one-definition, six-theorem overlap addendum. I reread the permitted TeX's first-moment identity at lines 1837–1841 and its independent-graph premise immediately above it. I also reread `2510.22783v1.pdf`, Lemma 4.13, printed p. 27, and `2103.05068v3.pdf`, Lemmas 5.2–5.3, printed p. 29. No existing source, freeze, implementation, or prior review was changed, and no Lean code was written.

**Verdict: the proposed finite product-law and same-position overlap route is mathematically valid, with no new probabilistic assumption.** Its final matrix bounds are exact consequences of the already proved collision estimates. A final exact statement/signature report should still be compared before the new freeze.

## Source meaning and scope

The TeX writes the shared-edge first moment as the sum over positions of squared single-graph edge probabilities. The preceding proposition explicitly takes two independent graphs. The older fixed-column argument makes the same equality before its block decomposition. This identity concerns the same edge coordinate in two independently sampled graphs with the same distribution.

The older independent-digit paper also distinguishes the general overlap `sum_i P(i in A) P(i in B)` for independent, possibly differently distributed sets from the square sum for an independent copy of the same random set. Its subsequent conditional-copy inequality is a different statement; it is not part of the proposed addendum.

The addendum constructs the requisite product law directly. It does not assume an arbitrary coupling has independent coordinates, and it does not condition the two samples on shared internal information or an exploration event.

## The one definition

For finite sample types Ω and Λ with already given normalized laws w and v, define `FiniteLaw.prod w v` on Ω×Λ by

```
weight(ω,λ) = w.weight(ω) * v.weight(λ).
```

Nonnegativity follows from the two weight nonnegativity proofs. Normalization follows by splitting the finite product-type sum and using the two existing total-weight identities. These are constructor proofs, not additional fields asserting a desired probabilistic property.

No additional `Nonempty Ω` or `Nonempty Λ` assumption is needed. A normalized finite law already rules out an empty outcome type, although that consequence need not be a constructor argument. An empty deck or empty edge support is different: its matrix sample space is still a nonempty space of empty assignments, and the product law exists normally.

The constructor permits different finite sample types, universes, and laws. It must not require uniformity. Its self-product is a later specialization with v=w, using two independently chosen coordinates even though their types agree.

## All six proposed theorem boundaries

### 1. Product expectation

For arbitrary `f : Ω × Λ → ℝ`,

```
E_(w.prod v) f = E_w (fun ω => E_v (fun λ => f(ω,λ))).
```

This is an exact identity of finite real sums. It must retain arbitrary signed f, with no nonnegativity, boundedness, integrability, support, or positivity hypothesis. Reindex the product sum and distribute the weights; there is no limit argument and no new assumed factorization interface.

### 2. Rectangle probability

For arbitrary events A on Ω and B on Λ,

```
P_(w.prod v)(A(ω) and B(λ)) = P_w A * P_v B.
```

The two events depend on their displayed separate coordinates. The indicator multiplication identity follows by the four truth-value cases, or the corresponding trusted finite indicator identity. No event probability is assumed positive. An event allowed to inspect both coordinates is not generally a rectangle and cannot use this formula without proving that structure.

### 3. Expected intersection cardinality

For an arbitrary element type α, a finite support s, and functions

```
H : Ω → Finset α,
J : Λ → Finset α,
```

with the explicit pointwise inclusions `H(ω)⊆s` and `J(λ)⊆s`,

```
E_(w.prod v) #(H(ω) ∩ J(λ))
  = sum_{i in s} P_w(i in H) * P_v(i in J).
```

The common finite support is a finite-indexing condition, not a concentration or distributional estimate. The element type itself need not be finite; the graph specialization uses α=ℕ. Use an existing decidable-equality instance or local classical decidability for finite sets, without adding `Fintype α`.

Apply the already proved expected-cardinality identity to the intersection, whose support inclusion follows from the supplied inclusions, then apply the rectangle formula to each membership event. The right side is a sum of products even if Ω=Λ: it becomes a square only when the two marginal random-set distributions match.

### 4. Self-law edge density

For an arbitrary existing finite law w, natural N, random row map `R : Ω → ℕ → List ℕ`, and the same fixed prefix x in both copies,

```
edgeDensity w N R x
  = E_(w.prod w) #(internalEdges N (R ω) x ∩ internalEdges N (R λ) x).
```

Use common support `range(N−1)` and the already proved pointwise support inclusions. The two factors in each summand are identical probabilities, so their product is the defining square.

The theorem must use the same law, row map, prefix, and N in both copies, as proposed. Sharing only the law while using different row maps or prefixes would generally give a mixed product sum rather than `edgeDensity w N R x`. The generic intersection theorem already covers that broader setting without a square claim.

The row maps need not be sorted for this generic identity: the existing finite edge definition is used exactly. The actual shuffle-graph specialization below uses the already constructed sorted rows.

### 5. Actual matrix overlap bounded by the fourth-power expression

For the unchanged feasible fixed-column data n, hn and bounded vector prefix x, take w=`matrixLaw n hn` and R=`sortedRows n`. Under the newly constructed self-product law,

```
E #(internalEdges(prefix x, first sorted matrix)
      ∩ internalEdges(prefix x, second sorted matrix))
  ≤ prefixMean(N,n,hM,x)^4 * tailCollisionFactor(N,n,M)^2 / 4.
```

This follows by the exact identity in theorem 4 and existing C.54. It adds no N≥2, small-block, stable-block, concentration, spatial, or independence assumption. In particular it is not a new assertion about the printed −cF bound.

The two matrix samples have the same deterministic count array and prefix. A product of different cut laws is allowed by theorem 3 but is not this self-density specialization; do not substitute this bound for such a mixed overlap without a separate proved comparison.

### 6. Actual matrix overlap bounded by the prefix mean

With the same data and self-product law,

```
E #(shared internal prefix edges) ≤ prefixMean(N,n,hM,x).
```

This follows by theorem 4 and existing C.55. It holds for every permitted prefix, including the terminal/full-word prefix, and does not assume a small expected block size. No occupancy-conditioned or exploration-conditioned model is inferred.

## Empty, different-law, and coordinate cases

- **Empty finite support s:** both pointwise inclusions force the random sets to be empty. The intersection cardinality and the finite sum are zero, while the sample laws may be perfectly nontrivial.
- **One empty random set or null membership event:** its contribution vanishes. No positive marginal probability is required anywhere.
- **N=0 or N=1:** `range(N−1)` is empty by natural subtraction, so both edge sets, their intersection, and edge density are zero. The product of the two actual matrix laws remains well defined.
- **K=0:** all matrix rows are empty words. For the forced empty prefix, each graph has N−1 deterministic path edges; the intersection and density are N−1. The tail factor is 1 and the prefix mean is N, so both inherited upper bounds remain correct, including the two small-deck cases.
- **Empty prefix:** both copies use that same empty prefix, so the identity concerns all edges. It is not a mixed-prefix intersection.
- **Full-length prefix:** the tail factor is 1 and the mean bound includes the terminal case. Repeated full words and arbitrary sorting ties are allowed by the existing sorted-row construction.
- **Empty alphabet:** when a column exists, feasibility forces N=0; when K=0 the empty matrix and empty prefix exist for every N. The overlap construction does not choose an alphabet digit.
- **Zero or one selected pile count:** existing collision bounds already give the relevant zero edge cases. The overlap identity introduces no new positivity restriction.
- **Different laws or different row maps:** theorem 3 gives products of the two marginal probabilities. The square identity is a self-copy specialization, not a general coupling identity.
- **Common finite support larger than necessary:** extra indices have at least one zero marginal and do not change the identity. For edge density the chosen support is exactly the existing path-edge range.
- **The two coordinate sample types happen to agree:** this does not couple the samples. The product constructor still weights (ω,λ) by w(ω)v(λ), rather than constraining λ=ω.
- **A shared conditioning event across the two copies:** the unconditioned product law does not represent such a joint conditional distribution automatically. No result here asserts that it does.

## The recentering caveat is essential

The intersection is formed in one fixed coordinate type, with the same position i in each copy. For the actual sorted deck these are the existing absolute zero-based path positions. The one-based source notation is obtained by adding 1 to both positions, a common deterministic relabeling.

Separate sample-dependent translations preserve each graph's edge count but need not preserve intersection cardinality or squared marginal probabilities. For example, let a random set be {0} or {1}, each with probability 1/2. Its expected intersection with an independent copy is 1/2. Moving each copy's own point to 0 makes the expected intersection 1. Thus the new generic identity also applies to separately defined relative-coordinate random sets, but it does not equate their overlap with that of the absolute-coordinate sets.

The planned actual-matrix theorems use the existing `sortedRows` and `internalEdges` definitions directly. They must not be described as proving equality with randomly recentered ambient overlap or as resolving the ambient/exploration coordinate obligations found in the whole-file reread.

## Dependencies and pre-freeze acceptance

Construct the single product law first. The finite expectation and rectangle identities follow directly from its weights. The finite intersection theorem uses the rectangle identity and the existing expected-cardinality theorem. The self-density identity uses the intersection theorem and existing edge support. The two actual matrix bounds then use that identity with the already proved C.54 and C.55.

No new named helper is mathematically necessary beyond the proposed six theorems. Generic finite sum manipulation, support inclusion, indicator cases, and square multiplication can be local proved steps. The proposed semantics are accepted subject to comparison of the exact final signatures before freezing. No change to any earlier assumption, theorem, definition, or coordinate convention is required or authorized by this addendum.

## Final-signature comparison and acceptance

I have now compared every signature in `overlap_contract_statements.md` and the complete independent `overlap_contract_reconstruction.md` with the audit above. **I accept S.D01 and S.01–S.06 exactly as specified, with no remaining pre-freeze correction.** No Lean implementation was written in this audit.

S.D01 retains the definitionally multiplicative product weights and proves both law fields internally. S.01 retains arbitrary real-valued integrands, including signed functions, and the stated factor order. S.02 has exactly the two separate-coordinate events, with no public decidability, positivity, or independence assumption. S.03 permits different finite sample types and different laws, keeps only decidable equality on the arbitrary element type, and retains both stated pointwise inclusions in the common finite support. Its sum is a product of marginal probabilities; no square is inferred there.

S.04 has exactly one law, N, row map, and prefix, used identically in both independently drawn coordinates. Its equality direction, natural subtraction in the existing support, and use of the same absolute position agree with the frozen density definition. S.05 and S.06 retain the existing feasible fixed-column data in the same argument order and inherit precisely C.54 and C.55, including the coefficient 1/4, the original population N in the collision factor, and all empty, zero-factor, full-prefix, and N=0/1 cases. Neither statement adds a concentration, positive-size, small-mean, conditioning, or recentering premise.

The agreed dependency order and proposed file allocation are valid: `Overlap/FiniteLaw.lean` contains S.D01 and S.01–S.03, while `Overlap/Edges.lean` contains S.04–S.06. The six proofs require no additional named helper declaration or custom instance. This acceptance concerns the exact finite same-position identities and inherited bounds; it does not identify an arbitrary coupled or conditioned pair with the product law, or prove any missing spatial localization or asymptotic first-moment estimate.
