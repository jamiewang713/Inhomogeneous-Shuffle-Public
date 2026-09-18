# Counting implementation coverage

Implemented only the frozen finite targets F16, F17, and F19 in
`RiffleProfiles/Counting.lean`, namespace `RiffleProfiles`.

| Frozen target | Declaration | Exact content |
|---|---|---|
| Definition | `lowCount` | Natural sum `sum_{q<=K,q<=h} choose(K,q) k^q` |
| Definition | `tailWeight` | Real sum `sum_{q<=K,h<=q} choose(K,q) a^q` |
| F16 | `tailWeight_le` | For `a>=0`, `z>=1`, the tail is at most `(1+a*z)^K/z^h` |
| F17 | `lowCount_le` | For `0<z<=1`, the cast of `lowCount` is at most `(1+k*z)^K/z^h` |
| F19 definition | `SparsePattern` | A subset of `Fin K` with at most `h` positions and a function from that subset to `Fin k` |
| F19 | `sparsePattern_card` | Exact cardinality `lowCount K h k` |
| F19 | `sparsePatternForget` | Forgets labels and returns the selected subset |
| F19 | `sparsePattern_forget_image_card_le` | The finite forgetful image has cardinality at most `lowCount K h k` |
| F19 definition | `BoundaryDescriptor` | Stop length, final digit, and labelled deviations strictly preceding the final position; empty extensions have final digit zero |
| F19 | `boundaryDescriptor_card_le` | Frozen premise `2<=k`; cardinality at most `k(K+1)lowCount(K,h,k)` |
| F19 definition | `ProfileDescriptor` | Two boundary descriptors, one labelled exceptional sparse pattern, and D counts in `{0,...,K}` |
| F19 | `profileDescriptor_card_le` | Frozen premise `2<=k`; the exact product bound from the contract |

One private algebraic helper, `sum_choose_mul_pow`, is the trusted binomial
theorem specialized to `1+a`. It adds no assumption. F16 and F17 use finite
sum monotonicity and the appropriate monotonicity of natural powers. The
sparse-pattern equality uses sigma/function cardinalities and partitions the
powerset by subset cardinality. Descriptor bounds use subtype and product
cardinalities.

The definitions permit K=0, h=0, h>K, k=0 for sparse patterns, and zero
weights. No special-case hypothesis was added to avoid those cases. The
source premise k>=2 was retained on the two boundary/profile theorems even
though their cardinal inequalities also admit a more general domain.

Validation: the module compiled under the workspace's pinned Lean 4.19.0
runtime and mathlib, with warnings treated as errors, using
`python3 lean_formalization/check_lean.py lean_formalization/RiffleProfiles/Counting.lean`.
There are no new axioms, `sorry`, `admit`, or placeholder theorem declarations.

The module does **not** claim a map from actual source boundary prefixes into
the finite descriptor type; that is a separate, unimplemented source-to-model
bridge. It also does not claim the asymptotic `N^epsilon` conclusion: the
finite generating bounds and exact descriptor count are the inputs for that
separate wrapper. Coarse profiles are not silently replaced by labelled ones;
the forgetful image is explicitly distinct.
