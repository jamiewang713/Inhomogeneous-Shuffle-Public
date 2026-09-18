# Candidate source profile counting and exact finite specialization

Not frozen. No new Lean implementation is authorized until all three independent reviews are compared. This batch uses the literal source profile definitions in the existing project `RiffleTimeProfile/Digits.lean`, not a substituted labelled profile. The three supplied mathematical sources remain the only paper references.

## Reviewed dependency compatibility plan (before any changes)

The existing Analysis, Digits and DigitEstimates project modules are not yet imported in the checked library. A read-only Lean4.19 test of a verbatim Analysis snapshot found proof/syntax compatibility issues: the field_simp-only cancellation in finite_gibbs needs ring; continuous_finsetSum is named continuous_finset_sum in pinned mathlib; the anonymous local Fintype binder is expressed as letI in Lean4.19. Candidate local compatibility copies may change only those proof steps and other reviewed version-specific proof syntax needed to check the existing declarations, never a theorem header, definition body, source assumption, or original file. Any further change requires its own reviewed exact diff before it is made. The existing checked Base/Ambient compatibility copies remain immutable.

## P01: raw counts and the source coarse profile

For arbitrary k,K,R,N, profiles p:Fin K→Simplex k, partition P, timeClass:Fin K→Fin R, chi:Real, full word omega, and endpoints v,M:Nat, define rawCounts at a key in Fin R×Fin P.cellCount×Fin k as the natural cardinality of the exact goodPositions fibre already defining TimeProfile.digitCount. Prove rawCounts≤K and digitCount=rawCounts/logScale N. Define the literal coarseProfileData to be (digitCount function, exceptionalPositions), with no exceptional labels. Prove equality of these data is exactly TimeProfile.SameCoarseProfile for fixed endpoints. Also prove our T06 sourceExceptionalPositions definition equals the existing exceptionalPositions filter for any endpoints, including word-dependent choices pointwise.

## P02: finite number of actual coarse profile data

Assume N≥2. Let I be any index type (no finiteness assumption), word:I→(Fin K→Fin k), v,M:I→Nat, and Q:I→Prop be arbitrary. Assume only that Q(i) implies the actual exceptional set for word(i) at endpoints v(i),M(i) has cardinality≤h. Take the set of actual source coarseProfileData values for all i with Q(i).

Prove this image set is finite and its Nat.card is at most

lowCount K h k * (K+1)^(R*P.cellCount*k).

Construct a finite code for each realized datum: the actual exceptional positions labelled by word(i) on that set, and the raw good-count array with values in Fin(K+1). Decode by forgetting the exceptional labels and dividing raw counts by logScale N. Thus the actual data image is contained in the decoded range of a finite code type. Do not claim that source coarse data contain exceptional labels or that the word-to-profile map is injective. No regularity, legality, endpoint order, full-support, finite-I or k≥2 assumption is needed. k=0 is handled automatically by actual labels from the selected full word, rather than by adding a nonempty-alphabet premise.

## P03: actual boundary-pair/coarse-profile image

Use existing Model D and Setup A, an arbitrary partition P of Simplex D.k, and timeClass:Fin D.K→Fin R. An input consists of an actual admissible boundary pair, a full index omega, and any natural endpoint M. Set v to the length of the existing join of that pair. Let Q be any predicate on these inputs. It can restrict retention, stopping, legality, or any desired family, but the counting theorem assumes none of those conditions beyond the existing admissible-pair domain.

Take exactly the set of (boundary pair, coarseProfileData at v,M) values obtained from inputs satisfying Q and actual exceptional card≤h. Prove it is finite and its Nat.card is at most

D.k^2*(D.K+1)^(R*P.cellCount*D.k+2)
 * (lowCount D.K (floor(boundaryThreshold A)) D.k)^2 * lowCount D.K h D.k.

Use P02 for the actual coarse-data image and T05 for the actual pair type. Natural endpoints and multiple full extensions are discarded by image semantics; they are not separate factors in the count. The count does not require injectivity of the word-to-profile map.

For its source-prefix consequence, fix any family of triples (y,z,x) whose pairs are AdmissiblePair and whose x is Legal D and extends the join. Use the existing full_extension theorem to obtain a full word extending each x and fullList_of_full to pass to FullIndex. Prefix digit equality proves that the source data at v=|join|,M=|x| are independent of the full extension and belong to the preceding image. Prove this independence and inclusion, with no chosen full-extension premise inserted into the source family. Restrict to exceptional card≤h. In particular the result applies to actual retained stable source prefixes after their already proved legality/join-prefix facts are supplied. No variance, integration, or stopping-time assertion is assumed by this finite count.

## P04: actual source cL decomposition

Preserve the exact existing source D08 profile_cost_replacement statement and all its binders (N≥2, chi>0,C≥0, regularity, w≤v≤M≤K, LegalPrefix): both its good-position-cardinality error and the coarser (M−v) error. Register it as a checked source consequence and connect its good-cost sum, exceptional-cost sum, and normalized count definitions to our frozen F04–F06 forms by exact finite-sum identities. The actual ambient length w is retained. No floor(r log N) replacement or limiting-time equality is made.

## P05: actual source entropy/KL specialization

Preserve the exact existing D11 profile_entropy_bound statement (N≥2,chi>0,theta in[3,4], arbitrary endpoints/timeClass, no regularity or legality added):

profileH ≤ theta*profileS − sum_a digitTotal(a)*psi(P.rep(a.cell),theta).

Identify profileH with the source's zero-aware total-weighted Shannon formula via the already proved DigitEstimates.profileH_source_formula, preserving that theorem's original binders when reused. Preserve existing exceptional_psi_error and its explicit interval [0,4 log(k)*profileR] under k≥2,N≥2,theta in[2,4]. The finite good/exceptional partition and psi bound derive this error. No integrated time correction is asserted in this batch.

Previously proved project lemmas may be reused only after the complete dependency copies compile and their transitive foundations are checked. Every source adapter must make its dependency and any remaining integral/limit obligation visible. These source statements do not assert that Q_x or cL are constant on the literal coarse profile; that assertion remains false in general and no label-free word-class size bound is introduced.
