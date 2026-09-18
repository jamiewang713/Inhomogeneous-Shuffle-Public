# Proposed additive contract for occupancy slices

This is an independent statement-design report for a new comparison and freeze. It leaves the existing v1 and collision freezes, their Lean implementations, and all three permitted source files unchanged. It authorizes no Lean implementation before the new comparison and freeze.

The bounded target is the finite conditional internal-edge estimate appearing in the permitted TeX at lines 1516–1523. The source conditions on the number of rows with a fixed prefix and uses the exact tail factor with denominator `N(N−1)`. The fixed-column law is stated at 446–451; the sorted internal-edge definition is at 460–467; independent columns are explicit again at 2921–2923 and in the factorial calculation at 4360–4367. I reread those passages for this report.

The result below counts a fixed occupancy event without dividing by its probability. It is distinct from conditioning on the internal information `U_x` at 1530–1541, and from the exploration sigma-field at 1923–1943. Neither latter conditional model is asserted or assumed here.

## 1. Exact data, existing definitions, and probability space

The common deterministic data are:

- `N K k M : ℕ`;
- `n : Fin K → Fin k → ℕ`;
- `hn : ∀ j : Fin K, ∑ a : Fin k, n j a = N`, for statements that use a law;
- `hM : M ≤ K`;
- `x : Fin M → Fin k`, for statements about a prefix.

`hn` is the original column-size condition, not a conditional-law hypothesis. The count values are natural numbers and may be zero. There is no extra positivity assumption on `N`, `k`, `K`, `M`, the digit counts, or the occupancy-slice probability. No good-shuffle, stable-block, concentration, or asymptotic hypothesis is introduced.

The following are existing implemented declarations and are used unchanged:

- `FixedMatrix N n`, the finite product of the actual prescribed-count column subtypes;
- `matrixLaw n hn`, the constructed product of the uniform column laws;
- `prefixWord x`, the source prefix encoded as `List ℕ`;
- `rawRow n ω i`, `rawRows n ω`, and `sortedRows n ω`;
- the frozen `occupied`, `occupancyCount`, `collisionPairs`, and `edgeCount` definitions;
- `tailCollisionFactor N n M`, with absolute column indices and population `N`.

The prefix is allowed to request zero-count digits. The existing list/vector bridge covers every in-alphabet source word; applying these theorems additionally requires its length bound `M≤K`. Legality in the logarithmic source sense is not a new premise.

All seven proposed theorems quantify over the actual existing probability space. There is no abstract distribution argument with a desired conditional formula supplied as a premise.

## 2. Complete new definition inventory

There are exactly **three** proposed new definitions, grouped as O.D01 and O.D02. All names are in namespace `EdgeLocalization`. `Conditional` is a module directory, not another namespace. There are no new named custom instances.

### O.D01: split count arrays

**`prefixCounts`** has the exact signature

`{K k M : ℕ} (n : Fin K → Fin k → ℕ) (hM : M ≤ K) : Fin M → Fin k → ℕ`.

Its value is

`prefixCounts n hM t = n (Fin.castLE hM t)`.

**`suffixCounts`** has the exact signature

`{K k M : ℕ} (n : Fin K → Fin k → ℕ) (hM : M ≤ K) : Fin (K-M) → Fin k → ℕ`.

Its value is

`suffixCounts n hM t = n ⟨M+t.val, h_index⟩`,

where `h_index : M+t.val<K` is proved from `hM` and `t.isLt`. Natural subtraction is used in the suffix length. The choice of proof for the bound does not affect the value.

Neither definition takes `N` or `hn`, since it only restricts a count array by column indices. In particular they are defined even for count arrays for which no matrix law exists.

### O.D02: split matrix equivalence

**`splitMatrix`** has the exact signature

`(N : ℕ) {K k M : ℕ} (n : Fin K → Fin k → ℕ) (hM : M ≤ K) :`

`FixedMatrix N n ≃`

`(FixedMatrix N (prefixCounts n hM)) × (FixedMatrix N (suffixCounts n hM))`.

The forward map is definitionally the ordered pair of coordinate restrictions:

- its first component at `t : Fin M` is `ω (Fin.castLE hM t)`;
- its second component at `t : Fin(K-M)` is `ω ⟨M+t.val,h_index⟩`.

The inverse glues these arrays. At a full column index `j : Fin K`, split explicitly on `j.val<M`:

- on that branch use the prefix-array column at `⟨j.val,hj⟩`;
- otherwise use the suffix-array column at `⟨j.val-M,h_suffix⟩`.

The column-subtype transports are justified by the equalities between the displayed index maps and `j`. The suffix branch uses `M+(j.val-M)=j.val`, proved from `M≤j.val`. The bounds and both inverse laws are part of the equivalence's proved constructor. They are not hypotheses or additional named lemmas. Because the forward map is the literal restriction pair, later local glue-coordinate equalities can be obtained by applying the first or second coordinate evaluation to `(splitMatrix N n hM).apply_symm_apply (p,t)`. They need not unfold the inverse's dependent transports.

This equivalence does not use `hn`, `x`, a probability law, a sorting witness, or a feasible-column witness. It simply splits the same dependent product into disjoint coordinate intervals, including empty intervals.

In the remainder of this report, write

`glue(p,t) = (splitMatrix N n hM).symm (p,t)`.

This is only mathematical shorthand for the inverse expression; **no `glue` declaration is proposed**.

## 3. Fixed local abbreviations for the theorem specifications

The following abbreviations eliminate repetition in the displayed statements. They do not add definitions, arguments, fields, or hypotheses to Lean.

- `np = prefixCounts n hM` and `nt = suffixCounts n hM`;
- `Ω = FixedMatrix N n`, `Ωp = FixedMatrix N np`, and `Ωt = FixedMatrix N nt`;
- `hnp t = hn (Fin.castLE hM t)`;
- `hnt t = hn ⟨M+t.val,h_index⟩`;
- `W = matrixLaw n hn`;
- `Wp = matrixLaw np hnp` and `Wt = matrixLaw nt hnt`;
- `X = prefixWord x`;
- `Q = tailCollisionFactor N n M`;
- `Z(ω) = occupancyCount N (sortedRows n ω) X`;
- `Zp(p) = occupancyCount N (rawRows np p) X`;
- `C(ω) = (collisionPairs N (sortedRows n ω) X).card`;
- `E(ω) = edgeCount N (sortedRows n ω) X`.

The typed proof terms `hnp` and `hnt` are obtained by unfolding the restricted count arrays and applying `hn` to the corresponding index. They are not separate assumed count conditions. Existing `fixedMatrixFintype` instances supply the three finite sample-space enumerations; their product uses the trusted product instance. If Lean needs finite-instance equality at a reindexing step, it is resolved by the uniqueness of `Fintype` instances or by using the existing exact instance, never by a new model premise.

## 4. Complete proposed named theorem inventory

There are exactly **seven** new named theorems. Every auxiliary project-level statement planned for this addendum is on this list. Within their proofs, local `have` results may establish coordinate identities, cardinalities, weight identities, indicator equalities, and case arithmetic. Those local results must be proved from the listed data and existing project or trusted mathlib results. No additional named helper or assumed interface is authorized by this inventory.

### O.01 — `matrix_expectation_split`

Exact argument list:

`{N K k M : ℕ} (n : Fin K → Fin k → ℕ)`

`(hn : ∀ j, ∑ a, n j a = N) (hM : M ≤ K)`

`(f : FixedMatrix N n → ℝ)`.

Exact conclusion:

`W.expectation f = Wp.expectation (fun p => Wt.expectation (fun t => f (glue(p,t))))`.

There is no nonnegativity, boundedness, or integrability premise on `f`; every sum is finite.

Preferred proof: use the proved collision-core theorem `matrixLaw_uniform_weight` for `W`, `Wp`, and `Wt`. The finite equivalence `splitMatrix` gives

`card Ω = card Ωp * card Ωt`.

Consequently each full-matrix weight equals the corresponding product of prefix- and tail-matrix weights. Reindex the finite expectation sum through the equivalence, rewrite the product-space sum as an iterated sum, and distribute the weights. These are local consequences, not new weight-field assumptions. This avoids creating a binary probability-law constructor or assuming a conditional law.

### O.02 — `tailCollisionFactor_suffix`

Exact argument list:

`(N : ℕ) {K k M : ℕ} (n : Fin K → Fin k → ℕ) (hM : M ≤ K)`.

Exact conclusion:

`tailCollisionFactor N (suffixCounts n hM) 0 = tailCollisionFactor N n M`.

There is **no `hn` argument**. This is an identity of explicit finite products, valid for arbitrary natural count arrays and all `N`. The index bijection sends `t : Fin(K-M)` to the full-column index of value `M+t.val`; its inverse subtracts `M`. The suffix index finset in the full model is exactly the image. In the case `M=K`, both products are empty and equal one.

### O.03 — `prefix_occupancy_glue`

Exact argument list:

`{N K k M : ℕ} (n : Fin K → Fin k → ℕ) (hM : M ≤ K)`

`(x : Fin M → Fin k)`

`(p : FixedMatrix N (prefixCounts n hM))`

`(t : FixedMatrix N (suffixCounts n hM))`.

Exact conclusion:

`occupancyCount N (rawRows n (glue(p,t))) (prefixWord x)`

`= occupancyCount N (rawRows (prefixCounts n hM) p) (prefixWord x)`.

There is **no `hn` argument**. The two sample objects already have their displayed deterministic column types; this is a samplewise prefix identity. Prove membership equality for each actual row label by the existing `prefixWord_prefix_rawRow_iff` and the split coordinate identities. Values outside `[0,N)` never enter either finite set.

Together with the already proved `sorted_occupancy_eq_raw`, this gives `Z(glue(p,t))=Zp(p)` for every pair `(p,t)`. Thus occupancy depends on the prefix array alone as a deterministic fact.

### O.04 — `increasing_pairs_in_finset_card`

Exact argument list: `(s : Finset ℕ)`.

Exact conclusion:

`((s ×ˢ s).filter (fun p => p.1 < p.2)).card = Nat.choose s.card 2`.

This theorem has no `N`, matrix, prefix, or law parameter. It extends the existing range formula `increasing_pair_card` to a deterministic subset of original row labels. One proof transports through the increasing enumeration of `s` and applies the already proved range formula. Another proves the insertion recurrence and splits explicitly according to which of two distinct natural labels is smaller. Both count each unordered pair once.

### O.05 — `tail_expected_collisionPairs_given_prefix_array`

Exact argument list:

`{N K k M : ℕ} (n : Fin K → Fin k → ℕ)`

`(hn : ∀ j, ∑ a, n j a = N) (hM : M ≤ K)`

`(x : Fin M → Fin k)`

`(p : FixedMatrix N (prefixCounts n hM))`.

Exact conclusion:

`Wt.expectation (fun t => ((collisionPairs N (sortedRows n (glue(p,t))) (prefixWord x)).card : ℝ))`

`= (Nat.choose (occupancyCount N (rawRows (prefixCounts n hM) p) (prefixWord x)) 2 : ℝ)`

`  * tailCollisionFactor N n M`.

The original population `N` remains in every one-column pair factor. There is no replacement of `N` by the prefix occupancy. The fixed original-label set carrying the prefix is

`s = occupied N (rawRows np p) X`.

For a fixed increasing pair in `s`, the two glued full rows agree if and only if their suffix words agree: their prefix words are already both the fixed word `x`. For a pair not wholly in `s`, the full prefix collision event is false. The existing `matrix_pair_prefix_probability`, applied to the suffix matrix with the empty prefix, gives the suffix-equality probability; existing `prefix_factors_empty` and O.02 identify it as `Q`. Existing F12 and O.04 sum this constant over all increasing pairs in `s`. Finally, existing `sorted_collisionPairs_card_eq_raw` transports the collision cardinality through sorting.

O.03's cardinal equality alone is not sufficient for this argument. The following exact **local proved steps inside O.05** preserve the original label identities:

- For every `i : Fin N`, `X <+: rawRow n (glue(p,t)) i ↔ X <+: rawRow np p i`.
- For every `i j : Fin N` whose two prefix-array rows both carry `X`, `rawRow n (glue(p,t)) i = rawRow n (glue(p,t)) j ↔ rawRow nt t i = rawRow nt t j`.
- Consequently, for every such original pair of labels, the full event `rawRow n (glue(p,t)) i = rawRow n (glue(p,t)) j ∧ X <+: rawRow n (glue(p,t)) i` is equivalent to `i.val∈s ∧ j.val∈s ∧ rawRow nt t i = rawRow nt t j`.

Prove these using the literal split restrictions, the equivalence's `apply_symm_apply`, existing C.21–C.22 for coordinatewise prefixes and row equality, and the fact that both prefix-array words have exactly length `M`. For the implication from one prefixed endpoint and equal rows to both endpoints, use frozen F19. These are local proofs of label membership and equality, not inferences from a cardinality identity. No conditional pair law is assumed and no additional named coordinate lemma is proposed.

For `N=0` or `N=1`, first prove the row subset has fewer than two labels, or use the existing empty-collision results, before instantiating a theorem about two distinct labels. All sizes are quantified in the final statement.

### O.06 — `matrix_collisionPairs_occupancy_slice`

Exact argument list:

`{N K k M : ℕ} (n : Fin K → Fin k → ℕ)`

`(hn : ∀ j, ∑ a, n j a = N) (hM : M ≤ K)`

`(x : Fin M → Fin k) (q : ℕ)`.

Exact conclusion, using the abbreviations from section 3:

`W.expectation (fun ω => if Z(ω)=q then (C(ω) : ℝ) else 0)`

`= (Nat.choose q 2 : ℝ) * tailCollisionFactor N n M * W.probability (fun ω => Z(ω)=q)`.

The if-expression is the chosen exact Lean representation of multiplying by the occupancy-event indicator. There is no hypothesis `q≤N` or `0<P(Z=q)`.

Proof: O.01 first integrates the tail for each fixed prefix array. O.03 and sorting invariance make the occupancy indicator constant in that inner expectation. On the true branch O.05 supplies `choose(Zp(p),2)Q`, and `Zp(p)=q` substitutes `q`. On the false branch both integrands vanish. A second use of O.01 for the occupancy indicator identifies the remaining prefix expectation as `P_W(Z=q)`. The finite constant-factor and indicator algebra is proved locally, using the existing law normalization; no new expectation wrapper is required.

### O.07 — `matrix_internal_edges_occupancy_slice`

Exact argument list is identical to O.06, including arbitrary `q : ℕ`.

Exact conclusion:

`W.expectation (fun ω => if Z(ω)=q then (E(ω) : ℝ) else 0)`

`≤ (Nat.choose q 2 : ℝ) * tailCollisionFactor N n M * W.probability (fun ω => Z(ω)=q)`.

The indicator uses the same **sorted** occupancy `Z` as O.06. On its true branch, frozen F21 bounds adjacent internal edges by the number of identical-row collision pairs. On its false branch both sides of the pointwise comparison are zero. Existing expectation monotonicity and O.06 then prove the displayed inequality. It is an inequality for adjacent edges, never an equality with the unordered collision count.

This is stronger than the finite numerical coefficient used at TeX 1520–1523: `choose(q,2)≤q²`. On a positive-probability occupancy slice, division yields the ordinary finite conditional expectation bound. The addendum itself does not introduce a conditional-expectation operator or assert a value on a null slice.

## 5. Dependency graph and proposed modules

Every new file is under `lean/EdgeLocalization/EdgeLocalization/Conditional`. Existing frozen and collision modules remain untouched.

| Module | New declarations | Required proved dependencies |
|---|---|---|
| `Conditional/Model.lean` | `prefixCounts`, `suffixCounts`, `splitMatrix` | Existing `Collision.Model` types; trusted finite-index and equivalence constructions. No new theorem declaration. |
| `Conditional/Split.lean` | O.01 `matrix_expectation_split`; O.02 `tailCollisionFactor_suffix`; O.03 `prefix_occupancy_glue` | `Conditional.Model`; existing `Collision.Matrix` for C.17 and C.21; finite sum/product reindexing. |
| `Conditional/Counts.lean` | O.04 `increasing_pairs_in_finset_card`; O.05 `tail_expected_collisionPairs_given_prefix_array` | `Conditional.Split`; existing C.33, C.31, C.48–49, C.57, F12/F19; O.02–O.04. |
| `Conditional/Estimates.lean` | O.06 `matrix_collisionPairs_occupancy_slice`; O.07 `matrix_internal_edges_occupancy_slice` | `Conditional.Counts`; O.01/O.03/O.05, existing F21 and expectation monotonicity. |

The logical dependencies are:

- O.D01 → O.D02;
- O.D01–O.D02 and existing C.17 → O.01;
- O.D01 → O.02;
- O.D01–O.D02 and existing C.21 → O.03;
- existing finite-order counting → O.04;
- O.02–O.04 and existing matrix pair probabilities/sorting invariance → O.05;
- O.01, O.03, O.05 and existing sorted occupancy invariance → O.06;
- O.06 and the frozen edge-to-collision injection → O.07.

O.05 does not mathematically depend on O.01: the prefix array is already fixed, and the tail law is an existing matrix law. The file import is acyclic and merely makes the shared split definitions and O.02–O.03 available. O.04 is independently provable as soon as its statement is frozen.

Constructor equivalence laws and the weight/cardinality identities used by O.01 are local proofs. No extra `prefixLaw`, `tailLaw`, `glue`, histogram-sum lemma, split-cardinality lemma, or generic Fubini lemma is proposed as a named declaration. The seven displayed propositions are the complete helper/target inventory.

## 6. Explicit case audit

**`N=0`.** Every actual row-index set is empty. All occupancies and collision/edge counts are zero, even though the prefix may request a zero-count digit. The only possible occupancy slice is `q=0`; its pair coefficient is zero. For `q>0` its event and integrand are false/zero. The split equivalence still splits the actual empty columns, and both normalized factor laws exist from `hn`.

**`N=1`.** A prefix occupancy can only be zero or one; both binomial coefficients are zero. There is no distinct label pair, and the existing zero-collision/edge results apply before any two-row probability theorem. Algebraically total pair factors at `N=1` are not cancelled or interpreted as probabilities of nonexistent pairs.

**`M=0`.** The prefix-array space has one element, every row carries the empty word, and `Z=N` deterministically. The tail law is the full-column law under the split equivalence. O.06 reduces to the exact collision mean on the slice `q=N` and to zero on every other slice.

**`M=K`.** The suffix has zero columns and a unique empty-array sample; its collision factor is one. A row carrying the full word `x` equals every other row carrying `x`, so the collision count is exactly `choose(Z,2)`. O.06 is the corresponding exact slice identity; O.07 retains the adjacent-edge inequality.

**`K=0`.** Necessarily `M=0`, both component arrays are empty, every row is the empty word, and `Z=N`. All empty products are one. The full collision count is `choose(N,2)`, while the internal edge count is `N-1` with natural subtraction. The same formulas include `N=0,1`.

**`k=0`.** If at least one column is present, `hn` forces `N=0`. If `K=0`, the column-size condition is vacuous and arbitrary `N` is permitted. The split definition never chooses a default alphabet digit. A vector `x : Fin M → Fin 0` can exist only for `M=0`, which is already handled.

**`q=0,1`.** The occupied subset has no increasing pair; O.06 and O.07 both have zero right side. No assertion that the expected number of adjacent edges equals a pair count is used.

**`q>N`.** Occupancy is the cardinality of a subset of `range N`, so this event is impossible and every slice integrand is zero. The universal statements do not omit these values or impose `q≤N` merely to simplify the proof.

**A null slice with `0≤q≤N`.** It can be impossible because of the prescribed column counts or requested prefix, even when the numerical bound permits it. The formula does not divide by the slice probability; O.01's event-indicator proof still applies and gives zero.

**A zero-count requested prefix digit.** Existing `column_zero_count` makes occupancy identically zero. This is included, without introducing source legality as an additional hypothesis.

**A requested prefix pile of size one.** Occupancy is at most one and there are no collision pairs in that prefix. A singleton occupied block remains possible; the one-row occupancy is not incorrectly set to zero.

**Zero tail factor.** The exact suffix pair probability is zero. O.05–O.07 then have zero right side. No inverse of a tail factor or collision probability is used.

**Repeated words and outcome-dependent sorting.** The already proved samplewise collision-cardinality and occupancy-cardinality equalities apply to each glued matrix separately. The sorting permutation need not be independent, uniformly random, or determined by the prefix array.

**Conditional population.** Fixing a prefix array fixes a subset of original row labels. Its size can be `q`, but the tail columns still sample from the original `N` labels. The denominators remain `N(N−1)` exactly. This contract does not posit a new fixed-count law on `q` labels.

## 7. Formalization boundary

This proposed addendum proves an exact conditional component required by the assigned internal shuffle-graph estimate, using only the actual already constructed finite model. Its final statement is the division-free occupancy-slice inequality O.07, valid for every `q`.

It does not prove a theorem about arbitrary exploration-conditioned matrices, the `U_x` resampling distribution, endpoint localization, the printed `−c_F` spatial gain, stable-profile counting, or asymptotic exponent replacement. The full Lean goal remains larger than this addendum. Every old freeze remains byte-identical; any implementation must follow a new explicit comparison and freeze of these three definitions and seven statements.

## 8. Independent comparison and acceptance

After completing the statement report, I read `conditional_contract_reconstruction.md` and `conditional_contract_assumptions.md` in full. I accept the three definitions and all seven statements above for the proposed separate freeze. There is no remaining mathematical or signature mismatch among the three reports.

- Both reports confirm the exact definition domains and argument order: count restrictions take `n hM`; `splitMatrix` takes explicit `N n hM`; all existing raw/sorted row calls take their own explicit count array; tail factors retain explicit original population `N`.
- O.01 is accepted for every real-valued integrand and follows from existing C.17 plus the split equivalence's cardinality. No conditional-law, integrability, or sign premise is missing.
- O.02, O.03, and O.04 correctly omit `hn`. O.03 is a deterministic identity for actual typed arrays; its conclusion is only a cardinality equality.
- Both reports require the stronger local label-membership and row-equality steps in O.05. Those exact local obligations are recorded in section 4 and follow from the literal forward restrictions, `apply_symm_apply`, and existing C.21–C.22. Nothing in the argument infers a set identity merely from equal cardinalities.
- Both reports verify O.05's `choose(Zp(p),2)` coefficient and unchanged `N(N−1)` sampling denominator. Its collision equality and O.07's adjacent-edge inequality remain distinct.
- O.06 and O.07 have exactly the same unrestricted natural `q` domain and the same sorted occupancy indicator. Null slices, `q>N`, empty prefix/tail, zero piles, and `N=0,1` need no new premise and are all covered in the recorded cases.
- The proposed module dependency order is acyclic. The reconstruction's trusted increasing-enumeration proof supplies O.04 without any additional named helper; all other auxiliary steps can likewise remain local proved steps inside the seven fixed declarations.

No additional definition, named instance, theorem, hypothesis, or source correction is needed for this addendum. The prior freezes and reviews remain untouched. This acceptance does not include arbitrary exploration conditioning or the remaining spatial-density/localization claims.
