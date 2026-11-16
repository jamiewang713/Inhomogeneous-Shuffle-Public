# X1 source-premise recheck and concrete-realization review

Reviewer: independent hypothesis-audit agent. This is a read-only mathematical and statement-fidelity review before implementation of R1–R4. The only mathematical sources consulted are the permitted TeX manuscript and the two permitted PDFs. No proposed repair of an ambient theorem is approved here.

## Decision

The first-column obstruction survives the manuscript's crossing, admissibility, retained-pair, fluctuation-regularity, good-column, and profile restrictions. The singleton-middle experiment also survives restriction to stable prefixes. The problem is exact exhaustion of a positive residual population, not an empty population, small conditional mean, null event, or missing side mass.

Approve **each of R1, R2, R3, and R4** in `X1_REALIZATION_DRAFT.md`, including the final Boolean, literal-intersection, and finite-tower additions. They concretely realize frozen X1 using already frozen D6 and F3–F4. They do not change any v1 assumption or conclusion. In particular, arbitrary positive conditioning is asserted to preserve a deterministic **count**, not the uniformity of an assignment.

## 1. The exact finite experiment

Let `L≥1`, let `M` be either `L` or `1`, and put `N=2L+M`. Use three digits and at least two independent legal fixed-count columns, with first histogram `(L,M,L)`. Tail histograms do not affect any assertion below; the draft's choice to repeat the first histogram is one valid D6 realization. Let the ambient prefix be the root `w=∅`, and set `x=y=z=(1)`.

For **every** legal matrix:

* exactly `L` rows have first digit `0`, exactly `M` have first digit `1`, and exactly `L` have first digit `2`;
* the number of rows preceding the first-prefix middle block is `L`, and the cumulative count through that block is `L+M`;
* after revealing the rows with first digit `1`, the remaining population has `2L` labels, of which `L` are marked by digit `0`;
* in the source's equal-index reveal at `a=b=1`, the common-prefix condition before the sampled column is empty, so the sample is **all** `2L` remaining labels;
* the actual marked/sample intersection count is `L`.

Consequently the named residual parameters are `population=2L`, `marked=L`, `draws=2L`. Their mean is `L`, their variance is zero, their marked complement is `1/2`, and their sample complement is zero. Both marked and unmarked populations are positive. The residual population is at least two, so neither division by `N−1` at a one-point population nor the zero-population convention explains the failure.

The draft correctly distinguishes zero-based cumulative counts from a manuscript endpoint convention. If positions start at one, adding the same fixed `1` to the two cumulative endpoints leaves all deterministic-atom and variance conclusions unchanged. The draft does not silently equate different random variables.

## 2. Crossing, admissibility, and retention

Source: `def:boundary-pairs-stable-blocks`, TeX lines 522–697; root ambient definition at lines 491–518.

Choose the source's `k=3` and `0<χ<1/3`. Since `M≤L`, both side-pile fractions satisfy `L/(2L+M)≥1/3>χ`. Thus the first-column large-pile boundaries are exactly `i_left=0` and `i_right=2`, whether or not the middle pile also exceeds `χN`.

The one-letter prefix `(1)` is legal because `M>0`. At its first digit, `1>0` and `1<2`, so it crosses both boundaries. The conditions on earlier digits are vacuous. Both admissibility counts are exactly zero: its only digit is neither `<i_left` nor `>i_right`. In particular, the singleton middle digit is not counted by the admissibility truncation as a pre-boundary bad digit.

The set `A_{y,z}` is nonempty and contains `x` and its legal continuations. The source allows `y=z`; it only requires compatible prefixes. Since both lengths are `1<K`, the pair is nonterminal. The source imposes no positive macroscopic lower bound on crossing time, so the scaled time `1/log N→0` is permitted.

For every legal continuation `ξ`, the left piece at index `1` consists of all rows with first digit `0`, and the right piece at index `1` consists of all rows with first digit `2`. Thus their sizes and expectations are exactly `L`. The fluctuation maximum includes the first column because its index range is `M_w<i≤M_vee`, here `0<i≤1`. Therefore

`c_F(ξ;y,z) = (1/2) log_N L`.

This is finite for every `L≥1`, including `L=1`, so the pair is retained.

## 3. Fluctuation regularity and stability

Source: the same definition, particularly its continuation-uniform fluctuation-regularity condition and its separate singleton stable-family branch.

At the root, `c_L(x)=log_N M`. Every later legal pile fraction is at most one, so for every continuation `ξ`,

`c_L(ξ)≤log_N M≤log_N L=2c_F(ξ;y,z)`.

The pair is therefore fluctuation-regular with **zero error**, uniformly over all continuations. No favorable interpretation of an `o(1)` term is needed.

For `M=L`, the prefix `x=(1)` generally is not stable when `δ` is small: `c_L(x)−c_F=(1/2)log_N L→1/2`. This does not defeat the example against the stated ambient transfer and ambient concentration/anti-concentration lemmas, which quantify over `ξ∈A_{y,z}` and `x∈A_{y,z}`, respectively, not just the stable subfamily.

For `M=1`, `c_L(x)=0`, so `c_L(x)−c_F≤0<δ` for every source `δ>0`. The definition therefore makes the stable family exactly `{x}`. This is the immediate stable-singleton branch, not the terminal fallback. Restricting the disputed claim to stable blocks would still leave this example.

## 4. Profile truncation does not discard the singleton

Sources: `def:space-time-digit-profile`, lines 700–747, and `lem:ub-bad-profile-reduction`, lines 1040–1118.

For the singleton case, `x=y∨z`, so `s=u=1/log N`. The profile counts only times satisfying `s log N<j≤u log N`; this set is empty. Therefore every profile count, the exceptional set, and its normalized size `R_x` are zero. The `R_x>α_χ` truncation does not apply. This conclusion is stronger than saying that there is only one exceptional digit: the first crossing digit is outside the profile's counting interval altogether.

Neither admissibility nor the stated bad-profile reduction contains a rule discarding a stable block merely because its size is one. Such a block has no internal graph edge, so a later edge-count estimate might choose to handle it separately, but that would not validate the endpoint anti-concentration lemma as presently quantified.

## 5. Good columns and macroscopic assumptions

Source: `def:good-columns`, lines 306–309. A good column needs **at least two** coordinates of size at least `χ`, not all three. Each first histogram above is good because its two side fractions are at least `1/3`. Choosing good tail columns makes every column good and satisfies a local good-shuffle condition, for example with `γ=1/2` for sufficiently large `N` and fixed positive macroscopic interval length `ρ`. Integer-grid endpoint errors are bounded independently of `N`.

The finite realization in R1–R4 does not assume any asymptotic profile. It is unnecessary to introduce one into those Lean statements. If one additionally asks for a source example satisfying almost-time-profile assumptions, there is no inherent incompatibility:

* Repeated balanced histograms have the exact constant uniform three-pile profile.
* Repeated singleton-middle histograms converge to `(1/2,0,1/2)`. Whether a specified arbitrary Borel partition records this convergence as a fixed cell is partition-dependent, so it should not be claimed for every preselected partition without checking its cells.
* A partition-independent way to avoid that issue is to use a singleton first histogram and balanced tail histograms. Restrict to `L=3n+1`, so `N=2L+1` is divisible by three. Use the constant profile concentrated at `(1/3,1/3,1/3)`. The exceptional first column changes any cell count by at most one; grid rounding contributes another bounded error. These errors divided by `log N` are absorbed, for large `N`, by the fixed positive `φ|I|+1/log N` tolerance in `def:almost-time-profile-like-cuts` (lines 250–264). There are only finitely many positive-length grid intervals in that condition. All columns are good. The first-column obstruction is identical for this tail choice.

The numerical first-moment margin is not an explicit premise of either disputed ambient lemma. Even if one imports it from the later application, the balanced constant tail can satisfy it by choosing `T` large. With `a=log 3`, the root profile has `β(s)=1−as` and `B_θ(s,u)=(θ−1)a(u−s)`. Choosing `θ=3` in the infima of `def:numerical-first-moment-margin` (lines 750–792) gives

`N₁≤3−as−2aT≤3−2aT`,

`N₂≤1+as−2aT≤1−aT`,

`N₃=β(T)=1−aT`.

Thus `aT≥2` gives a uniform negative margin, for instance `η≤1`. This calculation is a source-premise compatibility check, not a new Lean target or a proof of the entire upper-bound theorem.

## 6. Exact failure of the two ambient implications

Sources: `lem:ub-ambient-conditioning-transfer`, lines 1155–1200, and `lem:ub-ambient-concentration-anti-concentration`, lines 1203–1434, especially the `a=b` construction.

The maximizing indices are forced to be `a=b=1`. In the root ambient population, its histogram equals the deterministic original histogram, so the separate unresolved question of an unrevealed **ambient** histogram cannot save this example. The source reveal includes the middle-row set and all other columns. It contains the block's internal information, because `x` has length one and all tail strings are revealed. Its `d₂` equals `2L` on every outcome.

The claimed sample complementary fraction is therefore

`1−d₂/(N−n₁^(1)) = 1−2L/(2L) = 0`.

The proposed lower bound `N^{−O(δ)−o(1)}` is strictly positive for every finite exponent and `N>1`. Consequently no choice of a high-probability good event can make that complementary-fraction claim true: it fails pointwise, on every positive reveal atom. This refutation does not rely on selecting implicit constants in asymptotic notation.

As `L→∞`, in both experiments `c_F→1/2` and the relevant side means are `L` of order `N`. For fixed sufficiently small `δ`, this lies in the proof's explicit high-fluctuation branch `c_F≥δ−1/sqrt(log N)` and in the large-mean range. A small-mean branch is therefore unavailable as an explanation.

The endpoint point masses are deterministic under every positive conditioning event. If `S` is any selected good event and `Z` is a finite reveal, then on each positive atom,

`P(left=L and S | Z=z) = P(S | Z=z)`

and likewise for the right endpoint at `L+M`. Thus if the sum of the two point masses is bounded above by `b` on every positive atom, finite total probability yields `2P(S)≤b`. There is **no** assertion that a high unconditioned probability forces a high probability on each conditioning atom. Instead the tower identity itself precludes a uniform decaying bound when `P(S)→1`.

Under the source's intended `O(δ)` convention, choose `δ` small after the earlier fixed parameters so that its fixed coefficient times `δ` is less than the positive limiting fluctuation exponent. Then the claimed endpoint bound tends to zero and contradicts this identity. The stricter pointwise zero-complement contradiction already avoids any need to formalize that convention.

## 7. Why the older fixed-column proof avoids this example

The permitted `2510.22783v1.pdf`, Lemma 4.5 proof, pp. 20–22, explicitly chooses fluctuation indices `u,v≥2`, retains the full deck of size `N`, and uses the first-column prefix size `N'=n_{x[1]}^(1)≤(1−χ)N`. On p. 21 the inequality `a₂+|R₁|≤N'` supplies a genuine unsampled reserve. In the equal-index case on p. 22, the estimate for `d₂` retains the factor `N'/N≤1−χ`. That factor is absent when the new manuscript chooses the first column itself and samples all remaining labels.

The discussion on p. 23 explicitly distinguishes deterministic first-digit locations from the randomness that begins in later digits. Hence the counterexample identifies a protection in the old proof that the new ambient formulation does not retain; it does not refute the old proof's quantified statement.

The permitted `2103.05068v3.pdf`, Lemma 5.6, p. 33, concerns a different multinomial exploration encoding. It explicitly assumes an exploration boundary leaving a positive fraction of the underlying mass unoccupied and explains why an almost-exhausted exploration fails. It cannot supply a missing reserve for the present fixed-column first-digit construction.

## 8. Boundary and freeze-scope checklist

* `L=0` is excluded by the already frozen `L≥1`; it is not silently discarded during proof. The selected middle sizes are positive, so `x=(1)` is legal. `N≥3` makes all base-`N` logarithms meaningful in the source interpretation.
* The matrix has at least two columns, exactly as frozen X1 requires. A one-column experiment would make this pair terminal and is not the proposed source witness.
* `L=1` still gives the finite exhaustion and deterministic count statements. It need not give a large-fluctuation asymptotic contradiction by itself; that contradiction uses the sequence `L→∞`.
* Every conditional probability-law conclusion uses an explicitly positive event or atom. No assertion is made for a null conditioning fibre.
* Counts are constant on the entire legal matrix space, so arbitrary positive conditioning preserves their law. Arbitrary conditioning does **not** generally preserve residual assignment uniformity, and R2/R4 correctly make no such claim.
* R1 identifies the actual sets and count, not merely a numerically equivalent unrelated random variable. The Boolean choice exports precisely the balanced and singleton experiments in frozen X1.
* R3's tower consequence follows from F4 and has no new source hypothesis: its numerical bound is the premise of an implication explaining why a proposed point-mass estimate cannot hold.
* The concrete finite realization, positive-event formulas, and finite tower consequence are within X1+D6+F3/F4. A separately reviewed implementation record can be frozen without editing the v1 contract or its hash.
* Formalizing the manuscript's boundary/stability predicates and its unspecified `O(δ)`, `o(1)`, or exploration sigma-field as new Lean targets would require another explicit review and freeze. R1–R4 do not claim to do that. Likewise, adding a reserve hypothesis or altering the source fluctuation maximum would be a theorem replacement, not completion of v1.
* The finding is a counterexample to the listed intermediate ambient implications. It is not a proof that the final mixing upper bound is false, nor a claim that all exploration geometry has now been formalized.

