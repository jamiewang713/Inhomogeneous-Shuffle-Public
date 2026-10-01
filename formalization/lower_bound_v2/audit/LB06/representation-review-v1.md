# LB06 independent representation review v1

Reviewer scope: exact Lean representation, public target, reusable checked imports,
and implementation interfaces. This review adds no proof implementation and changes
no shared declaration. Reviewed 2026-10-01 against Contracts/v1.

## Readiness and exact export

The receipt `audit/LB00/CONTRACT_READY.md` releases the shared foundation with Lean
4.33.1, mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, and contract-manifest
SHA-256 `4aa7208c17818ae792398054c98ccd25c6c2270c6877572161ab73341398f858`.
The independent command

```text
python3 formalization/lower_bound_v2/scripts/lane.py LB06 --check-ready
```

returned `LB06 CONTRACT_INPUTS_OK`. This is foundation/provenance readiness, not
proof of any LB06 conclusion.

OWNERSHIP.json requires exactly this future theorem:

```lean
RiffleLowerV2.Types.roundedType : RiffleLowerV2.Targets.RoundedTypeTarget
```

The frozen target body is:

```lean
def RoundedTypeTarget : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∀ C : ℝ, 0 ≤ C →
  ∃ Ctype : ℝ, 0 < Ctype ∧ ∀ T xi : ℝ, 0 < T → 0 < xi → xi < 1/(4*(k : ℝ)) →
  ∀ m : ℕ, ∃ Cround : ℝ, 0 < Cround ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
  ∀ N K : ℕ, N0 ≤ N → ∀ (P : BorelPartition k), P.cellCount = m →
  P.IsRegular xi C → ∀ (cuts : Cuts k N K) (hN : 0 < N) (I : Finset (Fin K)),
  (I.card : ℝ) ≤ T*logScale N → ∀ alpha ∈ Icc (2 : ℝ) 4,
  ∃ D : RoundedTypeData P, TypeDataSpec cuts hN P I xi alpha D ∧
    TypeApproximation cuts hN P I alpha
      (Ctype*T*xi*Real.log (1/xi) + Cround*(Real.log (logScale N)+1)/logScale N) D
```

Thus `Ctype` may depend only on k,C. Cround and N0 are chosen before P,N,K,
cuts,I,alpha; their lexical dependencies include k,C,T,xi,m. Cround must be
positive even for m=0. A coarser named formula independent of C is preferable
and matches the source rounding term. N0 cannot depend on a particular
partition beyond its fixed number m of cells. No macroscopic approximation,
LB05 theorem, or full-support hypothesis belongs in the interface.

## Representation verdict

The shared representation is suitable. No mathematical change to the frozen
target or shared definitions is required by this review.

* `WordOn k I := (j : I) → Fin k` counts exactly the chosen coordinates. A
  function on the empty subtype is the unique empty word. This avoids the
  unwanted factor `k^(K-I.card)` that an ambient-word filter would create.
* `RoundedTypeData P` contains only natural counts and a natural bin index.
  `roundedClass` and `selectedClass` are derived finite sets. The data structure
  does not smuggle nonemptiness or approximation into an assumption.
* `retainedTilt` is already normalized by the retained power sum. Prove that sum
  positive before rewriting division or claiming normalization. The definition
  is totalized at zero; totalization supplies no probability-law proof.
* `TypeDataSpec` requires exact cell totals, support, coordinate error at most
  one, positive retained denominators in every cell, both nonemptiness claims,
  the count of occupied floor bins, the exact natural multinomial product,
  global maximality with the smallest-index tie rule, nonnegative exponents,
  exact cardinality, the strict lower/non-strict upper mass interval, and actual
  cutoff for every unbinned word. Every conjunct is an obligation.
* The multinomial expression uses natural division inside each cell's product.
  Before taking real logarithms, prove divisibility/positivity and the real-cast
  quotient identity. Do not rewrite a natural quotient as a real quotient
  without its divisibility condition.
* Natural floor is correct for bins only after proving `0 < massOn cuts x ≤ 1`.
  Without positivity, `Real.log 0 = 0` would give a spurious occupied zero bin.
* The tie rule quantifies over all natural bins, including empty ones. Once the
  selected cardinality is positive, empty bins cannot tie, so choosing the
  smallest maximizing element of the finite occupied-bin set proves the rule.
* `tiltedEntropy` is actual `shannonEntropy (tiltedWeight p alpha)`, not an
  abbreviation for `alpha*tiltedCost-psi`. The entropy identity must be proved,
  including coordinates of probability zero.

Empty chosen set: choose every count zero and bin index zero. The unbinned and
selected classes are singletons, mass is one, J*=H*=0, and empirical sums are
zero. Empty cells inside nonempty chosen sets contribute 0!=1 and zero entropy;
normalization of their retained law still follows from their representative
being a simplex point. Do not divide by a cell size without a separate zero case.

## Particularly useful deterministic rounding interface

There is a simple alternative to sorting remainders. For a law q on `Fin k`, set

```text
s(a) = n * sum_{l : Fin k, l.val < a} q(l),  a = 0,...,k
count(l) = Nat.floor(s(l.val+1)) - Nat.floor(s(l.val)).
```

All subtractions are natural. Prefix monotonicity permits casting them to real
subtraction. Telescoping gives total n because s(0)=0 and s(k)=n. If q(l)=0,
the adjacent prefix sums agree, so count(l)=0. The two floor errors differ by
less than one, proving the required absolute coordinate error. This defines a
deterministic digit-order rounding, with no arbitrary choices and no need to
choose a positive-probability coordinate for the remainder. It has the same
mathematical specifications as the manuscript's deterministic floor/remainder
construction; document the construction choice in the proof provenance.

Suggested local helper interface (proposed, not an existing checked theorem):

```lean
exists_supported_rounding
  (n : ℕ) (q : Fin k → ℝ)
  (hq : ∀ l, 0 ≤ q l) (hsum : ∑ l, q l = 1) :
  ∃ c : Fin k → ℕ,
    (∑ l, c l = n) ∧
    (∀ l, q l = 0 → c l = 0) ∧
    (∀ l, |(c l : ℝ) - (n : ℝ) * q l| ≤ 1)
```

Prefer also exporting the deterministic local definition and its three lemmas,
rather than relying only on existential choice.

## Suggested local proof decomposition

The following are proposed interfaces/obligations, not declarations claimed to
exist. They can all stay inside `RiffleLowerV2/Types/`.

1. For a simplex point r with k≥2 and 0<xi<1/(4k), prove a retained coordinate
   exists, the retained denominator is positive, q is nonnegative and sums to
   one, and q(l)=0 exactly on discarded coordinates. Positivity needs no new
   eventual condition: some coordinate is at least 1/k, which is greater than
   2xi. A coarse denominator lower bound `k^(-4)` follows from that same
   coordinate and alpha∈[2,4]; Jensen is unnecessary for this purpose.
2. Prove a generic function-class theorem for finite types J,A,B and a cell map
   `cell : J → A`. Under `∑ b, c a b = card {j // cell j = a}`, the finite set
   of functions with counts c is nonempty and its cardinality is the product of
   multinomials. Specialize J to the subtype I. Finite-set/subtype count adapters
   then connect it to `wordCellCount` and `cellPositionCount` without replacing
   shared definitions.
3. Prove the zero-safe finite factorial estimate
   `|log(n!) - ((n:ℝ)*log n - n)| ≤ A*(log(n+1)+1)` for every n, for a named
   absolute constant A. Both signs are needed. Combine with the multinomial
   equality to bound log cardinality on both sides.
4. Prove the modulus for `f(t)=t*log t` on [0,n], with f(0)=0:
   `|f(x)-f(y)| ≤ log(n+1)+2` whenever `|x-y|≤1`. Summing coordinates yields
   entropy rounding, including n=0 and short cells. A coarse larger explicit
   constant is harmless.
5. Prove retained-law cost/entropy approximation against an arbitrary actual
   p in the representative cell, uniformly in alpha. Include the zero-safe
   tilted entropy identity and a private coarse bound for full tilted cost;
   a k-dependent coarse bound suffices, so LB05 is unnecessary.
6. Prove a generic finite-bin lemma: a nonempty finite C of objects carrying
   masses in (0,1] and with cost at most B has a smallest maximal bin, positive
   selected cardinality, occupied-bin count at most B+2, and
   `log C.card - log (B+2) ≤ log selected.card ≤ log C.card`.
7. With N≥2, prove the exact exponential identities from definitions J*,H*.
   Use a positive selected cardinality before exponentiating log(cardinality),
   and positive logScale before cancelling it. The floor interval gives the
   strict lower mass bound in the frozen target.
8. Aggregate explicit errors. For L=log N≥1 and `I.card≤T*L`, use
   `log(I.card+1)≤log(T+1)+log L` and
   `log(2+T*L*log(1/xi))≤log(2+T*log(1/xi))+log L`.
   These produce a named Cround depending only on the permitted fixed data.
   Separately prove `(log(log N)+1)/log N → 0`. Never describe the fixed
   `Ctype*T*xi*log(1/xi)` budget as tending to zero in N.

The combinatorial theorem admits two independent implementation strategies:
recursive removal of a digit and selection of its positions (binomial
recurrence), or a finite permutation orbit/stabilizer count. The first avoids
group-action representation overhead; the second has substantial reusable
mathlib infrastructure. Neither a mass-sum upper bound nor a Gibbs inequality
proves the required lower count.

## Read-only source reuse and missing compiled imports

Already registered canonical project imports are only RiffleShuffle.Basic,
Graphs, Matrices, Profiles, Words and RiffleTimeProfile.Ambient, Base,
FixedCountModel. Their checked declarations, and the shared package's routine
adapters, may be imported through the frozen foundation.

Useful already checked Base interfaces include `prob_nonneg`, `prob_le_one`,
`sum_prob`, `exists_prob_pos`, `inv_card_le_pileMax`, `Cuts.profile_prob`,
`logScale_pos`, and the four `BorelPartition.IsRegular` fields. In particular
`good_actual_gt`, `good_digitCost_error`, and `exceptional_actual_le` match the
retained/omitted coordinate transfer needed here. The log-ratio bound follows
by rewriting digitCost as minus log on positive coordinates.

Read-only candidate sources:

| Source | Useful material | Limitation |
| --- | --- | --- |
| `RiffleTimeProfile/Analysis.lean` | `powerSum_pos`, `powerSum_le_one`, `finite_gibbs`, `exists_regular_partition` | Not currently registered/rebuilt in this package |
| `RiffleProfiles/Entropy.lean` | zero-safe finite Gibbs and weighted entropy | Old package; requires compatible checked port/import; supplies no lower count |
| `RiffleProfiles/Estimates.lean` | finite sum error, cell regrouping and replacement | Old package; does not prove analytic retained-law approximation |
| `FirstMoment/Entropy.lean` | word-mass normalization and `type_class_card_le_exp_entropy` | Only an upper bound; domain is `Fin K`, so arbitrary-I adaptation is required |
| `RiffleLower/Profiles.lean` | digit-count sums, exact product regrouping, legal-word log mass | No nonempty class or multinomial count theorem |

The exact partition theorem read is:

```lean
TimeProfile.exists_regular_partition {k : ℕ} (_hk : 2 ≤ k) {chi : ℝ}
  (hchi : 0 < chi) (_hchiK : chi < 1 / (k : ℝ)) :
  ∃ P : BorelPartition k, P.IsRegular chi 1
```

Its constant is exactly 1, independent of chi. The LB06 cutoff implies its
cutoff. This may be used to construct an internal partition; it need not equal
the partition in a macro AlmostLike assumption.

Pinned mathlib source candidates verified by inspection:

* `Mathlib.Algebra.Order.Floor.Semiring`: `Nat.floor_le`,
  `Nat.lt_floor_add_one`, `Nat.floor_natCast`, `Nat.floor_le_floor`.
  The corresponding compiled module exists in the current foundation view.
* `Mathlib.Data.Nat.Choose.Multinomial`: `Nat.multinomial`,
  `Nat.multinomial_spec`, `Nat.multinomial_insert`, and the multinomial theorem.
  Its compiled module is currently absent from the foundation view.
* `Mathlib.Analysis.SpecialFunctions.Stirling`: `Stirling.log_stirlingSeq_formula`,
  `Stirling.log_stirlingSeq'_antitone`, and
  `Stirling.log_stirlingSeq_bounded_by_constant` provide finite upper/lower
  logarithmic-factorial estimates after algebra, with n=0 separate. Its compiled
  module is currently absent from the foundation view. Verify the namespace in
  the actual import when implementing; this review does not claim a successful
  elaboration of these proposed uses.
* `Mathlib.GroupTheory.Perm.DomMulAct`: `DomMulAct.stabilizer_card` counts the
  product of factorials of fibers for the orbit/stabilizer alternative.

The source names and argument structures above were read directly; no old
olean is authorized by their presence. `scripts/lane.py` refuses missing
upstream compiled modules and rebuilds only modules under
`RiffleLowerV2.Types.`. LB06 must ask LB00 for a serialized additive dependency
registration/build (especially Analysis, Multinomial and Stirling), or port
needed project proofs into its own namespace with source hashes and checked
adapters. Do not modify the v1 source manifest or mix old caches.

## Proposed coordinator request

No amendment to TypeDataSpec, TypeApproximation, RoundedTypeTarget, or
RoundedTypeData is requested. Request only additive checked imports for the
analytic/finite-combinatorial modules selected by the implementation, with a
new dependency receipt retaining every v1 file unchanged. If a downstream lane
needs a shared name for a local helper, first propose that additive interface in
`audit/LB06/` rather than editing Shared/.

Review verdict: the target is implementable in its current representation; the
major work is new finite counting and analytic estimates, and the immediate
tooling obstacle is missing registered compiled dependencies. No old upper
type-class estimate can discharge the lower counting obligation.
