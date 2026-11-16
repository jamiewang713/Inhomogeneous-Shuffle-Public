# LB-02 independent missing-hypotheses and counterexample review, v1

Date: 2026-10-01. Scope: the LB-02 prompt, the three assigned manuscript
labels, frozen target statements, and their concrete finite probability
representations. This is a mathematical pre-proof review, not a Lean proof
receipt. Only this report was written by this reviewer.

## Verdict

No false frozen LB-02 target or missing mathematical hypothesis was found.
The stated constants survive all boundary cases below. No weakening of the
frozen targets is needed or approved. The principal implementation risks are
omitting a concrete law bridge, using the original rather than residual mean,
excluding degenerate alphabets or empty prefixes without authorization, and
placing an eventual threshold after a variable over which uniformity is
required.

The LB-00 receipt supplies definitions and target propositions, not proofs of
these targets. In particular, a theorem assuming `Targets.SuccessiveThinning`
or `Targets.PrefixTails` does not discharge that target. LB-02's probability
bound alone does not prove the permutation/run/TV conclusion assigned to
LB-10.

## Inspected state

- Manuscript: `time_inhomogeneous_riffle_shuffle_unified_article.tex`,
  `lem:successive-thinning-tail` (line 2996),
  `cor:iterated-hypergeom` (line 3085), and
  `prop:largest-prefix` (line 3111), including their proofs and the prefix
  definitions immediately preceding them.
- Frozen `Contracts/v1/ModelThinning.lean`, the
  `HypergeometricTransform` target in `AdditionalFinite.lean`, and the
  `MaximalMeanIdentity` target in `AssemblyInputs.lean`.
- `RiffleLowerV2/Shared/Model.lean`, `Statistics.lean`, and the existing empty
  prefix adapters; the underlying `TimeProfile.Cuts`, `ColumnAssignments`,
  `fixedCountPMF`, and `sampleRow` definitions.
- Existing `lean/Shuffle/HypergeometricConcentration.lean` and
  `ResidualSampling.lean`, read as possible mathematical/API inputs rather
  than as automatically compatible imports.
- `audit/LB00/CONTRACT_READY.md` and `.json` and LB-02's ownership entry.

The live manuscript hash is
`672f414c9ccd6229c7f496c80cba6cc989c5fd07d93b75e66083456ee6242b1d`,
matching the prompt and LB-00 receipt. Other inspected live hashes are:

| File | SHA-256 |
| --- | --- |
| `Contracts/v1/ModelThinning.lean` | `bdb0c4c3af301658c9798d191b3dfef1ac34d9df02fb988b1c10214d6b039288` |
| `Contracts/v1/AdditionalFinite.lean` | `b94a1cb35d7204e4e6f0c8dbb277ebc471ec16307a38d2351ef290de6da20869` |
| `RiffleLowerV2/Shared/Model.lean` | `cceadf1b4a5be2f412fe15a9b52b7b7f3c67bfa6d19270955f7c338f01e90930` |
| `RiffleLowerV2/Shared/Statistics.lean` | `dd57ff2f4bbac3e26176809ee15081b58510b041e6dee418f65d31d4fc26fb69` |

These identify the reviewed state; they do not replace or regenerate a frozen
manifest.

## Domain and edge-case ledger

| Case | Exact conclusion and required treatment |
| --- | --- |
| `M > 0` | Retain the explicit frozen domain. It justifies division by `M`, `0 <= q_j <= 1`, and the probability interpretation. Lean's totalized division at zero must not be used to claim the specified positive-population theorem has been proved by a different empty-population convention. |
| `x = 0`, `m = 0`, or `m = M` | One-step transform is respectively `1`, `1`, or `s^x`; all are equalities in the first comparison. No strictly positive pile-size premise is allowed. |
| `x = M` | The intersection count is the deterministic `m`; the comparison is `s^m <= (1-m/M+(m/M)s)^M`, valid for every positive `s`. |
| Empty column sequence | The empty universal condition in `thinningCount` selects all labels, so `X=M`, `Q=1`, and `mu=M`. The transform comparison is equality in its first part. The second part is `s^M <= exp(M(s-1))`. |
| Some `q_j = 0` | `X=0`, `Q=mu=0`. Transform and Poisson comparison both equal `1`. Bernstein tails vanish for `t>0`; the half-mean bound is exactly `1 <= 1`; the `<2` bound is `1 <= 2`. |
| Some `q_j = 1` | That column does not alter the intersection or backward parameter. It must be allowed without a limit argument. |
| `s = 1` | Both transform comparisons equal `1`; strict auxiliary inequalities must not accidentally exclude it. |
| `mu = 0` | No division by `mu` is permitted in the common tail proof. The chosen `h=t/(2(mu+t))` is valid because `t>0`, even when `mu=0`. |
| `k = 0`, `N > 0` | A `Cuts 0 N K` forces `K=0`: an existing column would have total count `0=N`. Thus the only nonvacuous case has the unique empty prefix and `k^K=0^0=1`. A generic counting bound claiming `sum_{r<=K}0^r <= (K+1)0^K` for arbitrary positive `K` would be false; split this case using `Cuts.sum_count`. |
| `k = 1` | Every column is deterministic. There is one prefix at each length, its count and mean are both `N`, and the all-prefix event has probability one. The frozen finite targets include this case. |
| `K = 0` | There is exactly one prefix, the empty prefix, for every `k`, including `k=0`. The count is `N` and its mass is `1`. |
| Zero-mass prefix | A zero factor means its selected pile is empty, hence the count is identically zero under the actual matrix law. It remains inside the simultaneous quantifier. |
| Every prefix length | `Prefix k K` includes lengths `0` through `K`; proving a result only for full words or positive lengths does not satisfy the target. |

## All-positive transforms and constants

The all-positive-`s` one-step comparison is correct. The old public
`Shuffle.HypergeomParams.expect_pow_le` explicitly requires `s <= 1`; it cannot
be cited for `s>1`. Its `expect_one_add_pow_le` and `expect_exp_le` helpers are
private. An additive extension or provenance-documented port must really prove
the missing range. The manuscript's positive symmetric-mean averaging proof
does cover it, including convergence: for a list of length `M>=1`, averaging
largest and smallest entries reduces the squared deviation by half the squared
range, at least `V/(2M)`.

For each independent uniform column subset, the next count conditional on the
preceding subsets is exactly `Hyp(M,X_previous,m_j)`. Backward parameters obey
`z_previous = 1-q_j+q_j*z_next`; positivity holds even at `q_j=0,1`.
The affine recursion yields `z_0=1-Q+Q*s`. No row independence is asserted or
needed. The exponential comparison follows from `1+v<=exp(v)` with positive
base `1-Q+Q*s`, then multiplication of the exponent by `M`.

The exact constants in the frozen tails check as follows:

1. For `0<=h<=1`, the two remainders
   `exp(h)-1-h` and `exp(-h)-1+h` are at most `h^2`. With
   `h=t/(2(mu+t))`, one has `0<h<=1/2` and
   `-h*t+mu*h^2 = -t^2*(mu+2t)/(4*(mu+t)^2)
   <= -t^2/(4*(mu+t))`. A union of the two non-strict tails gives the factor
   `2`. Nothing requires positive `mu`.
2. At `s=1/2`, the event `X<=mu/2` implies
   `s^X >= exp(-mu*log(2)/2)`. Markov gives
   `exp(-mu/2+mu*log(2)/2)=exp(-chernoffConstant*mu)`, where
   `chernoffConstant=(1-log(2))/2>0`.
3. Since `X` is natural, `X<2` implies `X<=1`, hence `(1/2)^X>=1/2`.
   Markov gives exactly `2*exp(-mu/2)`.
4. Set `A=N^epsilon`, `u=sqrt(mu)`, `t=A(u+1)`. In the frozen finite domain
   `N>=2`, `epsilon>0`, one has `A>=1`. The required inequality is
   `2*A*(u+1)^2 >= u^2+A*(u+1)`; the difference is
   `(2*A-1)*u^2+3*A*u+A>=0`. Consequently
   `t^2/(4*(mu+t))>=A/8`. Strict failure of the desired `<=t` bound is a
   subset of the `>=t` tail, so the event convention is safe.

## Residual law and necessary hypotheses

The frozen `ResidualLaw` is correctly formulated. Positive probability gives a
matrix realizing every prescribed symbol. Injectivity of `r.row` then implies
`usedCount r j a <= cuts.count j a` and
`sum_a usedCount r j a=b`. Thus each natural subtraction is genuine subtraction,
the residual counts sum to `N-b`, and `b<N` supplies a positive residual
population.

For a fixed injective complement enumeration `e`, deleting prescribed rows and
reading the others through `e` is a bijection from compatible original matrices
to residual matrices. Uniform finite point masses therefore give the frozen
conditional law, and the residual matrix sample space is again a product of
column spaces. The same argument works for **every** allowed enumeration,
including permutations of it. It cannot choose an enumeration depending on the
sample. The explicit injectivity of `e` is sufficient; given complement coverage
and the matching finite cardinalities it is also derivable, so it is not an
independently necessary extra hypothesis.

Conditional prefix count must mean the count among the remaining rows. In
original notation it is
`prefixCount w - #{q : the prescribed word r.word q has prefix w}`,
with the subtraction justified on the conditioning event. Its mean is exactly

`(N-b) * product_{j < length(w)}
  ((cuts.count j w_j-usedCount r j w_j)/(N-b))`.

The residual PMF equality is not by itself the requested exported conditional
tail specialization: the implementation must transfer the concrete statistic
and substitute these parameters. Constants can be uniform over all admissible
prescriptions because this law is exact, even when the conditioning probability
is very small. An additional claim of convergence as the *original* `N` tends
to infinity, uniformly over arbitrary `b<N`, would need `N-b` to tend to infinity;
the frozen `PrefixFailureUniform` makes no such unsupported residual claim.

Concrete counterexamples to plausible but false replacements:

- **Omit row injectivity:** take `N=3`, `b=2`, one binary column of counts
  `(1,2)`, prescribe digit `0` twice on the same row. The event has probability
  `1/3`, yet the proposed residual counts are `(1-2,2-0)=(0,2)` in natural
  subtraction and have sum `2`, not `N-b=1`. The existential residual `Cuts`
  itself fails.
- **Omit positive probability:** take `N=2`, `b=1`, column counts `(0,2)`,
  and prescribe digit `0`. The event is impossible. The prescribed subtraction
  cannot produce counts summing to `1`, and totalized conditional division does
  not repair the statement.
- **Omit complement coverage for `e`:** take `N=2`, `b=1`, counts `(1,1)`,
  prescribe row `0` to digit `0`, and let `e` enumerate row `0` again. Conditional
  observed digit is `0`, whereas the residual column has only digit `1`.
- **Keep the original mean for the residual count:** take `N=4`, `b=2`, one
  column with counts `(2,2)`, and prescribe both selected rows to digit `0`.
  The remaining digit-`0` count is `0`, so its half-original-mean lower-tail
  probability is `1`, greater than `exp(-2*chernoffConstant)`. Its residual
  mean is `0`, for which the correct bound is `1`.
- **Apply the residual mean to the full count:** in the same example the full
  digit-`0` count remains `2`. At `s=2`, its transform is `4`, exceeding the
  residual-mean exponential bound `1`.

## Simultaneous concentration and uniform quantifiers

For `k>=1`, the number of prefixes is `sum_{r=0}^K k^r`, bounded by
`(K+1)k^K`. The `k=0` case is handled separately as above. Summing the individual
failure bounds gives exactly

`prefixFailure N k K epsilon =
  2*(K+1)*k^K*exp(-N^epsilon/8)`.

No ancestor-family or positive-prefix-mass condition belongs in the conclusion.
The bound is uniform in the deterministic `cuts` because its right-hand side
contains no cut data.

For fixed `k>=2`, `T>0`, `epsilon>0`, and `delta>0`, the frozen quantifier order is

`exists N0, forall N>=N0, forall K,
  K<=T*log(N) -> prefixFailure N k K epsilon<=delta`.

In particular, `N0` may depend on `k,T,epsilon,delta`, and may be enlarged to be
at least `2`; it cannot depend on `K`, cut counts, or the selected prefix. For
`N>=2` and `K<=T log N`,

`prefixFailure <= 2*(T*log(N)+1)*N^(T*log(k))*exp(-N^epsilon/8)`.

The logarithm of this upper bound tends to minus infinity since `N^epsilon`
dominates `log(N)` and `log(log(N))`. This is the required explicit polynomial
union cost followed by a uniform threshold. A pointwise limit for each fixed
`K` is insufficient. No uniformity in unbounded `k` is claimed: for example,
with `K=1` and `k_N=ceil(exp(N^epsilon))`, the displayed error function grows
instead of vanishing, even though a one-column prefix count is deterministic.

## Other falsification checks and largest-word scope

- Column independence is essential: with `M=2`, two perfectly identical random
  singleton subsets give `X=1`, `Q=1/4`; at `s=4`, the transform is `4`, greater
  than `(1+3/4)^2=49/16`. Uniform marginals alone do not suffice.
- The size bounds are essential for the concrete permutation representation:
  with `M=1`, `m=2`, `x=1`, `s=1/2`, the clipped permutation condition gives
  transform `1/2`, but the proposed comparison base is `0`.
- Positivity of `s` cannot be dropped indiscriminately: `M=3`, `m=2`, `x=3`,
  `s=-10` yields actual transform `100` but proposed right side `(-19/3)^3<0`.
- The word must be fixed before sampling for the single-word tails. With
  `N=k=K=2` and both column counts `(1,1)`, select the lexicographically first
  absent full word after observing the matrix. It always has count `0` but
  nominal mean `1/2`; the claimed fixed-word half-mean tail would say
  `1<=exp(-chernoffConstant/2)`, which is false. The simultaneous event remains
  valid for all words because its union bound pays for this selection.
- The canonical maximal word is determined from the cuts, including a
  deterministic tie rule. Once its mean is identified, for any `m<=mu_*/2`,
  `{wordCount<m}` is contained in `{wordCount<=mu_*/2}`. This gives the required
  single-word tail with the exact `chernoffConstant`. The existence/mean
  identity and any `N^beta` adapter are separate proof obligations, not
  consequences of the tail bound alone. The increasing-run event and physical
  law bridge remain LB-10/LB-01 obligations.

## Finite diagnostic checks performed

A temporary in-memory Python computation enumerated exact rational
hypergeometric transition laws for every `M=1,...,8`, every column sequence of
length `0,...,3`, and every permissible size at each column. It checked mass and
mean exactly, and checked **14,160** rational transform inequalities at
`s=1/10,1/2,1,3/2,2,10`. No counterexample occurred. It also checked the two
displayed lower tails and **22,075** Bernstein inequalities numerically at all
support-distance thresholds and additional positive thresholds. These numerical
checks are diagnostics, not proofs or substitutes for Lean checking.

An independent exact finite enumeration checked **384** conditional residual
laws with `N=4,k=2,K=2,b=2` and column counts `(2,2)`: all injective prescribed
row lists, every positive-probability prescribed word list, and every ordering
of the unused labels. Every conditional atom agreed exactly with the uniform
residual model. No source or cache files were created by these diagnostics.

Final review disposition: the exact frozen statements are approved for proof
development. Mathematical proof construction, concrete adapters, conditional
specializations, lane compilation, exported declaration checks, and axiom
closure remain implementation obligations; this review does not mark them
complete.
