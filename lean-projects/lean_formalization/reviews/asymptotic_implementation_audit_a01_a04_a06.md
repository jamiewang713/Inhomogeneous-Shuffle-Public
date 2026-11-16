# Independent implementation audit: A01–A04 and A06

Approved. I found no mathematical defect, changed theorem domain, added
hypothesis, or missing factor in these implementations. This audit compares
the completed modules with `FROZEN_ASYMPTOTIC_CONTRACT.md` and the frozen
`reviews/asymptotic_adversarial.md`; it does not audit A05.

## Final reviewed files

The implementing agent confirmed that all three modules compile under the
pinned Lean 4.19.0 runtime with warnings treated as errors. After that
confirmation, I independently imported `MatrixLimits` and queried the axioms
of all ten public theorems in the reviewed modules. The read-only inspection
completed successfully with warnings treated as errors. Every declaration
depends only on `[propext, Classical.choice, Quot.sound]`.

SHA-256 values of the final source files:

- `RiffleProfiles/AsymptoticFinite.lean`:
  `d58bfc900afda611b7e2cfdd511a99eb242f18c22abef374752c1ac617056207`.
- `RiffleProfiles/TailLimits.lean`:
  `c5e2b0a3a523d4d8ad6acf8ba7401b22bdc5c1bdbe5ed22576a00afffccb8b76`.
- `RiffleProfiles/MatrixLimits.lean`:
  `37855053f56fc234006c7fe659932cf21fe4ed1ed375a55ecfcc2a0e8975e154`.
- `FROZEN_ASYMPTOTIC_CONTRACT.md`:
  `7074bcb2888043662af650e8c390e3a7c36edba602c13786a9604d1397fcefb1`.
- Frozen adversarial review:
  `2ae67367b0f0625c2ef1e482dbcd28c56e56c17e5e45efbef008b24e5b234cf5`.

## Shared definitions and helpers

`chiLog chi` is exactly `log(1/chi)`, and `exceptionalAllowance chi` is
exactly its reciprocal square root. Neither definition has been approximated.
`chiLog_pos`, `exceptionalAllowance_pos`, and `exp_neg_chiLog` have their
reviewed local domains. In particular the last identity only requires
`chi > 0`, while positivity of the logarithm and allowance requires `chi < 1`.

`exists_chiLog_cutoff` preserves the frozen stronger cutoff schema: any
`cap > 0` and real `U` give a positive `chi0 < min 1 cap` with
`max 1 U ≤ chiLog chi` for every `0 < chi < chi0`. Its explicit construction
does not divide by any possibly zero horizon or alphabet parameter.

The private positive-base power-ratio identity, exponential-error cutoff,
negative-square-root cutoff, and factor-two absorption lemma all lie in the
reviewed exp/log, parameter-limit, and finite-factor schemas. Their local
premises are discharged internally when used; none appears as an extra
assumption on A01–A06.

## A01 — `scaled_tailWeight_le_rpow`

AsymptoticFinite 52–84 preserves every frozen binder: `N ≥ 2`, `T ≥ 0`,
`K ≤ T*logScale N`, `a ≥ 0`, `beta ≥ 0`, and `z ≥ 1`. The unused proof
arguments `_hT` and `_hbeta` remain in the statement; no weakening occurred.
The left side is exactly `N * tailWeight K (floor(beta*L)+1) a`.

The proof uses `tailWeight_le` and multiplies by the nonnegative factor `N`.
It compares logarithms only of positive generating-function bases, never of
the tail itself. `Nat.lt_floor_add_one` yields the required non-strict
upper-tail threshold inequality after casting. Since `log z ≥ 0`, that
threshold gives the correct denominator direction. The numerator comparison
uses `log(1+a*z) ≥ 0` and the stated horizon bound.

The final exponent is exactly `1+T*log(1+a*z)-beta*log z`; the leading one
records the factor `N`. No assumption `a ≤ 1` is present. The proof admits
`z=1`, `a=0`, `beta=0`, `K=0`, and `T=0` without strict replacements.

## A02 — `lowCount_le_rpow`

AsymptoticFinite 87–112 retains `N ≥ 2`, `T ≥ 0`, the same horizon bound,
`beta ≥ 0`, and `0 < z ≤ 1`, with arbitrary natural `k`. Its threshold is
`floor(beta*L)`, with no added one and no hypothesis that it is at most `K`.

The proof obtains `floor(beta*L) ≤ beta*L` from nonnegativity and multiplies
by `log z ≤ 0` using `mul_le_mul_of_nonpos_right`. This is the required
reversal of the denominator exponent comparison. The resulting exponent is
exactly the frozen one. It remains valid at `k=0`, `beta=0`, `K=0`, `T=0`,
and `z=1`.

## A03 — `boundary_tailWeight_small_chi`

TailLimits 52–105 implements the exact order

`k,T,C,epsilon → chi0 → chi → N,K`.

The only fixed-parameter premises are `T ≥ 0`, `C > 0`, and `epsilon > 0`.
The output includes `0 < chi0 < 1`, and the bound holds for every `N ≥ 2`
and admissible finite `K`, without an additional large-`N` cutoff. The natural
threshold and mass argument are exactly
`floor((C/chiLog chi)*L)+1` and `k*chi`.

The proof chooses `delta=min(1/2,epsilon/(2*C))`. This satisfies the reviewed
conditions `0 < delta < 1` and `C*delta ≤ epsilon/2`; the earlier example
using `epsilon/(4*C)` was a possible proof choice, not a frozen value.
The shared exponential cutoff controls `T*k*exp(-delta*chiLog chi)` by
`epsilon/2`. Substitution into A01 and `log(1+x) ≤ x` gives precisely
`1-C+epsilon`. No loss to a multiple of `C`, no implicit `N` dependence,
and no positivity premise on `k` or `T` is introduced.

## A04 — `exceptional_tailWeight_small_chi`

TailLimits 108–158 keeps arbitrary real `C0`, arbitrary natural `k`, and
`T ≥ 0`. Its positive cutoff below one precedes every `chi`, `N`, and `K`.
The theorem includes the complete scaled expression

`N*tailWeight K (floor(exceptionalAllowance chi*L)+1) (k*(3*chi))`.

With `u=chiLog chi`, the proof uses `z=exp(u/2)`, proves the exact product
identity `chi*z=exp(-u/2)`, and proves
`exceptionalAllowance chi * log z = sqrt u/2`. It then bounds the positive
logarithmic term by `3*T*k*exp(-u/2)`. The private cutoff forces
`1+3*T*k*exp(-u/2)-sqrt u/2 ≤ -C0` using a threshold at least one.
This argument covers negative targets as well as positive ones. The leading
one, the factor three, and the exact source allowance are all retained.

## A06 boundary union — `exists_boundary_truncation_parameters`

MatrixLimits 21–50 keeps `k ≥ 2`, `T ≥ 0`, and arbitrary real `C0`, and
returns `C > 0` and `chi0 > 0` before quantifying over models and setups.
It retains the frozen `D.k=k`, explicit `D.N ≥ 2`, and horizon premises,
and the setup conditions `A.C=C` and `0 < A.chi < chi0`.

The choice `C=|C0|+4` is a valid witness for the frozen existential. A03 is
used with `epsilon=1`, giving the exact power `N^(2-C)`. The unchanged T09
theorem bounds the actual expected boundary-union row count by twice that
quantity. The proof explicitly establishes

`2*N^(2-C) ≤ N^(3-C) ≤ N^(-C0)`.

The first inequality uses `2 ≤ N` and positivity of the real power; the
second follows from `C=|C0|+4`. Thus neither the two-side factor nor the
expected-row factor `N` is lost. The threshold is rewritten through
`A.C=C` and the unchanged definitions, rather than approximated.

## A06 exceptional event — `exists_exceptional_truncation_parameters`

MatrixLimits 52–75 returns `0 < chi0 < 1` before all `chi`, models,
regularity constants, partitions, and endpoint functions. It retains
`D.k=k` and `D.K ≤ T*logScale D.N`. Here `N ≥ 2` is correctly derived from
`Model.one_lt_N`, so no extra theorem premise is added.

The partition premise is precisely `P.IsRegular chi Creg` with arbitrary
real `Creg`; no sign condition is added to it. The functions
`v,M : FullIndex D → Nat` remain arbitrary. Their word dependence,
unordered values, clipped windows, and empty exceptional sets are all
handled by the unchanged T09 theorem. The event uses the strict comparison
`exceptionalAllowance chi < exceptionalCard/logScale D.N`, so the strict
floor-plus-one threshold is retained by the subsequent tail theorem.
Allowance nonnegativity is derived from the cutoff, and the final step is
exact substitution into A04, including the factor `N` and mass `k*(3*chi)`.

Both A06 results concern the stated row-cardinality expectations under
`Shuffle.fixedMatrixLaw (modelHistogram D)`. They do not postulate independent
rows or replace a labelled row marginal by a sorted-row distribution.

## Scope and other review record

These declarations prove the frozen finite/asymptotic row consequences.
They do not establish a sorted-edge comparison, time-integral estimate,
coarse-profile word-fibre bound, or the complete original assigned proof.
No Lean source or frozen file was edited during this audit.

The separate P01–P05 candidate review is retained at
`reviews/profile_source_adversarial.md`, SHA-256
`e962a782b61bedbbdf6be188774389fd0d67e03cb021ee64a67691975c1ede14`.
It approves candidate SHA-256
`c68c9f8a5b34671e45813e297ea009a17c59187cc41faf891fd8fbfd47c34e7b`;
its comparison and freeze remain a separate batch.
