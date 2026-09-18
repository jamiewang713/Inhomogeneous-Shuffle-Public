# Ordered actual profile-count limits: independent algebra review

## Exact approval

I approve the proposal `audit/PROFILE_COUNT_LIMIT_STATEMENTS.md`, SHA-256

`6a8326d663ffd3107f3078154edaf7f9457970da62ed5fcab505e66c586a3f83`.

All three CL1–CL3 interfaces and all five proof-local helper schemas are valid as written. No assumption, quantifier, coefficient, type, or edge-case correction is needed. There are no new definitions. No implementation or frozen contract was changed during this review.

I independently compared the proposal with the actual frozen `FirstMoment.Counting`, `BoundaryEncoding`, and `ProfileClasses` definitions and the authorized unified TeX's parameter hierarchy (lines 474–488), admissibility budgets (lines 580–593), bad-profile counting statement and proof (lines 1039–1118), and refined class description in the first-moment proof (lines 1872–1876). The mathematical claim here is the count of retained classes; it does not prove the discarded-mass estimates in the same source lemma.

The three exact proposition signatures, including CL3's full dependent class/route expression, elaborate under Lean 4.33.1. This was checked with transient `#check` expressions only, not exported declarations or attempted proofs.

## The exact finite count being bounded

The existing key definition has two boundary codes, one word length, `d` count entries, labelled exceptional positions, and a route in `Fin 4`. A boundary code contains its length, final crossing digit or sentinel, and labelled outward exceptions. Consequently the existing bound is exactly

```text
4 (k+1)^2 (K+1)^(d+3) sparseCount(K,k,qb)^2 sparseCount(K,k,qe),

sparseCount(K,k,q) = ∑_{j=0}^q choose(K,j) k^j.
```

The two copies of the boundary sparse factor explain the coefficient `2` in the boundary rate. The remaining sparse factor includes the exceptional **values**, not only positions. The factor `(K+1)^(d+3)` contains the two boundary lengths and the stable-word length as well as all count entries. The route factor four and both terminal/sentinel factors `(k+1)` are retained.

The existing `sparseCount_weighted`, `sparseCount_exp_bound`, and `profileCount_exp_bound` already handle budgets above `K`: the binomial terms beyond `K` are zero. No missing `qb≤K` or `qe≤K` hypothesis should be inserted.

## CL1: a threshold uniform over finite depths and budgets

Set

```text
m = d+3,
P0 = 4 (k+1)^2 (T+1)^m,
lambda = 2a log(1/tb) + b log(1/te) + kT(2tb+te).
```

With all displayed CL1 parameters fixed, the same standard log-power little-o fact used in the frozen `profileCount_eventually` gives one natural threshold for

`P0 (log N)^m ≤ N^eps`.

Increase it to at least two and to ensure `log N≥1`. This threshold is selected **before** the later `N,K,qb,qe`. For every such finite choice satisfying the stated depth bound,

`K+1 ≤ T log N+log N = (T+1)log N`.

All bases and prefactors are nonnegative, so taking the natural power `m` proves

`4(k+1)^2(K+1)^m ≤ P0(log N)^m ≤ N^eps`.

The hypotheses `0<tb≤1` and `0<te≤1` give nonnegative `log(1/tb)` and `log(1/te)`. Thus the three given budget inequalities can be substituted with the correct inequality direction into the frozen exponential bound:

```text
2 qb log(1/tb) + qe log(1/te) + kK(2tb+te)
 ≤ [2a log(1/tb) + b log(1/te) + kT(2tb+te)] log N
 = lambda log N.
```

Multiply by the absorbed polynomial, use positivity of `N`, and rewrite

`N^eps exp(lambda log N) = N^(lambda+eps)`.

This proves precisely CL1. No limit depending on an arbitrary chosen sequence is promoted to a uniform limit. In particular the proposed proof must obtain the threshold from the fixed polynomial as described; applying separate sequence-dependent instances and interchanging quantifiers would be invalid. The approved schema avoids that problem.

CL1 permits any natural `k,d`, including zero. Its nonnegative `a,b` premises are preserved even though the exponential comparison itself only uses the supplied bounds and nonnegative logarithms. `T=0`, a zero exponent contribution, and `tb=1` or `te=1` cause no problem.

## CL2: explicit fixed-weight/small-chi construction

Here `k≥2`, `T≥0`, `C>0`, and `eps>0` are fixed first. The helper schema can be justified by the following concrete choices; these are proof-local choices, not new definitions or premises.

Let

```text
t = min(1/2, eps / [12 k (T+1)]),
h = log(1/t).
```

Then `0<t≤1/2≤1`, `h>0`, and

`3kTt ≤ eps * T/[4(T+1)] ≤ eps/4`.

This covers `T=0` without dividing by `T`. The weight `t` depends only on the already fixed data, and in particular does not depend on `chi`, `d`, or `N`.

Choose

```text
B = 1 + 16 C h/eps + (8h/eps)^2,
chi0 = min(1/(2k), exp(-B)).
```

Both terms in the minimum are positive. Since `k≥2`, `chi0≤1/(2k)<1/k` and `chi0<1`, giving the proposal's strict inequality `chi0 < min 1 (1/k)`.

For every `0<chi<chi0`, let `u=log(1/chi)`. Monotonicity of the logarithm gives `u>B>0`. The two choices of terms in `B` yield

```text
2(C/u)h ≤ eps/8,
(1/sqrt u)h ≤ eps/8.
```

For the first, use `u≥16 C h/eps` and positive denominators. For the second, `u≥(8h/eps)^2` and `8h/eps>0` imply `sqrt u≥8h/eps`; again divide by positive quantities. Thus

`2(C/u)log(1/t) + exceptionalAllowance(chi) log(1/t) ≤ eps/4`.

This uses the literal existing definition `exceptionalAllowance chi = 1/sqrt(log(1/chi))`; no substitute allowance or variable-weight rate is used.

Now fix **any** natural dimension `d`, after `chi` has been chosen. Apply CL1 with

```text
a = C/u, b = 1/sqrt u, tb=te=t, residual exponent = eps/2.
```

Its exponent is at most

`eps/4 + 3kTt + eps/2 ≤ eps`.

For `N≥N0≥2`, `log N>0`, and both `a log N` and `b log N` are nonnegative. The standard natural-floor inequality gives

```text
(floor(a log N) : ℝ) ≤ a log N,
(floor(b log N) : ℝ) ≤ b log N.
```

These are exactly the CL1 budget inputs. The final exponent comparison is valid because `N≥2>1`. This proves the CL2 conclusion including the displayed strict chi threshold and both exact floor arguments.

The order is therefore

```text
k,T,C,eps fixed
  → fixed t and chi0
  → arbitrary sufficiently small chi
  → arbitrary fixed finite dimension d
  → N0
  → every N≥N0 and every K≤T log N.
```

The polynomial threshold may depend on `d`, so the partition/time-mesh dimension may grow as `chi` decreases. No bound uniform in all dimensions after `N0` is asserted. The fixed-weight method proves exactly the source meaning of `N^{o_chi(1)}`: for each target exponent, first make the sparse-data rate small, and only afterward absorb the fixed finite count polynomial. A sharper explicit rate with a weight varying in `chi` is unnecessary.

## CL3: the actual class range

Use CL2 at dimension `d=c*k`, with `c` fixed after `chi` and before its natural threshold. This threshold is independent of the future model `D`, setup, cell map, good predicate, and route.

For every displayed actual model and setup, the already proved `profileClass_card_le` gives

```text
Nat.card(ProfileClass A cell good alpha route)
 ≤ profileCountBound D.K D.k
     (boundaryBudget A) (exceptionalBudget A alpha) (c*D.k).
```

Set `alpha=TimeProfile.exceptionalAllowance chi`. Rewrite exactly the three equalities supplied by CL3:

```text
D.k = k,
A.C = C,
A.chi = chi.
```

The existing definitions then become exactly the floor budgets in CL2. The model's depth assumption is the required `K≤T log N`. Cast the natural cardinality inequality into the reals and compose it with CL2.

No class descriptor from a different package is substituted. `ProfileClass` remains the range of the actual encoder on actual admissible pairs and actual stable words. Its `ProfileWord` domain still uses the real condition

`exceptionalCard ≤ alpha * log N`.

Only the consequence needed for encoding is rounded, exactly as in the already frozen `profileWord_exceptional_budget`. CL3 adds no finite-domain instance, legal-word assumption, regularity assumption, retention predicate, or probabilistic condition on route. Its arbitrary cell/good maps may vary with the model because the exact finite key bound is uniform over those maps. The sole fixed combinatorial dimension is their codomain size `c`.

## Edge cases and helper-schema verdict

- Empty horizons and `T=0` force `K=0` in the depth premise, but the positive constant factor in the refined polynomial is still retained and is absorbed by sufficiently large `N`.
- `d=0` and `c=0` are allowed. If `c=0` and `K>0`, there is no cell map of the stated type; its universal quantifier is then vacuous. For `K=0`, the maps and finite bounds have their usual empty-domain meanings.
- Empty actual class domains have cardinality zero. No cardinality convention is used to avoid proving finite encoding; the earlier actual class result injects the range into the existing finite key type.
- Budgets larger than `K` remain valid in both finite estimates and the floor substitution.
- The alphabet assumption `k≥2` appears only in CL2–CL3 as proposed. It ensures positive denominators in the explicit parameter choice and matches the actual source models.
- All route, stop-tag, labelled boundary, and labelled exceptional factors remain in the count. In particular the argument does not mistakenly apply a positions-only count to a values-refined class.

All five listed proof-local schemas are instances of the above arguments and are approved. They require no additional exported theorem, changed definition, or hidden uniformity assumption. No homogeneous cutoff constant or variational condition is used by this counting batch. The stochastic discarded-mass, localization, and density estimates remain separate obligations.
