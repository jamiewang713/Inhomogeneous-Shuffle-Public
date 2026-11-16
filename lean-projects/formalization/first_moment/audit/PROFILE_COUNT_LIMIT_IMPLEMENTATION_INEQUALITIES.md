# Ordered profile-count limits: implementation adversarial review

**Approve CL1–CL3 without corrections.** The implementation matches the frozen exact interfaces and all five reviewed proof-local schemas. The threshold construction is uniform where claimed, and chi is chosen before the dimension and the final deck-size threshold. No new hypothesis or changed finite count was found.

Reviewed artifacts:

```
FirstMomentModel/ProfileCountLimit.lean
SHA-256 b1d28e2066343c32e1a9c49fea565f4574904fd8bf1394af3c8f7687e1958d29

PROFILE_COUNT_LIMIT_CONTRACT.md
SHA-256 3252bc424f8d01aae30d4abeea57e43afa6cccb2da867df4b0ebf547c5857458

audit/PROFILE_COUNT_LIMIT_STATEMENTS.md
SHA-256 6a8326d663ffd3107f3078154edaf7f9457970da62ed5fcab505e66c586a3f83
```

This is an independent read-only source/interface audit. The root agent is running the separate trust verification; I did not repeat that build, alter code, or edit the contract or prereview. The implementation contains exactly the three exported theorems and no new definitions or exported helpers. There are no axioms, placeholders, unsafe declarations, or extra instances in the module.

## CL1: `profileCount_uniform_eventually`

All binders and hypotheses agree exactly with CL1: fixed natural `k,d`; real `T,a,b,tb,te`; nonnegative `T,a,b`; `0<tb,te<=1`; and positive epsilon. The conclusion chooses `N0>=2` before universally quantifying `N,K,qb,qe` and their three finite bounds. No premise such as `qb<=K`, `qe<=K`, `k>=2`, or `d>0` has been added.

The implementation obtains the eventual bound from the fixed expression

```
C0 = 4*(k+1)^2*(T+1)^(d+3),
C0*(log N)^(d+3) <= N^eps.
```

It uses `isLittleO_log_rpow_rpow_atTop`, transfers the real eventual bound along natural casts, and intersects it with `log N>=1`. The resulting natural threshold is extracted **before** the finite values `K,qb,qe` are introduced. Hence there is no invalid promotion of separate sequence-dependent thresholds to a common one.

For every later `K<=T log N`, the proof establishes `K+1<=(T+1)log N`, then absorbs exactly the factor `4*(k+1)^2*(K+1)^(d+3)`. The source `profileCount_exp_bound` is used literally. Both reciprocal logarithms are proved nonnegative, so each budget inequality is multiplied in the correct direction. The real exponential rate is

```
2*qb*log(1/tb) + qe*log(1/te) + k*K*(2*tb+te).
```

The conversion to the asserted real power uses `N>0`, derived from `N>=2`, and adds the polynomial epsilon exactly once. No boundary factor, route factor, digit-label factor, or constant polynomial factor is dropped.

## CL2: `profileCount_small_chi`

The exact order is preserved:

```
fixed k,T,C,eps -> choose chi0 -> every chi<chi0 -> every d -> choose N0
-> every N,K satisfying the displayed bounds.
```

The implementation's explicit choices are the previously reviewed ones:

```
t = min (1/2) (eps/(12*k*(T+1)));
h = log(1/t);
B = 1 + 16*C*h/eps + (8*h/eps)^2;
chi0 = min (1/(2*k)) (exp(-B)).
```

They are defined before chi and d are introduced. The premises imply `0<t<=1/2`, `h>0`, and `0<chi0<min(1,1/k)`. The bulk rate is at most `eps/4`. For every positive chi below chi0, the proof establishes the positive denominator `u=log(1/chi)>B` and then

```
2*(C/u)*h <= eps/8;
exceptionalAllowance(chi)*h <= eps/8.
```

The inverse square root is the existing definition `1/sqrt(log(1/chi))`; its denominator is explicitly positive before division. Nothing relies on a totalized inverse or square root at chi zero or chi at least one. The first two rates plus the bulk rate are at most `eps/2`. CL1 is called with its remaining polynomial allowance `eps/2`, giving the exact requested exponent eps.

Both natural-floor arguments are proved nonnegative using the positive chi denominator, `C>0`, the existing nonnegativity of the exceptional allowance, and `log N>=0`. `Nat.floor_le` then supplies precisely the two CL1 budgets. No floor argument is presumed nonnegative without proof, no budget is capped at K, and no real profile predicate is replaced by its floor.

## CL3: `profileClass_small_chi`

The printed binders match CL3 exactly. After fixing chi and c, the implementation invokes CL2 at dimension **`c*k`**, then chooses `N0` before introducing the actual model D, setup A, cell map, good predicate, or route. Thus N0 is uniform over all those later data subject to their stated equalities and bounds.

`profileClass_card_le` supplies the genuine existing realized-range cardinality bound. The order-preserving cast gives

```
Nat.card(ProfileClass) <=
profileCountBound D.K D.k (boundaryBudget A)
  (exceptionalBudget A (exceptionalAllowance chi)) (c*D.k).
```

The final rewrite uses only `D.k=k`, `A.C=C`, `A.chi=chi` and the exact budget definitions, as frozen. There is no silent relation between A.C and a partition regularity constant. No extra finiteness, legality, retention, profile regularity, or route-correctness premise occurs. Arbitrary good predicates still describe the same actual ProfileWord domain with its original real exceptional cutoff.

The statement bounds each class domain individually; it does not count the union of class domains over every ambient prefix, setup, or model. Its implementation respects that scope.

## Degenerate cases and retained scope

- `T=0` forces K=0, while `T+1` keeps the chosen weight meaningful. The polynomial's remaining constant is still absorbed by the eventual argument; the proof never asserts N0 can be two.
- `k=0` or `d=0` in CL1 are permitted. CL2 and CL3 retain their original `k>=2` hypothesis; no extra dimension positivity appears.
- `c=0` is allowed. A cell map into `Fin 0` exists only in the compatible empty-domain cases, and the universally quantified statement needs no added nonempty-domain premise.
- Natural budgets zero or greater than K are accepted by the original sparse-count theorem and by all new steps.
- Empty actual profile domains have empty realized class ranges. The implementation uses the previously proved finite encoder bound, not the totalized cardinality of an unproved infinite type.
- The dimension is allowed to depend arbitrarily on chi. It is not allowed to change with N after N0, and no such stronger assertion appears.
- The count remains `4*(k+1)^2*(K+1)^(d+3)*sparseCount(K,k,qb)^2*sparseCount(K,k,qe)`, including exceptional values and both boundary sparse assignments.

No homogeneous cutoff, variational premise, stochastic density estimate, localization claim, or new model assumption enters these three counting theorems.
