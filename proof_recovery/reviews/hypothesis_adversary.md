# Independent hypothesis and falsity audit

Scope: read only `time_inhomogeneous_riffle_shuffle_unified_article.tex` and the two permitted PDFs, through their fresh exact text derivatives in this directory. No earlier reviews, project Lean source, or other papers were read. No Lean code or paper source was modified. All finite checks below used exact rational arithmetic; decimal values are only for presentation.

No actual blocked Lean declaration was supplied. I therefore identify mathematical nodes in the paper dependency graph, not an invented Lean target.

## 1. Definite false active lemma: block value-set bounded differences

**Source:** `lem:block-bd`, TeX lines 4951–4977. The stated assumptions are a uniformly random partition of `[N]` into fixed-size disjoint value sets `V_1,...,V_m,V_0`, and oscillation at most `L_j` when all other relevant `V_i` are fixed and only `V_j` and the reservoir change. The claimed conclusion is

`P(|f-E f| >= t) <= 2 exp(-2 t^2 / sum_j L_j^2)`.

**Exact counterexample with a nonempty reservoir:**

- `N=4`, `m=2`, `|V_1|=2`, `|V_2|=1`, `|V_0|=1`.
- `f(V_1,V_2)=|V_1 intersect {1,2}|`.
- After fixing `V_2`, `V_1` is a 2-subset of the three remaining values. Its count of elements in `{1,2}` changes by at most one: `L_1=1` is valid.
- After fixing `V_1`, changing `V_2` and the reservoir leaves `f` unchanged: both `L_2=0` and the strictly positive `L_2=1/4` are valid upper bounds.
- Marginally `V_1` is a uniform 2-subset of `[4]`, so `E f=1` and `P(|f-1|>=1)=1/3`.
- With `t=1,L_2=0`, the asserted upper bound is `2 exp(-2) = 0.2706705664... < 1/3`.
- Even with both constants positive, `L_2=1/4` gives `2 exp(-32/17) = 0.3044629845... < 1/3`.

This was independently enumerated over all 12 ordered partitions.

For a large explicit gap, take `N=100`, sizes `50,49,1`, and `f=|V_1 intersect [50]|`. Again `L_1=1,L_2=0`, while exact enumeration of the hypergeometric mass function gives

`P(|f-25|>=3) = 4451732538475727065989931 / 14028273713231951242326543 = 0.3173400112...`,

against the asserted `2 exp(-18) = 3.0459959489e-8`.

**Failure in proof:** lines 4971–4975 identify a coordinate oscillation after fixing *all other blocks* with the conditional range of the Doob increment after revealing only *earlier blocks*. These are different quantities under sampling without replacement. In the N=4 example the first Doob conditional mean is just `f(V_1)`, whose range is 2, despite the specified coordinate oscillation being 1.

**Downstream effect:**

`lem:block-bd -> lem:permutation-bd -> lem:lalley-comparison -> lem:lalley -> prop:cold-lower -> thm:buffered-reduced-lower-bound`.

The largest-prefix lower-bound branch is not affected by this particular lemma. Neither is the upper-bound branch.

**Classification:** mathematical falsehood, not a Lean API problem. No direct or abstract proof of this exact statement can exist in a consistent theory. Under a frozen-statement rule, stop at this node rather than adding independence assumptions.

**Possible alternative dependency, not a modification made here:** the specialized component-sorting concentration statement can instead be represented by assigning independent continuous labels to vertices and ranking them to obtain a uniform permutation. Ascents are unchanged under ranking. Vectors of labels belonging to different deterministic graph components are independent, and changing one vector changes at most two intercomponent comparisons. An independent-block bounded-differences lemma then supplies the desired specialized bound. This may repair the downstream proof without changing the final theorem's assumptions, but it does not prove the false general value-set-partition lemma.

## 2. Definite false intermediate inequality: Bonferroni coefficient

**Source:** proof of `lem:two-category-poisson`, TeX lines 4571–4576, and its mixed rare-word conditional application at lines 4683–4690.

The paper asserts

`(1/2) E(X)_2 - (1/6) E(X)_3 <= P(X>=2)`.

The coefficient of the third factorial term is wrong. The exact inversion formula already given by the same paper at lines 4481–4487 is

`1_{n>=2} = sum_{r=2}^n (-1)^r (r-1) (n)_r / r!`,

whose third coefficient is `-1/3`, not `-1/6`. At `n=3` the asserted pointwise lower expression is `2`, larger than the indicator `1`.

**Counterexample inside the actual fixed-column model, with mean <= 1:** `N=8`, `K=3`, each column has four zeros and four ones, and `X` counts rows whose word is `000`. Conditioning on the first zero-pile, I enumerated all `70^2` choices of the two subsequent zero-piles. The distribution is

`P(X=0,1,2,3,4) = (1251/4900,624/1225,264/1225,24/1225,1/4900)`.

Hence `E X=1`, `E(X)_2=27/49`, and `E(X)_3=6/49`. The claimed lower bound is `25/98 = 1250/4900`; the actual probability is `1153/4900`. The claimed lower bound exceeds the actual probability by `97/4900`.

This is not merely a small-N issue. For balanced columns with `N=2^K`, the all-zero word has mean one. Its r-th factorial moment is exactly

`E(X)_r = ((N/2)_r)^K / ((N)_r)^(K-1)`.

At `N=1024,K=10`, all requested piles have size `512`, and `4 <= N^(1/5)`. Exact rational arithmetic gives the purported lower bound `0.3332810917...`, while the valid fourth-order Bonferroni upper bound

`(1/2)E(X)_2 - (1/3)E(X)_3 + (1/8)E(X)_4`

is only `0.2890850176...`. Thus the error remains within the asymptotic moment regime of the proof. Along `N=2^K`, the respective limiting quantities are `1/3` and `P(Poisson(1)>=2)=1-2/e`.

**Effect:** the proof of `lem:two-category-poisson` is invalid as written, and therefore so is its current use in `lem:occupancy -> lem:cold-collision-count -> lem:many-cold-edges -> prop:cold-lower`. This does not establish that the two-category lemma itself is false. Correcting the coefficient changes a proof inequality, not the final theorem's hypotheses, but it must be explicit and verified after the reports are compared.

## 3. Exact missing estimates in central-window comparison

**Source:** `lem:central-window`, lines 4454–4534.

The assumptions are factorial moment relative error `epsilon_N` through total degree `R_N=floor(N^(4a_0))`, mean bounds `N^(-a_0)<=mu,nu<=L_* log N`, and `epsilon_N N^(2L_*) = o(N^(-4a_0))`.

Two displayed inference steps are not justified by those assumptions as written:

1. Lines 4500–4509 bound the weighted moment error by `epsilon_N (1+mu)(1+nu) exp(mu+nu)` and declare it `o(N^(-4a_0))`. The stated small-o condition does not absorb the two logarithmic factors. For example, the deterministic numerical sequence `epsilon_N = N^(-2L_*-4a_0)/log N` satisfies the assumption, but that displayed bound at `mu=nu=L_* log N` is of order `N^(-4a_0) log N`. This identifies an invalid estimate, not by itself a distributional counterexample to the lemma.
2. The factorial expansion is equal to the indicator only on `X+Y<=R_N`. A small probability of `X+Y>R_N` does not alone bound the expectation of the degree-`R_N` polynomial there. A signed Bonferroni truncation inequality or a deterministic polynomial remainder bound controlled by a high factorial moment is missing.

The actual application has polynomial slack in `epsilon_N`, so the logarithms may be absorbable there. That does not justify silently strengthening this standalone lemma's frozen assumptions. A valid proof under its original assumptions, or an explicit reformulated downstream lemma, is required.

**Classification:** proof dependency/API-ready inequality missing; no claim here that the standalone conclusion is false.

## 4. Scope of random-pile-size extension

**Active source:** `def:randomized-time-profile-like-cuts` lines 266ff and `cor:random-time-profile-upper-bound` lines 1999–2011. The upper extension uses uniform convergence over admissible deterministic cut arrays followed by averaging. This is a valid general probabilistic reduction once the deterministic upper theorem is proved.

**Inactive source:** the old overview from lines 2562–2785 is inside `comment`. Its lower-bound blueprint at lines 2737–2747 mentions a many-to-one random-cut extension. It is not an active proved theorem.

**Active lower part:** `thm:buffered-reduced-lower-bound` lines 2812ff and its completion at lines 5197–5205 concern deterministic cuts. The active part does not separately state or complete a randomized lower theorem.

The permitted homogeneous PDF `2510.22783v1.pdf`, pages 52–53, Lemmas 6.3–6.6, explicitly uses uniform success over deterministic cut arrays and a union over at most `N^(Kk)=exp(O((log N)^2))` arrays. The permitted `2103.05068v3.pdf`, page 37, Proposition 6.1, records the deterministic Lalley test. They support this architecture, not an automatic inference that arbitrary mixtures of individually singular measures remain singular.

The needed inhomogeneous dependency is a *single deterministic union test*: for each typical cut array choose its cold-set translate scan, prove a false-positive bound `exp(-N^c)` with a uniform fixed `c>0`, prove uniform success for its own shuffle law, and union over the finite cut arrays and translations. The active uniform-ascent proof has the needed style of null bound, but the false block-bd dependency must first be removed from the success proof. The finite cardinality count also presumes integer pile sizes; this should be explicit in any frozen Lean data type.

## 5. Upper exploration dependencies are not fully specified

**Source:** `def:recursive-first-moment-margin` lines 367ff and `lem:ub-conditional-preservation`, `lem:ub-conditional-first-moment`, `lem:ub-portenko-exponential-moment` at lines 1923–1959.

The paper defines accessibility by reference to an exploration, but does not define the exploration states, filtration, regular event, stopping convention, or exact conditional residual law at a level from which the displayed conditional estimates can be formalized. The homogeneous PDF's Section 5, particularly pages 38 and 44–46, explicitly handles these conditional laws by constrained matrix counting. Conditioning on already sorted lexicographic prefixes is not the same as fixing a bounded number of labeled rows. I found no verified counterexample to the intended upper theorem, but these are genuinely missing formal dependencies, not trusted library facts.

## Audit conclusion

The earliest decisive mathematical obstruction found independently is the false active `lem:block-bd`. It cannot be recovered under its stated assumptions. The paper also contains a definite erroneous Bonferroni proof inequality. The specialized component concentration and the ultimate lower theorem may still be valid through different proofs. Their validity must not be conflated with validity of the false helper, and no specific blocked Lean declaration has been identified from the permitted inputs.
