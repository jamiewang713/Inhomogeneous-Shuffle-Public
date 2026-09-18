# Whole-TeX reread: intended meaning of the small non-singleton estimate

I reread all 5,221 lines of `time_inhomogeneous_riffle_shuffle_unified_article.tex` in source order, including the inactive `comment` environment at lines 2562–2785, before preparing this reassessment. No source, frozen contract, or Lean implementation was changed. References below are to this original TeX unless a supplied PDF is expressly identified.

## Reassessed conclusion

The intended purpose is to show that every retained small first-crossing profile contributes a negative power of N to the shared-edge first moment, so that the class-count loss and the later exploration can be paid for. The proof attempts to obtain this by spreading the internal collision mass across a random interval location. The factor `N^(-cF)` is the proposed spreading gain.

The whole proof makes that purpose clearer than the standalone lemma does. In particular, the small-case contribution enters only through the class exponent at lines 1886–1892, and the corresponding auxiliary margin is later proved redundant at lines 2433–2462. The counterexample does not contradict the desired first-moment decay or the main mixing-time conclusion. It contradicts the unnecessarily strong displayed local density estimate with the written fluctuation definition.

There is a useful positive reassessment: **the small non-singleton part of the first-moment argument can be supplied by a weaker direct collision estimate under the existing deterministic shuffle model, without any conditional endpoint atom estimate.** A complete derivation appears below. This preserves the intended final first-moment conclusion for these classes, while not asserting that the original local inequality has become true.

## What the complete text actually fixes

| Question | Source evidence | Consequence |
|---|---|---|
| Which probability law? | Lines 95–113, 388–392, 449–451; explicitly independent fixed-count columns again at 2917–2923 | The upper density probabilities are over a deterministic-cut shuffle matrix. They are not probabilities averaged over random cuts. |
| Is the whole deck an allowed ambient block? | Lines 492–518; explicitly `w=empty`, `r=0`, `b=1` at 497 and again at 1833–1834 | The root example is within the stated ambient domain. There is no mandatory preliminary first-digit split. |
| Are coordinates shifted to begin after a good anchor? | Lines 305–312 mention local goodness as a replacement for a harmless homogeneous shift, but lines 534–565 and 623–628 start at `M_w+1` | A first-column anchor is suggested by the proof lineage, but no such reduction or indexing convention is enacted. The first ambient column contributes to cF. |
| What does cF mean? | Lines 619–643 define it from square roots of expected side-piece counts; 648–656 define “fluctuation-regular” only by `cF >= cL/2-o(1)` | The name does not define a standard deviation, a conditional variance, or non-exhaustion of a population. |
| What do “small” and “singleton” mean? | Lines 661–686 and 1495–1511 | Small means a bound on the expected-size exponent. Singleton means the stable family equals `{y vee z}`. Neither means that the realized occupancy is at most one. |
| Which edges are counted? | Lines 460–472 and 1488–1511 | All equal-string adjacent edges internal to the prefix cylinder are included. An edge at the cylinder's left endpoint is still internal when both rows lie in the cylinder. |
| Is density conditional on a good event? | The displayed bounds at 1492–1511 are unconditional. The proof uses S_x at 1525–1541, with exponentially small complement prescribed at 1212–1214 | A polynomially likely collision cannot be removed from this lemma through S_x. |
| Is density averaged over edge positions? | Lines 1497–1498 and 1838–1841 use a sum of squared fixed-rank probabilities | There is no division by N, averaging over a uniform position, or random external translation. |
| Which profiles are discarded? | Lines 579–592 and 1039–1118 | Boundary truncation counts repeated small-side digits; profile truncation removes `R_x>alpha_chi`. A single exceptional last digit survives. |
| Is the small estimate only needed after exploration? | Lines 1817–1914 prove the unconditional first moment first; lines 1923–1943 subsequently apply it conditionally | Exploration does not retroactively restrict the standalone root-level lemma. |
| Does the lower-bound half redefine upper cF? | Lines 3362–3373 introduce a separate “true location-fluctuation” exponent c_loc; the import list at 2844–2895 does not import the upper ambient atom theorem | The later variance definition cannot silently replace cF in the upper proof. |

## Strongest charitable coherent reading

The intended mechanism is the deterministic-pile analogue of the following principle: conditional on a prefix block's internal strings, the internal equal-string graph is known up to a random translation. If that translation has atom probabilities of order `N^(-F)`, an expected internal edge mass E is spread over that location scale. Squaring the per-position probabilities and summing leaves a factor approximately `E^2 N^(-F)`. Lines 1530–1547 state this mechanism explicitly; lines 1569–1583 apply it to small blocks.

The 2025 source makes the missing anchor particularly plausible. Its Definition 4.3, printed pp. 18–19, starts the boundary stops and fluctuation maxima at column 2. Its Proposition 4.2 and Lemma 4.5 proof, printed pp. 18 and 20–22, use a good first column to provide a strict first-digit slice inside a larger resampling population. The prose before Definition 4.7, printed p. 23, explains why fixed first-column counts require this treatment. The unified note says it mirrors that architecture (lines 81, 442–444) and mentions a harmless initial shift (312).

A coherent intended implementation would therefore first establish an anchored decomposition using a suitable early good column, distinguish deterministic side counts from random side counts, and retain enough unrevealed population for the conditional resampling argument. The local-good hypothesis can supply good columns within a short macroscopic interval; a buffered proof may be able to pay for discarding such an interval. That would be a proof reduction to establish, not a new non-degeneracy assumption to guess.

However, this reading is **not yet an interpretation forced by the written definitions**. The root ambient is explicit, crossings at its first column are explicitly legal, and both fluctuation maxima include that column. Simply starting with a good column does not fix the issue: the counterexample's first column is already good. Simply starting an ambient proof inside its first-digit slice also does not justify replacing the full resampling population by that slice while conditioning on its residual counts. The unused population must actually be present in the conditional law.

## Why the later conventions do not remove the example

### Ambient recentering and conditional means

Lines 509–512 recenter positions at the ambient left endpoint and correctly say that translating an entire block does not change its internal edge **count**. This does not imply that independently translating two random copies preserves their expected shared edges, or preserves a sum of squared marginal location probabilities. For the root ambient in the example, its left endpoint is deterministic anyway, so either global or recentered coordinates give the same obstruction.

Lines 1286–1290 explicitly restrict the anti-concentration construction to the ambient population and temporarily use ambient column counts. The transfer lemma's proposed positive complementary fractions at 1177–1178 are conclusions, not standing assumptions defining which pairs may be used. The `a=b` construction at 1388–1408 permits the first column; there the sample can equal the entire residual population. The numerical comparison defining fluctuation-regularity does not exclude that case.

The lower half is more explicit about legitimate conditioning: lines 3032–3077 and 3138–3166 subtract prescribed row counts and prove the residual product law; lines 4400–4451 do the same for factorial moments. These passages reinforce the requirement to state the actual residual population and counts. They supply no convention under which deterministic first-column endpoints become random.

### Conditioning on internal information

The charitable reading of U_x at 1209–1212 is the multiset of internal strings, or their original labelled-row information, excluding sorted positions. That is exactly the information needed for “fixed up to translation” at 1530. Even this least restrictive sensible interpretation leaves the example's left endpoint deterministic. Conditioning cannot create randomness in a constant endpoint. The good-event probability identities consequently remain an obstruction without any ambiguity about whether labels are revealed.

### Windows, truncations, and regularity

The deterministic window at 1238–1244 is an upper bound on possible displacement. A constant endpoint lies inside such a window; a wide upper window does not imply a small atom. The size/window parts can therefore hold in the example while the atom part fails.

The example x=(1,0) has one exceptional digit and expected occupancy 1. The definitions retain such a word: `R_x=1/log N`, and lines 999–1007 explicitly allow a first crossing caused by an exceptional final digit, changing S by zero. Thus interpreting “remaining retained profiles” as “all digits good” would contradict the written profile machinery.

At its deterministic left rank, `P(m in I(B_x))=P(Q>=1)` tends to 3/4, so the relevance threshold at 1445 also retains this block. The summed density receives its contribution at an actual internal edge, not an excluded boundary edge.

The later global typical set S_1 is only specified through regularity and sparsity sketches at 1974–1983. Its allowed polynomial exceptional probability might in principle accommodate a new global discard of some rare anchored collisions. No such discard or counting argument is supplied, and the local density lemma is not stated with S_1. In particular, this possibility is a potential repair of the overall proof, not an explanation of the existing formula.

### Random cuts and the lower half

The random-cut upper extension at 1999–2011 first conditions on typical deterministic cuts and then averages the uniform deterministic conclusion. It does not change the deterministic local law used in the density theorem. A deterministic cut sequence is also a permissible degenerate mixture.

The revised lower proof consciously uses relative cold intervals and permits the ambient global location to enter only through a random translate (3449–3451, 4123–4223). Its ascent test scans all translations (4899–4948, 5115–5162). This avoids a need to anti-concentrate the ambient translation. It is a different use of localization, not a hidden shift shared by the upper density calculation.

The earlier random-cut lower-bound blueprint at 2737–2747 is inside the inactive comment environment ending at 2785. It does not introduce an active upper-bound convention.

## What the final small-case argument actually needs

Let

```
d_x = sum_m P((m,m+1) in E(G_Bx))^2,
e_x = |E(G_Bx)|,
mu_x = E|I(B_x)|.
```

For N>=2 define the exact tail pair-collision factor

```
q_x = product_{j>M_x} sum_l n_l^(j)(n_l^(j)-1)/(N(N-1)).
```

An adjacent equal-string edge injects into an unordered pair of original row labels carrying equal full strings. Independence of the columns and uniform fixed column counts therefore give

```
E e_x <= binom(N,2)
         product_{j<=M_x} [n_{x[j]}^(j)(n_{x[j]}^(j)-1)/(N(N-1))]
         q_x
      <= (mu_x^2/2) q_x.
```

The last step uses only `(n)_2/(N)_2 <= (n/N)^2`. Also, summing the same one-column inequality over digits gives `q_x <= N^cE(x)`. Consequently,

```
d_x <= (sum_m P(edge_m in G_Bx))^2
    = (E e_x)^2
    <= (mu_x^2 q_x/2)^2.
```

This is an exact finite estimate. It has no concentration-event remainder and no conditioning on U_x. Empty or one-row occupancies contribute zero, a zero tail collision factor gives zero, and an empty tail product is 1. A fixed ambient prefix is simply part of x in this unconditional computation. For exploration, the same argument must be applied to a proved product law with its **actual residual population and counts**; replacing N by an ambient expectation is not justified.

Writing `mu_x=N^(L_x+o(1))` and using `L_x<2delta` gives

```
d_x <= N^(4L_x+2cE+o(1))
    <= N^(2cE+8delta+o(1)).
```

There is no `-cF` gain. Nevertheless this is sufficient after class counting. Write `L_v=cL(y vee z)`, `F=cF`, and let epsilon denote the source's retained-profile approximation losses. For a non-singleton first crossing, lines 999–1007 and 1777–1782 give

```
S <= L_v-F+O(epsilon)+o(1).
```

The entropy estimate at theta=3, the tail estimate, and `F>=L_v/2-o(1)` give

```
H+2cE
 <= 3(L_v-F)-B_3(s,u)-2B_2(u,T)+O(epsilon)+o(1)
 <= (3/2) beta(s)-2A(s,T)+O(epsilon)+o(1)
  = 2 beta(T)-(1/2) beta(s)+O(epsilon)+o(1).
```

These are the local ambient beta quantities when working with parameters (r,b). The identity uses additivity of A. The one-column bounds `B_3>=2A` and `B_2>=A` are proved at 2349–2395.

Because this is the non-singleton stable branch, the stopping definition gives `L_v-F>=delta`. Combining this with the fluctuation comparison yields `L_v>=2delta-o(1)`, and then `L_v<=beta(s)+O(epsilon)+o(1)` implies `beta(s)>=-O(epsilon)-o(1)`. Thus the tail-size margin alone gives

```
H+2cE <= -2eta+O(epsilon)+o(1).
```

After the `8delta` density loss and the source's subpolynomial class-count cost, a negative exponent remains. This argument also avoids the delicate assertion that every low-F small case must be an initial singleton: it applies to all small non-singleton first-crossing blocks for which the existing profile estimates hold. Exceptional final digits cause no problem, because their exact cost stays in Q and they do not increase S. No unaccounted rare-event second-moment error is used.

For an initial small singleton, the same exact inequality and `4L_x <= 2L_x+4delta` give

```
d_x <= N^(2L_x+2cE+4delta+o(1)),
```

which is the already intended singleton form and combines with the existing singleton numerical margin. Terminal singleton blocks can use the even simpler inequality `d_x<=E e_x<=mu_x`.

## Implications for formalization

The most charitable reading supports the **final small-class decay goal**, and the direct collision calculation proves a suitable intermediate route under the original unconditional shuffle model. It does not validate the written `N^(-cF+2cE+...)` standalone theorem. The concrete pinned-edge example remains consistent with the weaker estimate and still contributes a rapidly vanishing amount to the first moment.

An honest continuation can therefore distinguish two tasks: prove the exact fixed-column collision law and the sufficient small-class exponent calculation; separately establish an anchored localization framework for the large-block and conditional exploration parts. The latter still needs a precise population, sigma-field, and indexing construction. The whole-file reread does not authorize smuggling an endpoint atom estimate into assumptions or silently altering cF.

No existing frozen theorem statement has been changed here. The alternate argument is a mathematical audit of what the final proof needs, to be independently compared and explicitly stated before any new formalization contract is frozen.
