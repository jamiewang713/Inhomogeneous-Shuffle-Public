# Independent reconstruction of uniform asymptotic ambient estimates

This pre-code report uses the permitted TeX and the already proved finite matrix, exponent, and relative-coordinate modules. I reread the uniform-limit convention at TeX 476–488, ambient definition at 490–517, three edge-density cases at 1486–1513, singleton argument at 1594–1637, and terminal statement at 1640–1660. No Lean implementation, source change, or frozen-artifact edit is made here.

## Exact source assumption and one scalar definition

The source fixes the small parameters before taking N to infinity, and assumes that the deterministic ambient prefix has actual expected occupancy `N^(b+o(1))`. The relevant finite scalar property is

`HasSizeExponent (f : Nat -> Real) (b : Real) :=`

`for every epsilon>0, there exists N0, for every N>=N0,`

`  (N:Real)^(b-epsilon) <= f N and f N <= (N:Real)^(b+epsilon)`.

All powers are real powers of the real cast of N. This is a proposition expressing two-sided asymptotic power control; it stores no chosen rate, supplied logarithm identity, error function, or density estimate. Its definition need not constrain N0 to exceed one, since every application can enlarge the threshold to at least two.

On sufficiently large N this is exactly the usual scalar meaning of `f N=N^(b+o(1))`. In one direction, the lower sandwich forces f N positive and the logarithmic ratio tends to b, as proved below. Hence the computed error gives the usual power representation by the positive-base logarithm identity. Conversely an eventual representation with an error tending to zero implies every sandwich by positive-base power monotonicity. No fixed multiplicative constant, sign condition on b, or polynomial lower bound beyond the stated sandwich needs to be assumed separately.

This formalizes the source's ambient expected-size assumption, not its additional time relation `A N/log N=r+o(1)`, profile approximation, retained-pair conditions, or concentration claims. Those conditions are unnecessary for this bounded conversion and are not inferred from it.

## Family data and the actual expectation

Fix an alphabet size k and deterministic functions K,A:Nat->Nat. Let

`n : for every N, Fin(K N) -> Fin k -> Nat`,

with `hn : for every N j, sum_a n N j a=N`, and let `hA : for every N, A N<=K N`. The ambient word is the deterministic family `w : for every N, Fin(A N)->Fin k`. Its reference exponent b is a fixed real number.

The sole asymptotic input is HasSizeExponent applied to

`f N = (matrixLaw (n N) (hn N)).expectation`

`  (fun omega => (occupancyCount N (sortedRows (n N) omega) (prefixWord (w N)) : Real))`.

Thus the assumption is about actual expected occupancy under the already constructed original-N fixed-count matrix law. It is not an assumed power identity for prefixMean and does not use a new conditional ambient law. The exact proved expected-sorted-occupancy theorem will identify f N with the existing prefixMean during the proof.

No global ambient legality premise is needed. The size property itself forces positive actual expectation eventually. Each finite child estimate retains its already frozen legality premise, which also implies the ambient word's legality for that child through the given prefix relation. Persistent zero ambient occupancy would contradict the assumed lower sandwich; it cannot be hidden by the totalized real logarithm.

## Seven useful theorem obligations

### 1. Scalar explicit logarithmic-error control

For f,b with HasSizeExponent f b and every positive real accuracy epsilon, prove

`exists N0, 2<=N0 and for every N>=N0,`

`  abs(Real.log(f N)/Real.log(N:Real)-b) <= epsilon`.

Choose the sandwich threshold for epsilon and enlarge it to `max 2 N0`. At every admitted N, the base is positive and greater than one, so its logarithm is positive. The lower power is strictly positive; hence f N is strictly positive. Apply trusted logarithm monotonicity to both sandwich inequalities and `Real.log_rpow` to their endpoints. Division by the proved positive log N gives

`b-epsilon <= log(f N)/log N <= b+epsilon`.

The absolute-value bound follows by elementary real inequalities. All nonzero and positivity requirements are derived locally. The non-strict epsilon formulation is equivalent to the usual strict convergence formulation: apply it with epsilon/2 to obtain a bound strictly below epsilon. If the statement designer selects a strict conclusion instead, using the half-accuracy sandwich proves it with the same assumptions.

This theorem may expose no named positivity helper: the needed positivity is proved inside this logarithm argument. Its result does not claim anything about log base zero or one.

### 2. Computed ambient error tends to zero

With precisely the family data and actual-occupancy size assumption above, for every epsilon>0 prove

`exists N0, 2<=N0 and for every N>=N0,`

`  abs(ambientMeanError N (n N) (hA N) (w N) b) <= epsilon`.

Apply obligation 1 to the displayed actual expectation f. For each N, the previously proved `matrix_expected_sorted_occupancy` identifies that expectation with `prefixMean N (n N) (hA N) (w N)`. Unfolding ambientMeanError then gives the exact conclusion. Neither error convergence nor a mean-power equality is an added hypothesis. There is no dependence on a child word, its length, its tail, or its stable class in this threshold.

### 3. Uniform ambient-relative fourth-power exponent

For every epsilon>0, prove that one threshold N0>=2 works for every N>=N0 and then **every** M, hM:M<=K N, hAM:A N<=M, x:Fin M->Fin k, pointwise extension

`for every t:Fin(A N), x(Fin.castLE hAM t)=w N t`,

and legality `legalPrefix (n N) hM x`. With the existing source L and E at these data, conclude

`Drel(N,M,x) <= (N:Real)^(4*L+2*E+epsilon)/4`.

Here Drel is the already proved relative density with the actual samplewise shift

`ambientLeft N (sortedRows (n N) omega) (prefixWord (w N))`.

Use obligation 2 with accuracy epsilon/4. Its bound on the computed ambient error e gives `4*e<=epsilon` without assuming e nonnegative. The already proved R.14 gives the exponent `4*(L+e)+2*E`. Positive-base power monotonicity yields the displayed bound. The error written with the derived bound proof `hAM.trans hM` agrees with the family proof `hA N` by proof irrelevance; this requires no equality assumption.

The quantifier order is essential: N0 is chosen before M,x and their proof arguments. It is constructed from the ambient-only threshold, so it controls all legal extensions simultaneously, even though the set of extension lengths and words changes with N. No union bound or count of these words is needed.

### 4. Uniform small coarse exponent

For each epsilon>0, retain the same post-threshold quantifiers over N,M,x, then quantify over every real delta and impose the exact source cutoff L<2*delta. Conclude

`Drel(N,M,x) <= (N:Real)^(2*E+8*delta+epsilon)/4`.

Use obligation 3 and `4*L<=8*delta`. The same threshold works for every child and every delta satisfying this cutoff. The threshold is chosen before delta because the ambient-error estimate does not depend on it. This stronger uniform order includes the source convention of fixing delta before N tends to infinity. No assumption delta>0 is needed for this algebra and no cutoff on L+e is substituted.

### 5. Uniform singleton-shaped small exponent

With exactly the same data and cutoff as obligation 4, conclude

`Drel(N,M,x) <= (N:Real)^(2*L+2*E+4*delta+epsilon)/4`.

Apply obligation 3 and `4*L<=2*L+4*delta`. This is valid for every numerically small legal prefix. It therefore applies to the source's small singleton class once membership in that class is established, without inserting a new singleton predicate or endpoint-spread premise here. The explicit O(delta) term is 4*delta, and the only asymptotic loss is the arbitrary positive accuracy epsilon. The coefficient 1/4 remains exact.

### 6. Uniform ambient-relative mean exponent

For every epsilon>0, one N0>=2 works for every N>=N0 and all the legal extension data in obligation 3, with conclusion

`Drel(N,M,x) <= (N:Real)^(L+epsilon)`.

Use obligation 2 at accuracy epsilon, or reuse the common epsilon/4 threshold from obligation 3, and the existing R.17 bound `Drel<=N^(L+e)`. The signed error is bounded above by its absolute value, and positive-base monotonicity finishes. No small-size or tail condition is introduced. The epsilon/4 choice also demonstrates directly that one ambient threshold can support all five bounds simultaneously.

### 7. Uniform terminal specialization

For every epsilon>0, one N0>=2 works for every N>=N0 and every full-length x:Fin(K N)->Fin k extending w N, with legality at the reflexive full-length bound. Conclude the same mean exponent bound

`Drel(N,K N,x) <= (N:Real)^(L+epsilon)`.

Specialize obligation 6 to M=K N, or apply R.18 with the error control. The already proved X.13 says the tail exponent is exactly zero at full length. There is no need for a newly named tail-zero lemma, terminal-size premise, or second-moment estimate. This supplies the scalar asymptotic form of the source terminal bound, with no O(delta) loss required by this route.

## Uniformity and limiting cases

- Thresholds for the five matrix conclusions must be existentially quantified before every child length/prefix and, in the small cases, before every delta. Placing `exists N0` after x would lose the requested uniformity. The computed ambient error is the only asymptotic quantity used, so the stronger uniform order follows directly.
- The ambient family itself is fixed deterministic data. The result does not provide one common threshold over arbitrary unrelated ambient families, random exploration-selected ambients, or all retained profile classes merely because each N has finitely many such classes. A fixed finite collection with separately proved size properties can use a maximum of its thresholds; uniformity over a larger collection needs its own precise hypothesis or proof. This report does not silently claim that the TeX's full uniform-profile convention has been discharged.
- The source limit fixes delta and the other small parameters before N tends to infinity. The post-threshold universal delta quantifier includes that setting and is justified because these algebraic constants do not depend on delta. It does not interchange any limits in unproved profile or concentration inputs, or provide a convergence rate for the ambient size property.
- N=0 and N=1 may have arbitrary totalized real-power/logarithm values in the definition, but each proof explicitly enlarges its threshold to at least two. All older all-N finite theorems remain unchanged.
- K N=0 and A N=0 are allowed. For an empty ambient the actual expectation is exactly N. Its source choice b=1 therefore has the expected zero error. No positivity of a present column or choice of a digit is needed when there are no columns.
- If the alphabet is empty and a positive-N column exists, feasibility is impossible; no extra inhabited-alphabet assumption is added. The empty-column family remains possible. A selected pile count one is legal and may give zero child density without affecting any logarithmic mean identity.
- A permanently empty or illegal ambient cannot satisfy HasSizeExponent with finite real b, because every sufficiently large lower power is positive. Finitely many such small-N exceptions are harmless. This is a consequence of the assumption, not a positivity premise added to it.
- The reference exponent b, each child L, and the computed error may have either sign. No lower bound on a child mean or positive part of its exponent is used. The source small cutoff remains on L itself.
- A zero fixed-count tail collision factor remains allowed. The existing exact tail comparison handles it without taking its logarithm. No tail approximation or rate depending on the child's M enters the threshold.
- Every density is the now-defined ambient-relative density under the unchanged original-N matrix law. No comparison with absolute density or conditioning on realized ambient occupancy appears. The existing two-copy identity gives the independently recentered shared-edge meaning without adding another overlap theorem here.

## Dependency and scope verdict

The proposed seven-obligation chain is scalar size sandwich -> scalar logarithmic-error control -> actual-occupancy ambient error -> uniform fourth-power and mean exponents -> the two small consequences and terminal specialization. Local arithmetic, threshold maxima, real-logarithm monotonicity, and the already proved finite theorems suffice; no extra named helper, rate, assumption, or axiom is needed.

The property on actual occupancy is the precise scalar content of the source's ambient `N^(b+o(1))` hypothesis. The resulting child bounds are uniform over every legal extension of that ambient family. They provide the finite-to-asymptotic small-singleton and terminal numerical implications, plus valid coarse and unrestricted count-based estimates. They do not supply the source's stronger minus-cF spatial factor, classify stable blocks, prove profile approximation, or complete the remaining localization and upper/lower-bound dependencies.

## Final exact-signature comparison and acceptance

After completing this reconstruction, I read the complete final `asymptotic_contract_statements.md` and the independent assumptions report, including its exact-inventory acceptance. I compared the body of A.D01 and every parameter, quantified binder, and conclusion of A.01–A.07 with the arguments above. **I accept the selected one definition and seven statements exactly, with no remaining correction before freeze.** No Lean code was written in this review; no earlier report or frozen artifact was edited.

A.D01 is precisely the two-sided eventual real-power sandwich at every positive tolerance. It contains no positivity, monotonicity, rate, log-error, or density premise. A.01 correctly outputs a threshold at least two and a non-strict absolute logarithmic-error bound at arbitrary positive accuracy. The positive lower power forces f N positive only after that derived threshold, and positivity of log N justifies division. Its weak epsilon conclusion is equivalent to strict eventual smallness by using half the requested tolerance. Negative or zero initial scalar values and either sign of b remain allowed.

A.02's explicit ordered family data are exactly k, K, A, n, hn, hA, w, b, and the size property of the actual expected sorted occupancy. Its conclusion is the previously defined computed ambientMeanError, with no substitute mean assumption or global ambient-legality premise. The exact expected-occupancy theorem supplies the only conversion to prefixMean. Eventual positivity is derived from the source size assumption, and the existing finite child estimates retain their own legality premise unchanged.

A.03 chooses N0 before N and before every M, hM, hAM, x, hprefix, and hx. It retains the actual ambientLeft shift, exponent `4*L+2*E+epsilon`, and denominator four. Applying A.02 with tolerance epsilon/4 establishes one bound for all those child choices. The two ambient-length proof terms agree by proof irrelevance, so the error does not become child dependent.

A.04 and A.05 resolve the uniformity choice explicitly: delta is not an input parameter before the cutoff. Each conclusion has `exists N0>=2, for every N>=N0, for every real delta`, followed by the complete child data and the strict source cutoff `L<2*delta`. Hence the same cutoff is uniform jointly in delta and every legal child. This stronger order follows directly from A.03's already chosen cutoff and the two pointwise linear exponent comparisons. The exact exponents remain `2*E+8*delta+epsilon` and `2*L+2*E+4*delta+epsilon`, each divided by four. No sign for delta, modified size cutoff, or singleton classification is added.

A.06 retains the same child-uniform threshold structure and gives `N^(L+epsilon)` with no denominator or small-size premise. A.07 specializes this to all full-length legal children of the same ambient word, using the supplied hA(N) in their extension relation. It introduces no terminal-size or singleton-family premise; the previously proved full-length E=0 identity remains available separately.

The fixed ambient family w may vary with N as explicitly typed. The threshold is for that one deterministic family and is not claimed uniform over an additional collection of unrelated ambient families or exploration histories. Empty words, empty/equal/full lengths, valid empty-alphabet/column data, selected singleton piles, zero tail collision factors, and the excluded initial populations N=0/1 are handled exactly as in the independent argument. No additional profile, concentration, or rate hypothesis is hidden in the statements.

I accept the exact three-module layout: Asymptotic.Model for A.D01, Asymptotic.Error for A.01–A.02, and Asymptotic.Estimates for A.03–A.07. The dependency graph and local helper plan are complete. Threshold enlargement, positive-log division, proof-irrelevant length casts, error absorption, and terminal specialization require no additional named declaration, custom instance, hypothesis, or axiom.
