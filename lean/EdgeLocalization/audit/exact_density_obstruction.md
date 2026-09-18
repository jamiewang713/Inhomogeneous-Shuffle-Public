# Exact obstruction to the original small non-singleton density estimate

This is a source-level mathematical counterexample, not a new Lean theorem or a change to the frozen contract. Its elementary first-column mechanism is covered by the finite Lean endpoint identities, but the complete fixed-column product law below is not yet formalized in that project.

## Fixed data and source assumptions

Take N tending to infinity through positive multiples of 12, T=2, K=floor(2 log N), and t=K−2. The independent fixed-count columns have counts

- column 1: (N/4,N/2,N/4);
- column 2: (2,(N−2)/2,(N−2)/2);
- every column 3,…,K: (N/3,N/3,N/3).

All counts are nonnegative integers with sum N. Fix 0<χ<1/4. Every column has two piles of proportion at least 1/4, so all columns are χ-good. For any fixed positive local interval width, the all-tail local-good condition holds for sufficiently large N, for example with γ=1/2.

The macroscopic profile is the constant point mass at (1/3,1/3,1/3). Changing only two columns changes any empirical cell frequency by at most 2/log N. For fixed positive ρ and φ, this is absorbed by the source's φ|I|+1/log N tolerance on the first grid interval for sufficiently large N. Other intervals contain no changes. Thus these cuts are almost-profile-like for every fixed finite regular partition used by the proof.

For this profile, write l=log 3. Then A(r,s)=(s−r)l and Bθ(r,s)=(θ−1)(s−r)l. At the whole ambient deck (r,b)=(0,1), β(s)=1−sl. Evaluating both infima in FM at θ=3 gives

- N1(0,s,u;1) ≤ 3−4l−sl ≤ 3−4l < −1;
- N2(0,s,u;1) ≤ 1−4l+sl ≤ 1−2l < −1;
- N3(0,s;1)=1−2l < −1;
- β(2)=1−2l < −1.

Hence FM(0,1,2,1/2) holds. The same inequalities apply to local ambient exponents b≤1−rl, because then β(r,b)(s)≤1−sl; the positive coefficients make decreasing b harmless. None of the global profile, good-column, or margin conditions excludes the example.

## Boundary pair and stable case

Work in the whole deck, with w empty. Let y=z=v=(1) and x=(1,0). The left and right large-pile boundary digits in column 1 are 0 and 2. Both boundary words therefore stop at their first genuine crossing. They are admissible, compatible and nonterminal when K≥3.

The two side-piece occupancies for the pair are deterministically N/4. The exact source exponents are

    cF = (1/2) log_N(N/4) = 1/2 − log_N 2,
    cL(v) = log_N(N/2) = 1 − log_N 2,
    cL(x) = log_N[N·(1/2)·(2/N)] = 0.

In particular, cL(v)−cF=1/2 exactly. Every continuation ξ of v has cL(ξ)≤cL(v), so cF≥cL(ξ)/2−(log_N 2)/2. This verifies the required fluctuation-regular comparison, with its explicit error tending to zero.

Choose any sufficiently small fixed 0<δ<1/4. The initial singleton condition at v fails, while the threshold is crossed by its child x. Thus x is a first-crossing stable block, the family is not {v}, and x is not a terminal fallback (its length is 2<K). Its mean occupancy is exactly one, so cL(x)<2δ. Also cF≥δ−(log N)^(−1/2) eventually. The only exceptional extension digit is the zero in column 2, with exceptional fraction 1/log N≤αχ eventually. The pair and profile survive the stated truncations.

## Exact edge probability

Let Z be the number of rows with prefix x. The zero pile in column 2 contains exactly two row labels, so Z≤2 identically. Because the first-column middle pile has size N/2 and columns are independent,

    P(Z=2) = (N/2)(N/2−1)/(N(N−1)) = (N−2)/(4(N−1)).

The zero-based left endpoint of x is N/4 in every realization. Equivalently, in the source's one-based coordinates the possible internal edge has index m=N/4+1. A row beginning with (1,0) is the first possible row inside the first-digit middle pile. An internal edge exists exactly when Z=2 and those two rows have equal tail strings.

For any two distinct fixed row labels, one uniform-third fixed-count tail column gives equality probability

    qN = 3·(N/3)(N/3−1)/(N(N−1))
       = (N−3)/(3(N−1))
       = (1/3)·(1−2/(N−1)).

The tails are independent of the first two columns and independent across times. Therefore the exact edge probability is

    p_m = [(N−2)/(4(N−1))] · 3^(−t) · (1−2/(N−1))^t.

There is no concentration assertion in this identity. All other internal edge probabilities are zero because Z≤2 and the left endpoint is fixed.

For N≥12 the leading bracket is at least 1/5. When t≤(N−1)/4, Bernoulli's elementary inequality gives

    (1−2/(N−1))^t ≥ 1−2t/(N−1) ≥ 1/2.

This time condition holds eventually because t=O(log N). Consequently

    sum_i P((i,i+1) in E(G_Bx))² = p_m² ≥ (1/100)·3^(−2t).

The source's tail exponent is cE=−t log 3/log N, so 3^(−2t)=N^(2cE) exactly.

## Contradiction to the source conclusion

The original small non-singleton bound at article lines 1496–1503 would imply, after dividing by the positive N^(2cE),

    1/100 ≤ N^(−cF+O(δ)+o(1))
           = 2·N^(−1/2+Cδ+eN),

where eN→0 and C is a fixed loss constant independent of δ, with the source's nested parameter convention. Choose δ sufficiently small that Cδ<1/8, and then N sufficiently large that eN<1/8. The right side is at most 2N^(−1/4), which tends to zero. This is a contradiction.

If an implicit O(δ) constant were allowed to depend arbitrarily on δ, the printed estimate would lose the quantitative meaning used in the subsequent first-moment margin argument. That reading would not supply the requested frozen theorem either.

Thus a different proof decomposition or stronger intermediate estimate cannot establish this particular original conclusion with its definitions unchanged. Repair requires changing the fluctuation/stopping or density statement. The user's permission for such a new mathematical contract is pending; no repair has been applied.
