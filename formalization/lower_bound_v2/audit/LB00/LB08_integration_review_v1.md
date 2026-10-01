# LB00 independent LB08 central-scale and final-assembly review v1

This coordinator source review supplements the lane's three final independent reports. LB00 did not author or edit these proof modules. Verdict: no mathematical or statement defect found in the reviewed scale, remainder, concrete central specialization and final assembly. The separate coordinator build and declaration audit supply kernel verification; this report alone is not that certificate.

Scales.lean retains tau=N^(-1/100), B=log(N)/10, R=floor(N^(1/25)) and m=2*(R/4) with natural division. Exact evenness and 2m≤R are proved arithmetically. When N^(1/25)≥10, both floor losses are retained to give m≥2 and m≥N^(1/25)/4. The upper bounds m≤N^(1/25)≤N and R≤N^(1/5) are valid at N≥1. The eventual theorem chooses a single threshold from fixed D,C before N and supplies log N≥1, m log 2≥3 log N, (log N)^3≤N^(1/50), and 0≤epsilon≤1. Bounding epsilon by the larger N^(1/5) moment radius is legitimate because D,C and the log factors are nonnegative.

CentralScales.lean controls the actual polynomial remainder at all occupancies. The nonnegative exponential-series term gives t^m/m!≤exp(2t)/2^m; replacing m-1 by m preserves the upper bound. For t≤2B, the order budget gives 2t-m log 2≤-(13/5)log N. Since m≤N, the entire remainder is at most N^(-8/5)≤N^(-1). This includes t=0 without a logarithm of t. Both remainder factors are nonnegative and at most N^(-1)≤1, so their product is at most N^(-1) as well. Multiplication by three and addition cost at most 9N^(-7/10); no probability-tail truncation is substituted.

For the moment term, nonnegative means with mu+nu≤2B give 1+mu,1+nu≤2log N and C log N+1≤(C+1)log N. The exact power exponent is 1/50+2/25-1+1/5=-7/10. Hence the stated common central constant 4D(C+1)+9 is valid. The one-variable estimate is the same two-variable inequality at nu=0, so its larger range through 2B is retained.

CentralModel.lean applies actual LB03 one- and two-word factorial estimates, with positivity proved from the selected piles. The two-word case retains word distinctness. Every degree through m or 2m is explicitly bounded by R and then N^(1/5); each actual moment error is dominated by the fixed common epsilon. All central comparison inputs, including evenness, m≥2 and epsilon≤1, come from the proved scale theorem. The constants and maximum threshold precede N,k,K,cuts and words.

Main.lean first obtains the completed rare-pair, nonrare-pair and marginal statements, then chooses D=max(Dr,128) and one maximum threshold before varying arrays and families. It handles both orientations of a rare category before the nonrare branch, with an explicit probability-event symmetry. Ordered covariance summation receives the actual pair estimate and nonnegative D*tau; no family-size cost or occupancy independence is introduced. Chebyshev uses the completed variance clause and the exact positive-mean/t>0 domain. The success theorem specializes t=1/2 and enlarges the strict success event to the required non-strict half-mean event. No frozen target is used as a premise of its own proof.

All target definitions and manuscript hashes remain those of the unchanged v1 release. The final three mathematical/representation reviews cover the actual conditional witness, forcing positivity, rare and nonrare regimes, scalar stability and concrete family assembly; their explicit authorship boundaries are preserved.

| Independently inspected source | SHA-256 |
|---|---|
| `RiffleLowerV2/Occupancy/Scales.lean` | `da8854a15548d7cca32c72e6f5cc46cc2c0779e9e55ecc8eb8cb39e67e59f18d` |
| `RiffleLowerV2/Occupancy/CentralScales.lean` | `52507fdb4813d50facf684b19b5a24c14131f0ae4353b84af82b2018fb12c003` |
| `RiffleLowerV2/Occupancy/CentralModel.lean` | `2cbb6194cbd6408e89a8dfe6d541e04cc9701e2604117c2eb2173ca6791bf496` |
| `RiffleLowerV2/Occupancy/Main.lean` | `c66657c99cf84390ab0ff635a92a77afa4ba6f2f6735cc788d91eb3e0a17dac5` |
