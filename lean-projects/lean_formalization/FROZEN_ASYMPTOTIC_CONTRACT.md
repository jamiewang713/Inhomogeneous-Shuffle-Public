# Frozen ordered-limit consequences of the frozen tails and counts

All three independent reviews have been compared, and this batch is frozen before implementation. Mathematical sources remain the three authorized files. No F/S/T statement or source definition may be changed.

Write L(N)=Real.log (N:Real), ell(chi)=Real.log(1/chi), and alpha(chi)=1/Real.sqrt(ell(chi)). All powers with real exponents below are Real.rpow. h_b=floor((C/ell(chi))*L(N)) and h_e=floor(alpha(chi)*L(N)) use natural floors. K and N are natural numbers. The bound K≤T*L(N) casts K to Real; it follows for the source horizonDepth when T≥0 and N≥2.

## A01: finite exponential form of the weighted upper tail

For N≥2, T≥0, K≤T*L(N), a≥0, beta≥0, and z≥1,

N*tailWeight K (floor(beta*L(N))+1) a
  ≤ N^(1 + T*log(1+a*z) - beta*log z).

This follows from frozen tailWeight_le, positivity, natural floor+1, and exact exp/log identities. Include the z=1, a=0, beta=0 and K=0 cases. Do not assume a probability interpretation or a≤1.

## A02: finite exponential form of the lower pattern count

For N≥2, T≥0, K≤T*L(N), beta≥0, k:Nat, and 0<z≤1,

(lowCount K (floor(beta*L(N))) k : Real)
  ≤ N^(T*log(1+(k:Real)*z) - beta*log z).

This uses the reversed power monotonicity for z≤1 and floor(beta*L)≤beta*L. The existing frozen lowCount and sparse labels remain unchanged.

## A03: exact leading exponent for admissibility tails

For every natural k, real T≥0, real C>0, and epsilon>0, there exists chi0 with 0<chi0<1 such that for every 0<chi<chi0, every N≥2 and K≤T*L(N),

N*tailWeight K (h_b+1) ((k:Real)*chi)
  ≤ N^(1-C+epsilon).

The choice of chi precedes N and the statement is uniform over all finite K satisfying the displayed bound. A proof may choose z=exp((1-delta)*ell(chi)) with a fixed delta in (0,1), then bound log(1+x)≤x and use chi^delta→0. Delta is a proof choice, not an added premise. The quantitative expression 1-C is retained.

## A04: arbitrary negative powers for exceptional tails

For every natural k, real T≥0, and real target C0, there exists chi0 with 0<chi0<1 such that for every 0<chi<chi0, every N≥2 and K≤T*L(N),

N*tailWeight K (h_e+1) ((k:Real)*(3*chi)) ≤ N^(-C0).

The source allowance is exactly alpha(chi)=1/sqrt(log(1/chi)), and the finite regularity factor remains exactly 3*chi. No extra o(1) term is inserted. A proof may choose z=exp(ell(chi)/2), use alpha(chi)*ell(chi)=sqrt(ell(chi)), and let the negative square-root term dominate. This theorem includes the N factor.

## A05: descriptor count with the source order of choices

For every k≥2, T≥0, C>0 and epsilon>0, there exists chi0 with 0<chi0<min(1,1/k) such that for every 0<chi<chi0 and every natural d, there exists N0≥2 for which all N≥N0 and K≤T*L(N) satisfy

(k^2*(K+1)^(d+2)*(lowCount K h_b k)^2*lowCount K h_e k : Real)
  ≤ N^epsilon.

The good-count dimension d is chosen after chi and before N0. Thus a partition and time mesh of any finite size may depend on chi, but cannot grow with N inside this theorem. The source boundary constant C is fixed before chi. Use A02 with z tending to zero and beta*log(1/beta)→0; the polynomial factor in K is absorbed only after d has been fixed. k=2, T=0, K=0 and h_b or h_e greater than K must remain covered.

## A06: actual finite-matrix row consequences

Apply A03 to the unchanged actual boundary union bound T09: for every k≥2, T≥0, and real C0, there exists a C>0 and chi0>0 such that every existing Model D with D.k=k, D.N≥2 and D.K≤T*log(D.N), and every existing Setup A with A.C=C and 0<A.chi<chi0, have expected number of rows in the union of the two discarded boundary events at most D.N^(-C0). The two-side factor is absorbed by a spare power of N using N≥2; it is not dropped.

For every k≥2, T≥0, and real C0, A04 supplies chi0 with 0<chi0<1. For every 0<chi<chi0, every existing Model D with D.k=k and (D.K:Real)≤T*log(D.N:Real), every real Creg and partition P with P.IsRegular chi Creg, and arbitrary v,M : FullIndex D→Nat, apply unchanged T09 to the exceptional-prefix event with allowance alpha(chi) and modelColumnProfile D. Its expected number of rows is at most D.N^(-C0). D.N≥2 follows from Model; it is not an extra premise. These are bounds on row cardinalities under the existing fixedMatrixLaw. A sorted-edge comparison remains a distinct obligation.

Every proof helper must be one of the exp/log, floor, monotonicity, parameter-limit, finite-factor, or uniform substitution steps explicitly reviewed for these statements. No positivity of individual pile counts, time measurability, independent-row law, or N-dependent partition may be introduced.

## Frozen exact helper and representation appendix

The three independent review reports identified in ASYMPTOTIC_FREEZE_SHA256.json are part of this statement freeze, including their exact mathematical helper schemas. The helper catalogue may be implemented as private lemmas or inlined. Helpers are derived only from their explicitly reviewed local domains and trusted mathlib results. They may not be inserted as additional assumptions in A01–A06.

Use TimeProfile.logScale N as L(N), which is definitionally Real.log(N:Real). Shared scalar definitions are `RiffleProfiles.chiLog chi := Real.log(1/chi)` and `RiffleProfiles.exceptionalAllowance chi := 1/Real.sqrt(chiLog chi)`. The boundary and exceptional natural thresholds are the exact floors written above. The common error exponent may be named `countErrorExponent k T C u := 3*T*(k:Real)/sqrt(u) + C*log(u)/u + log(u)/(2*sqrt(u))`.

For cross-module use, the shared cutoff helper may be stated as: for cap>0 and any real U there exists chi0 with 0<chi0<min(1,cap) such that every 0<chi<chi0 has max(1,U)≤chiLog(chi). This is precisely the stronger nonnegative-scale cutoff already reviewed in the reconstruction and adversarial catalogues and implies the representation report's positive-scale/U bound.

The common-z product helper covers k:Nat, T≥0, C>0, u≥1, N≥2 and K≤T*logScale N. The product `(lowCount K (floor((C/u)*L)) k)^2 * lowCount K (floor((1/sqrt(u))*L)) k`, cast to Real, is at most N raised to the exact E displayed in the reviews and hence at most N raised to countErrorExponent. The cutoff for countErrorExponent is chosen before the good-count dimension d.

The fixed-polynomial helper covers c≥0,T≥0,m:Nat,eta>0 and concludes the uniform N0 bound c*(K+1)^m≤N^eta for N≥N0 and K≤T*log N. No c>0, T>0, k>0 or positive individual pile condition may be added to a statement that does not already contain it. Time measurability and row independence are not part of this batch.

Existing F01–F20, S01–S05, T01–T09 and all source definitions remain unchanged. Any new substantive helper outside these compared schemas requires another three-role review and freeze before implementation.
