# Candidate finite contract — not yet frozen

All quantities are finite and real unless specified. No stochastic or integral
theorem is assumed. The purpose is to prove the actual finite estimates behind
the assigned source lemmas; remaining source-to-model bridges stay visible.
Routine local deductions in a proof are not additional assumptions.

## Definitions

- `cost(p) = −log(p)`; it equals `log(1/p)` for positive p.
- `L>0` is the normalization (later `log N`, with N>1).
- A position set is a finite set J. Actual selected masses are p_j, representative
  selected masses q_j. Legality means 0<p_j≤1. For χ>0, good positions are
  `G={j∈J:2χ<q_j}` and exceptional positions are `E=J\G`.
- The regularity predicate states exactly the source digit clauses:
  good implies `χ<p_j` and `|cost(p_j)−cost(q_j)|≤ε`; exceptional implies
  `p_j≤3χ`. In applications ε=Cχ. It imposes no lower bound on exceptional
  representative coordinates and no positivity assumption on unused digits.
- Actual cost of a finite position set is `Σ cost(p_j)/L`; representative good
  cost is `S=Σ_G cost(q_j)/L`; exceptional cost is `Q=Σ_E cost(p_j)/L`;
  `R=|E|/L`. A length exponent is b minus actual cost on the actual extension
  positions. Prefix splitting uses disjoint actual position sets.
- Finite cell replacement has cell indices in a finite type, position-to-cell
  map, representative values v_i, actual values f_j, empirical cell counts
  n_i/L, and arbitrary target cell masses m_i. Its target is Σ_i m_i v_i.
  The error δ_i bounds |n_i/L−m_i|. These are finite data, not secretly
  integrals or assumptions that the desired analytic estimate already holds.
- Finite interval blocking is a union of disjoint whole blocks plus two
  endpoint remainders. Block discrepancies and remainder masses are explicit.
- Prefix mass is a nonnegative multiplier times a product of selected masses.
  Side-cylinder mass at position i is the common earlier mass times the sum
  of permitted side digits, with later digits unrestricted.
- Entropy of nonnegative weights c_i with total C is Σ_{c_i>0} c_i log(C/c_i),
  zero when C=0. Normalized entropy is the case C=1. Cross entropy uses only
  indices where c_i>0. Tilted weights use p_i^θ and their full sum Z.
- `lowCount(K,h,k)=Σ_{q∈{0,…,K},q≤h} choose(K,q) k^q`.
  `tailWeight(K,h,a)=Σ_{q∈{0,…,K},h≤q} choose(K,q) a^q`.
  K,h,k are natural, a≥0. The strict source threshold x is represented by
  the integer h=floor(x)+1; weakening to q≥ceil(x) is explicitly an upper bound.
- A labelled sparse pattern is a subset of K positions with at most h elements
  and a digit from Fin k at each selected position. A coarse pattern forgets
  these labels. A boundary descriptor stores stopping length, the final digit
  (also for terminal fallback, with a fixed default for an empty extension),
  and sparse deviations strictly before that final position. Count arrays have D coordinates,
  each in {0,…,K}. The literal source profile remains coarse.

## Theorems to be reviewed

F01. `cost(p)=log(1/p)` for p>0; `cost(p)≥0` for 0<p≤1;
     `cost(q)≤cost(p)` for 0<p≤q.
F02. The good mass, exceptional mass, and good cost-error clauses follow from
     regularity, with the exact strict inequalities in the definitions.
F03. `|Σ_J f_j−Σ_J g_j|≤Σ_J |f_j−g_j|`; consequently a uniform ε bound
     gives `|Σ_J f_j/L−Σ_J g_j/L|≤|J|ε/L`, L>0.
F04. Exact good/exceptional split, Q≥0, and
     `|actualCost(J)−S−Q|≤|G|ε/L` under F02.
F05. For disjoint prefix and extension position sets, the length exponent
     splits exactly. Together with F04,
     `|cL(x)−cL(v)+S+Q|≤|G|ε/L`.
F06. Finite cell regrouping is exact. If |f_j−v_cell(j)|≤ε and
     |n_i/L−m_i|≤δ_i, then
     `|Σ_J f_j/L−Σ_i m_i v_i|≤|J|ε/L+Σ_i |v_i|δ_i`.
F07. Under explicit additive decompositions of the empirical and target totals,
     blocking discrepancy is at most the sum of whole-block discrepancies
     plus the nonnegative empirical and target masses of the endpoint
     remainders. If target remainder mass≤2ρ, empirical remainder mass≤
     2ρ+2/L, and full-block errors sum≤Tφ+B/L, the result is at most
     `4ρ+Tφ+(B+2)/L`. No continuous measure is postulated in this theorem.
F08. Negating the empirical/target values preserves the F06 error (tail c_E).
F09. Pointwise selected masses≤maximal masses, all selected positive, imply
     `b−Σ cost(selected)/L≤b−Σ cost(maximal)/L`.
     Combining with F06 gives the same one-sided target approximation.
F10. For χ>0 and nonnegative common earlier prefix mass, a side mass at least
     χ times that earlier mass is at least χ times any continuation mass
     obtained by multiplying it by selected factors at the crossing position
     and every later position, all in [0,1]. Prove both left and right
     instances by the same finite lemma.
F11. For L,χ,M,U,V>0 with U,V≥χM,
     `min(log U/(2L),log V/(2L))≥(log M+log χ)/(2L)`.
     This is the exact fluctuation exponent bound; the ambient discrepancy is
     defined as log(M_ambient)/L−b, never assumed to vanish in this lemma.
F12. If Q≥0, |cL_parent−cL_v+S_parent+Q|≤e,
     cL_parent−F≥δ, δ≥0, and S_x≤S_parent+d, then
     `S_x≤cL_v−F+e+d`. These hypotheses are explicit already-derived
     inequalities, not a replacement for proving the parent stopping rule.
F13. For a probability vector a and nonnegative weights w, with w_i>0 on
     support(a) and Σw>0, Gibbs' inequality gives
     `Σ_{a_i>0}a_i log(w_i/a_i)≤log(Σw)`.
F14. For c≥0, p≥0, p_i>0 on support(c), θ>0, and Σp^θ>0,
     `entropy(c)≤θΣ c_i cost(p_i)+(Σc_i)log(Σp_i^θ)`.
     Zero counts are omitted and the zero-total case is proved.
F15. Summing F14 over cells gives the profile entropy inequality. Removing
     exceptional positions from a bounded nonnegative cost 0≤ψ≤M changes
     the normalized sum by at most M|E|/L. Combine with F06 to obtain the
     finite entropy error, retaining every cell-count factor.
F16. For a≥0,z≥1: `tailWeight(K,h,a)≤(1+a*z)^K/z^h`.
F17. For k≥0,0<z≤1: `lowCount(K,h,k)≤(1+k*z)^K/z^h`.
F18. For finite independently weighted words with coordinate probabilities
     summing to one, and each coordinate's bad-digit total mass≤a,
     the mass of words with ≥h bad positions is at most
     `(1+a*(z−1))^K/z^h` for z≥1. A union bound alternative is
     `tailWeight(K,h,a)`; when each bad digit has mass≤χ, use a=kχ.
     Multiplication by N bounds N times this word mass; identifying it with
     shuffle expected row mass is a separate model bridge. A family of edge
     probabilities in [0,1] has sum of squares≤its sum.
F19. The number of labelled sparse patterns is lowCount(K,h,k). The image of
     the map forgetting labels cannot have larger cardinality. For the source
     alphabet k≥2, boundary descriptors have at most
     `k(K+1)lowCount(K,h_b,k)` possibilities. Paired boundaries, labelled
     exceptional data, and D counts have at most
     `k²(K+1)^(D+2)lowCount(K,h_b,k)²lowCount(K,h_e,k)` descriptors.
F20. Partition a finite set of words with fixed good-count array and exceptional
     positions E by their functions E→Fin k. If every labelled fibre has
     cardinality at most B, then the coarse fibre has cardinality at most
     k^|E|·B, including B=0 and empty fibres.
     The unlabelled fibre must not be identified with a single multinomial
     class. A concrete finite counterexample with two exceptional digits
     exhibits different words with identical coarse profiles.

## Not asserted by this finite contract

Theorems equating targets with integrals; construction of a regular measurable
partition; integration against μ_t; the random shuffle model expectation
identity; full asymptotic limit conversions; and the later false coarse-fibre
claim are not assumed or exported as proved. They remain separate obligations.
Freezing finite statements must not be reported as completing the assigned
macroscopic estimates.
