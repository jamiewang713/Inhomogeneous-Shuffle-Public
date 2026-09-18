# Independent assumptions audit: finite exponent conversion

This is a pre-code audit of the proposed additive exponent conversion. I reread the permitted TeX at lines 87–145, 445–517, and 1436–1660; the corresponding fixed-column paper definitions and Lemmas 4.8, 4.14–4.15; and the independent-digit paper's exponent definitions and Lemmas 4.12–4.14. I also checked the existing finite factor definitions and proved collision estimates. No Lean code, mathematical source, previous implementation, or frozen review was changed.

**Verdict: the proposed exact conversion is valid if it preserves the actual-cost source definition of c_L, keeps the signed ambient error explicit, and identifies N^c_E with the tail square product rather than the fixed-count collision product.** The finite conversion does not recover the missing −c_F spatial saving. Exact final signatures and a complete declaration inventory still require comparison before a new freeze.

## Source interpretation

The TeX defines legality at lines 445–448 by strict positivity only of the selected count in each prefix column. It permits zero counts in all other piles. The model at lines 94–108 uses deterministic natural counts summing to N and p=n/N. The definition of ψ_p(2) at lines 128–134 uses the sum of squared pile probabilities.

The source c_L at lines 499–506 is literally b minus the sum of actual suffix log-costs after the ambient word w, divided by log N. It is not defined as the logarithm of the exact full-prefix mean. The ambient assumption at lines 492–496 supplies only an asymptotic relation between that mean and N^b. The exact finite discrepancy therefore belongs in a separately defined quantity

ε_w = log(prefixMean(w))/log N − b.

The phrase c_L=log_N E|I(B_x)|+o(1) at line 508 has the correct asymptotic sign because the exact equality is log_N E|I(B_x)|=c_L+ε_w. No hypothesis bounding ε_w is part of this finite addendum.

The fixed-column paper's displayed c_L in (4.11) uses representative probabilities for good profile digits and actual probabilities for exceptional digits; Lemma 4.8 then has a profile approximation error. The present TeX instead uses the actual count for every suffix digit. Importing the older representative-profile c_L would change the requested definition and introduce an additional approximation obligation. The independent-digit paper's whole-deck identity c_L=1+log_N λ_x is exact in that different model; it does not justify replacing the present ambient b by an exact mean exponent.

## Finite data and source domains

Use deterministic natural counts n on K columns and k digits, with the existing column-sum proof hn. Let W be the ambient length and M the extension length, with W≤M≤K. Let w:Fin W→Fin k and x:Fin M→Fin k be deterministic prefixes. The extension hypothesis must identify the same initial coordinates, for example x(Fin.castLE hWM t)=w(t) for every t:Fin W. This is stronger information than a mere length comparison and is essential to the mean factorization.

Assume x is legal: every selected n(Fin.castLE hM t)(x t) is positive. Then legality of w is a proved consequence of the extension relation; it need not be an independent extra hypothesis. Alternatively a public source-level legal-word representation may already contain both legalities, but the proof must not accept positivity of a mean or a desired factorization as a substitute for proving it from the counts.

The finite exponent theorems should explicitly use N≥2. This gives N>0, N>1, log N>0, and a nonzero logarithmic denominator. It is a genuine finite restriction within the source's final N→∞ domain, not an added concentration premise. The previous all-N finite collision theorems stay unchanged. N=0 and N=1 are outside the real logarithm-to-base-N interpretation even if some totalized Lean expressions happen to simplify there.

The source also fixes k≥2 and K=floor(T log N), but neither is needed for these finite algebraic consequences. A separately stated finite conversion may quantify over arbitrary k and K and specialize to the source data. It must be described as such, without claiming to have formalized the profile limit or the full source lemma's stable-block hypotheses. No r, T, retained-pair, good-column, fluctuation, or first-moment-margin assumption is needed for this conversion.

All quotients inside logarithms and products are real quotients of cast counts. Natural-number division would produce a different quantity. All real exponents use real powers of the real cast of N, not natural exponentiation.

## Exact mean identity and its local proof obligations

Write μ_w=prefixMean N n hW w and μ_x=prefixMean N n hM x. Define the source suffix cost over the actual absolute columns after w and through x. In the existing zero-based indexing this is the condition W≤t.val for t:Fin M; it is exactly the source's one-based range W<j≤M. Including the first W columns again, or omitting column W+1, would be an indexing error.

Let C be this suffix log-cost sum and define L=b−C/log N. The identities to prove from the product definitions and extension relation are

log μ_x = log μ_w − C,

log μ_x / log N = L+ε_w,

μ_x = N^(L+ε_w).

Required intermediate facts are genuine consequences, not assumptions: selected pile probabilities are strictly positive; the two prefix masses and means are positive; the prefix product splits into its first W factors and remaining factors; and the first factors coincide with w's factors by the extension relation. The trusted finite logarithm-of-product and real exponential/logarithm identities then apply. Finite products with no factors equal one, so no nonempty-prefix premise is necessary.

The choice of b is an arbitrary real reference exponent in the exact algebra. Neither b nor L nor ε_w must be positive. In particular, legal blocks can have mean below one and hence a negative exact mean exponent. The exact identity must retain c_L as the original suffix-cost expression; defining it as log μ_x/log N−ε_w would make the identity tautological and lose source fidelity.

No factorization conditional on a realized ambient occupancy is involved. μ_w is the unconditional expected ambient occupancy under the existing matrix law, not the realized number of rows in that ambient block. The fixed-count population remains N throughout.

## Exact tail exponent and the necessary inequality

For each tail column j, set s_j=Σ_a (n_j(a)/N)^2 and ψ_j(2)=−log s_j, exactly as in the source. Feasibility and N≥2 imply some pile in that column is positive. Consequently s_j>0. This must be proved from hn; it is not an extra positive-tail hypothesis, and it does not require every pile to be positive. Feasibility also gives s_j≤1, so ψ_j(2)≥0 and the source c_E≤0 if those sign facts are included in the new inventory.

Define E=−(Σ_{M≤j.val<K} ψ_j(2))/log N. Finite logarithm-of-product algebra gives the exact identity

tailSquareFactor N n M = Π_tail s_j = N^E.

The identity is with the existing tailSquareFactor, not tailCollisionFactor. The latter is the probability that two different labels have equal tail strings and contains n_j(a)(n_j(a)−1)/(N(N−1)). It can vanish, whereas each s_j and their product are strictly positive on this domain. For example, one tail column with N=2 and counts (1,1) has tail collision factor zero and square factor 1/2; its E is −1. An exact collision-product=N^E statement would be false even for legal prefixes.

The already proved finite inequality supplies the needed bridge:

0≤tailCollisionFactor≤tailSquareFactor=N^E.

It uses the original population N and the fixed-count law. There is no asymptotic correction, lower bound on pile sizes, or replacement by independent rows. One must not take log of the collision product or assume it is nonzero to simplify the proof.

At M=K the tail is empty, E=0 and both tail products are one. The converse E=0⇒M=K is false: deterministic tail columns also have s_j=1. Thus the general sign statement is E≤0, not E<0 whenever a tail is present.

## Density conversion and the small-prefix consequences

The frozen actual-matrix result C.54 gives

D_x ≤ μ_x^4 q_tail^2/4.

Replace the nonnegative q_tail by the nonnegative square product, use the exact mean and tail identities, and combine real powers. This proves

D_x ≤ N^(4(L+ε_w)+2E)/4.

All exponent equalities must be derived from the trusted real-power identities with N>0. The desired power identity, positivity of the numerical expression, or final density inequality must not be accepted as an assumed interface.

If L<2δ, the two valid direct consequences are

D_x ≤ N^(2E+8δ+4ε_w)/4,

D_x ≤ N^(2L+2E+4δ+4ε_w)/4.

They follow respectively from 4L≤8δ and 4L≤2L+4δ, and monotonicity of real powers at base N≥2. The strict branch premise may yield a non-strict upper bound; it must not silently be changed to a premise about L+ε_w. These algebraic implications hold for arbitrary real δ with the displayed premise. The source chooses δ>0, but a separate nonnegative-δ assumption is not needed to make these finite proofs work. If the final inventory restricts δ to the source regime, that restriction should be stated explicitly before freeze.

The coefficient of the exact error is 4ε_w in both consequences. Replacing it by 2ε_w would require a different smallness condition or an additional sign estimate and is not justified. ε_w can have either sign. One cannot erase it, replace it by o(1), or absorb it into O(δ) without proving a further family-level bound. In particular L<2δ alone need not imply μ_x<N^(2δ) at a fixed N when ε_w>0.

The second consequence supplies the finite exponent form used by the source's small-singleton estimate, and it in fact holds for every legal prefix satisfying that numerical cutoff. It needs no stable-singleton premise or conditional endpoint atoms. The first consequence gives a valid nonspatial small-prefix estimate, but it does not supply the printed −c_F saving in the small non-singleton case. Likewise the unrestricted fourth-power bound does not prove the printed large-block exponent 4L−c_F+2E.

Removing the numerical /4 from these upper bounds is a valid further weakening because N raised to a real exponent is positive. It should nevertheless follow the exact final frozen statements, not be silently changed during implementation.

## Mean bound and terminal interpretation

C.55 and the exact mean identity give the broader valid bound

D_x ≤ N^(L+ε_w)

for every allowed legal prefix. At M=K one separately has E=0, hence this is the terminal exponent bound and may equivalently be written with an added E. Terminality does not require a random tail, a positive expected block size exponent, a small-mean hypothesis, or concentration. No new terminal-pair or stable-family assumption is needed for this finite numerical specialization, although such membership obligations remain if one later restates the full source classification.

As a concrete warning against dropping ε_w at finite N, a fixed first pile of size three with a deterministic continuation has μ_x=3 and two deterministic internal edges. Its ambient exponent may be b=0 in an asymptotic family, since 3=N^(0+o(1)); at finite N the exact error is log_N 3. The exact mean-bound right side is three, whereas replacing ε_w by zero would give one and fail. This example illustrates the need for the explicit error, not a challenge to the source's o(1) notation.

## Complete boundary and coordinate audit

- **N=0/1:** excluded only by the new finite logarithmic domain. All earlier finite collision results retain their all-N statements. No totalized log-at-zero or log-base-one calculation should be presented as the source meaning.
- **W=0:** the ambient mean is N. The source whole-deck choice b=1 gives ε_w=0. With arbitrary b, ε_w=1−b and the algebra remains valid.
- **W=M:** the suffix cost is the empty sum, L=b, and μ_x=μ_w by extension. Thus the exact power identity reduces to its ambient definition.
- **M=0:** W=0 and both words are empty. The source size exponent is b; with the whole-deck convention the exact mean exponent is one. The density remains the existing full-deck density.
- **K=0:** M=W=0 and every row is an empty word. The graph has N−1 deterministic edges, E=0, and the whole-deck mean bound is N. No positive column count is needed.
- **k=0:** if K>0, feasibility contradicts N≥2, so there are no such actual data. If K=0, all empty functions and the law exist for any allowed N. No extra inhabited-alphabet assumption is needed.
- **Zero piles:** unselected zero counts are allowed. A selected zero count violates source legality; its zero mean cannot be represented as a positive-base power with a finite real exponent. The new logarithmic conversion must not pretend to cover those illegal prefixes. Earlier zero-mean finite inequalities still do.
- **Selected pile count one:** legality holds and the mean is positive; the prefix pair factor and density can be zero. No proof requires a selected count at least two.
- **Zero tail collision factor:** allowed, gives density zero by the earlier result, and never obstructs the positive square-product logarithm.
- **All mass in one pile in a tail column:** allowed; its ψ contribution is zero. Nonempty tails can have E=0.
- **Negative b, L, E, or ε_w:** real-power formulas remain meaningful. E≤0 is derived when relevant; no unproved sign is needed for ε_w. A tiny legal mean is not an exceptional case to discard.
- **Exceptional source digits:** every selected positive count is included literally in the logarithmic sum. There is no good-digit threshold, truncation, or lost last digit in these identities.
- **Actual versus relative coordinates:** the proposed D_x is the existing squared density at absolute sorted-deck positions. The mean and collision counts are unchanged by a translation of an ambient block, but squared density and expected overlap need not be unchanged by separate sample-dependent recentering. No equality between those densities is proved here.
- **Conditioning and random prefixes:** the ambient and extension words and count array are fixed deterministic inputs. The theorem does not replace the matrix law by an exploration-conditioned law, condition on the realized ambient occupancy, or admit an adaptively selected prefix without a separately proved bridge. The exact error is deterministic for the stated data.

The same numerical upper bound could later be proved for a separately defined relative-coordinate edge set by proving preservation of its edge count and applying the generic sum-of-squares bound there. That would be a new reviewed bridge; it is not an identity supplied by this addendum. The absolute-coordinate density also has the already frozen independent-copy overlap interpretation, with the same coordinate in both copies.

## Dependency and acceptance boundary

The acyclic route is: source legality and extension → positive means and literal prefix product/log split → exact ambient-error mean identity; feasibility → positive square sums → exact source tail exponent identity; existing collision≤square and C.54 → the fourth-power exponent bound; real-power monotonicity → both small-prefix consequences; existing C.55 and the mean identity → the mean exponent bound; empty tail → terminal E=0.

None of those dependencies needs concentration, stable localization, an asymptotic profile approximation, a new axiom, or an assumed law identity. All positivity and power identities used by the route have been identified as proof obligations. The proposed finite semantics are accepted subject to the exact declaration/signature comparison. This acceptance does not alter any previous frozen statement, equate source c_L with an exact mean exponent, or claim completion of the source's blocked spatial estimates.

## Final-signature comparison and acceptance

I have compared the complete `exponent_contract_statements.md`, including all five definition bodies and every X.01–X.15 parameter list and conclusion, with this independent audit and the complete `exponent_contract_reconstruction.md`. **I accept the selected X.D01–X.D05 and X.01–X.15 exactly as specified, with no remaining pre-freeze correction.** No Lean code was written during this review.

- **X.D01–X.D05:** legality uses precisely the positive selected actual counts and has no population or feasibility input. The ambient size exponent keeps the literal actual suffix costs on the correct zero-based interval; its b is not replaced by an exact mean. The error is exactly log μ_w/log N−b. The column ψ definition and the two minus signs in the tail exponent yield the logarithm of the square-product tail with the correct sign. Their total Lean definitions do not claim a source logarithmic interpretation outside the domains of the later theorems.
- **X.01–X.05:** the pointwise extension hypothesis supplies the missing mathematical relation between w and x, and X.01 derives ambient legality rather than assuming it separately. The omission of hn from these pure positivity and logarithmic identities is valid: selected-count positivity and N≥2 suffice. X.03 proves the complete logarithmic prefix formula, X.04 derives the suffix difference by a finite split, and X.05 then proves the exact power identity. No mean ratio, desired power identity, positive mean, or nonzero logarithmic denominator is supplied as a new assumption. The argument orders and the derived ambient length proof are consistent, including empty and equal-length prefixes.
- **X.06–X.08:** feasibility and N≥2 correctly derive a positive column square sum even with zero piles. The tail identity needs no prefix legality and is valid for arbitrary natural M; M≥K simply selects an empty tail. The actual fixed-count factor is only bounded above by this square product. No positive collision-factor premise, extra nonempty alphabet premise, strict sign assertion for E, or hidden assumption M≤K appears.
- **X.09–X.12:** all actual-matrix statements retain precisely the feasible count array, legal deterministic prefix extension, original population N, arbitrary real b, and N≥2. The unrestricted bound has exponent 4(L+ε)+2E and coefficient 1/4. The small bounds use the source condition L<2δ, with arbitrary real δ, and retain respectively 2E+8δ+4ε and 2L+2E+4δ+4ε. The general mean bound retains L+ε. No sign on δ or ε, asymptotic error control, classification of stable families, or endpoint-spread premise is needed or inserted.
- **X.13–X.15:** the terminal exponent's zero value is a pure empty-sum identity and legitimately omits hn and hN for its all-N total-real statement. X.14 is exactly X.12 specialized to a full-length prefix with the same source ambient exponent and error; proof irrelevance handles the derived versus displayed ambient length proof without a new premise. Together with X.13 it covers the finite terminal exponent case. X.15 fixes the source whole-deck convention b=1 and proves the empty-root error is zero, requiring only N≥2 and no feasibility or legality premise.

The reconstruction's earlier proposed fourteen-item decomposition and the selected fifteen-item decomposition have the same mathematical content needed here. The selected inventory makes derived ambient legality and the full-prefix logarithmic identity explicit; it leaves finite product splitting and the intermediate equality L+ε=log μ_x/log N as local proved steps; it includes an explicit terminal density specialization and selects the b=1 root normalization. These are pre-freeze decomposition choices, not new hypotheses or changes to a previously frozen theorem. The selected fifteen statements require no extra named helper.

I accept the four-module allocation in the exact report: five definitions in `Exponent/Model.lean`; X.01–05 and X.15 in `Exponent/Mean.lean`; X.06–08 and X.13 in `Exponent/Tail.lean`; X.09–12 and X.14 in `Exponent/Estimates.lean`. The dependency graph is acyclic and uses only already proved matrix estimates plus proved finite-logarithm and real-power steps. The resulting bounds retain their explicit absolute-coordinate scope and do not infer a recentering, conditioning, profile-limit, or spatial-localization theorem.
