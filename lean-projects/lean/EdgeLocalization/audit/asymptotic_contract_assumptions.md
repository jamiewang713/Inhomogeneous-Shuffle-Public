# Independent assumptions audit: asymptotic ambient error

This is a pre-code audit. I reread the permitted TeX at 474–517, 1486–1518, and 1594–1660, the older fixed-column expected-size comparison in Lemma 4.8, and the independent-digit exponent definitions. I checked the already proved exact expected sorted occupancy and relative exponent bounds. No earlier source, implementation, frozen file, or report was changed, and no Lean code was written.

**Verdict: the proposed size-exponent hypothesis supplies exactly the eventual control of the computed ambient error needed by the five relative bounds.** Positivity is a consequence after a proved threshold, not a new global premise. The threshold can be chosen before every child length, word, and associated proof. Exact final signatures still require comparison before a new freeze.

## Source hypothesis and definition

The source ambient condition is E|I(B_w)|=N^(b+o(1)), with the final limit N→∞ after fixing the earlier parameters. The source c_L remains b minus the actual extension log-costs; the already proved exact discrepancy is ε_w(N)=log_N μ_w(N)−b. The new addendum should control that computed discrepancy from the source condition, not assume that the desired discrepancy or density bound is already small.

The proposed single definition

HasSizeExponent f b := ∀ ε>0, ∃ N₀, ∀ N≥N₀,
  N^(b−ε)≤f(N) ∧ f(N)≤N^(b+ε)

is a correct two-sided finite-threshold interpretation of this source notation for a real-valued f and fixed real b. Every power is a real power of the real cast of N. The definition itself need not restrict N to at least two, because its existential threshold can be enlarged in the proof. It must not require f to be positive, monotone, bounded by N, or asymptotically nonzero as separate data.

The lower bound matters. A one-sided upper size bound would not give the proposed absolute log-error conclusion. Conversely no exact finite relation f(N)=N^b is inferred: slowly varying positive factors are allowed. Accuracy ε must be strictly positive; ε=0 would demand an eventually exact power law, which does not follow.

## Scalar logarithmic conversion

For each ε>0, obtain the defining sandwich and enlarge its threshold to at least two. For every N beyond that threshold:

1. N>1 and log N>0 are derived.
2. The lower real power is strictly positive, so f(N)>0 follows from the lower sandwich.
3. Apply monotonicity of logarithm to both sandwich inequalities and the trusted positive-base log-of-real-power identity.
4. Divide by the positive log N, obtaining b−ε≤log f(N)/log N≤b+ε.
5. These two inequalities give |log f(N)/log N−b|≤ε.

Using a smaller tolerance such as ε/2 also proves this conclusion, but no assumed convergence interface or rate is needed. Negative b or negative log f(N) is harmless: only the base logarithm used as a denominator must be positive. The proof must not require log f(N)≥0.

A conclusion of the form `∃ N₀, 2≤N₀ ∧ ∀ N≥N₀, |computed error|≤ε` records the domain explicitly and is sufficient. Eventual positivity can be a local proved step; a separate named positivity theorem is not necessary for this inventory.

## Actual family and low-population data

Use an explicit fixed alphabet size k, functions K,A:ℕ→ℕ, actual-N count arrays n(N), the original count-sum proofs for each N and column, proofs A(N)≤K(N), and deterministic ambient words w(N). The source exponent b is a fixed real parameter. The only new asymptotic premise should be HasSizeExponent applied to the actual expected sorted ambient occupancy under `matrixLaw (n N) (hn N)`.

The existing exact expected-occupancy theorem identifies that expectation with `prefixMean N (n N) (hA N) (w N)` for every N, without requiring legality. Rewriting this proved identity transfers the scalar log-error bound to the already defined `ambientMeanError`. No law identity, expected-mean formula, or logarithmic error bound is accepted as a new field.

Global feasibility and length proofs package a family of valid existing finite matrix models; they do not impose a new asymptotic rate. They should not be supplemented by global ambient legality, positive ambient mean, N≥2, nonempty alphabet, or good-column hypotheses. In particular, at N=0 all feasible counts are zero, and a nonempty ambient word may be illegal; at N=1 a word may select a zero pile. Such low-N behavior is allowed. The conclusions start beyond a threshold proved to be at least two.

For a source family specified only eventually, choosing valid arbitrary data at its finitely many missing initial populations gives the required total family without changing the asymptotic content. This is a modeling convention, not a claim that completely invalid supplied count arrays themselves define probability laws. The generic scalar definition allows arbitrary real f before the threshold, including negative or zero values; actual occupancy expectations are nonnegative by the preexisting probability model, but can still be zero initially.

Eventually positive ambient mean also implies ambient legality from the literal prefix product: a zero selected count would make the product and mean zero. This does not require a uniform lower bound on selected counts. The child-bound wrappers already retain legality of x and its extension relation, which separately derive ambient legality via the existing theorem. Thus no public global legality assumption for w is needed. This also rules out an eventual interpretation that is vacuous solely because every ambient word is illegal.

## Uniformity over children

For one fixed ambient family and accuracy ε>0, choose the error threshold using ε/4. The error is a function only of N and the ambient data, so this choice precedes every child variable. At each N≥N₀, quantify over every natural M, length proofs M≤K(N) and A(N)≤M, every x:Fin M→Fin k, the exact coordinate extension relation to w(N), and x's source legality.

The required public quantifier order is therefore

fixed ambient family and accuracy → ∃ N₀ → ∀ N≥N₀ → ∀ child data.

Choosing N₀ after x or after an entire child sequence would provide a weaker, nonuniform claim and would not meet the proposed task. The existence of only finitely many prefixes for a given N is not a substitute for this uniform threshold: that set changes with N. The ambient-only error supplies the uniformity directly, without counting prefixes or using a union bound.

The fixed family length proof hA(N) and a child's derived proof hAM.trans hM may appear differently in the mean-error expression. They prove the same natural inequality and are identified by Lean's proof irrelevance; no equality-of-proof premise or child-dependent ambient error is necessary.

For the two small bounds, δ can be a fixed arbitrary real parameter before the requested accuracy. This allows every δ, including zero and negative values; it adds no δ>0 assumption. The threshold then remains uniformly before every child variable. The proof can in fact choose the same ambient threshold independently of δ, but a separate jointly uniform-in-δ conclusion is not needed unless the exact inventory promises it.

The root subsequently requested explicit threshold uniformity over δ as well. That stronger public statement should quantify δ after the existential N₀. Keeping δ before that existential only states a possibly different threshold for each δ, regardless of whether a particular proof term happens not to use it. This is a pre-freeze signature choice being resolved with the statement designer; the same ambient-error proof supports the stronger order without another hypothesis.

No uniformity across different ambient families follows from one HasSizeExponent premise. A theorem for all retained ambient classes would need either a fixed finite maximum of the individual thresholds or a genuinely joint uniform hypothesis proved for that class. The present proposal should not silently assert such a result, especially when the class itself grows with N.

## Five eventual relative-density bounds

Let L be the existing source ambient size exponent of a child and E its existing tail exponent. The finite relative inequalities already proved give, respectively,

N^(4L+2E+4ε_w)/4,

N^(2E+8δ+4ε_w)/4,

N^(2L+2E+4δ+4ε_w)/4,

N^(L+ε_w),

and the full-length terminal specialization of the last expression.

The absolute error estimate at tolerance ε/4 implies ε_w≤ε/4, hence 4ε_w≤ε. Positive-base power monotonicity then yields exactly the proposed eventual upper bounds

- N^(4L+2E+ε)/4;
- N^(2E+8δ+ε)/4 under the unchanged cutoff L<2δ;
- N^(2L+2E+4δ+ε)/4 under that same cutoff;
- N^(L+ε);
- its terminal full-length specialization, with the already proved E=0.

For the mean bounds, one may use the ambient tolerance ε directly or the same ε/4 threshold, since ε>0. The sign of ε_w is unrestricted: only its proved upper bound is used. Do not replace ε_w by |ε_w| in a definition, silently identify L with the exact log mean, or replace the cutoff by L+ε_w<2δ. The coefficient 1/4 is retained in all three bounds that already have it.

Every child inequality continues to use the actual samplewise ambientLeft shift, the original-N fixed-column law, the same deterministic ambient family, and the already frozen source exponent definitions. No random-pile mixture, residual population, conditioning event, or new coordinate-invariance claim is introduced. The proof is an exact scalar comparison of previously proved bounds, without a probabilistic failure event or concentration estimate.

## Remaining cases and limits

- **Accuracy zero or negative:** outside the new accuracy domain. Nothing supplies an eventually exact zero error.
- **Negative or zero f before the threshold:** allowed by HasSizeExponent. Eventual positivity is proved, never assumed globally.
- **Infinitely many zero/negative values at unbounded N:** incompatible with HasSizeExponent for finite b; the eventual lower power excludes them.
- **Negative size exponent:** allowed. Legal block means can tend to zero while remaining strictly positive; logarithms and real powers remain valid.
- **Empty ambient:** its exact mean is N, and the source b=1 gives the already proved zero error. The theorem need not assume this case separately.
- **A(N)=M:** no extension costs occur. The exact discrepancy still carries the ambient mean correctly before being bounded eventually.
- **M=K(N):** the terminal prefix uses exactly the existing full-length legality and extension domain; no smallness or singleton-family premise is added.
- **K(N)=0:** A(N)=0 and every child length permitted by the bounds is zero. The finite formulas include the deterministic empty-word graph.
- **Empty alphabet:** existing feasibility and word types control which data exist. No alphabet element is chosen from an unproved inhabitance assumption.
- **Zero unselected piles or selected piles of size one:** allowed. Eventual ambient positivity excludes only selected ambient zero counts; child legality retains its original selected-count condition. Tail collision factors may still be zero.
- **Small-cutoff boundary:** equality L=2δ remains outside the strict small case, exactly as in the source and finite contract.
- **Varying child lengths, digits, and exceptional last digits:** all are quantified after the threshold, and their exact costs remain in L. No profile approximation or digit restriction enters this error conversion.
- **All-N source model versus eventual assertion:** validity of each finite law is existing model data; the asymptotic size condition and every resulting estimate apply only eventually. Neither is strengthened to require small error at all N.

The small-singleton-shaped and terminal conclusions now have a precise epsilon-threshold formulation of the source's o(1) contribution from ambient size. They do not prove the stable-family classification, an entropy bound, a sum over classes, the global first moment, or the obstructed −c_F spatial saving. This is a valid bounded extension of the exact finite results, subject to final inventory comparison and a separate freeze.

## Final exact-inventory comparison and acceptance

I have compared the complete `asymptotic_contract_statements.md`, including its updated joint-uniformity signatures, and the complete `asymptotic_contract_reconstruction.md` with this independent audit. **I accept exactly A.D01 and A.01–A.07, with no remaining pre-freeze correction.** No Lean code was written, and no earlier frozen artifact was changed.

- **A.D01:** the one definition is exactly the two-sided real-power sandwich for every positive tolerance, with a tolerance-dependent eventual threshold. It imposes no positivity or sign condition at initial populations and contains no logarithmic-error or density assumption.
- **A.01:** the scalar theorem concludes a threshold at least two and the eventual absolute logarithmic error bound. The lower sandwich proves positive f(N) after that threshold; positivity of the base and its logarithm is derived there. Negative or zero initial values, arbitrary real b, and negative eventual logarithms are correctly allowed. The required positive accuracy is explicit.
- **A.02:** the common family parameters are exactly the explicit actual-N count data, feasibility, ambient lengths and words, b, and the size-exponent condition on the actual expected sorted occupancy. The target is the existing computed ambient error. The proof route uses the already proved occupancy expectation identity rather than assuming a product-mean formula, and adds no ambient legality, eventual-positivity, or nonempty-alphabet premise.
- **A.03:** the threshold is quantified before N and every child length, length proof, word, extension relation, and legality proof. Its exponent is exactly 4L+2E+ε with denominator four and the actual ambientLeft shift. The ambient-only error control at accuracy ε/4 provides the uniform bound, while proof irrelevance identifies the two legitimate ambient length proofs. No child-dependent threshold, large-block assumption, tail sign, or spatial improvement appears.
- **A.04–A.05:** the earlier quantifier issue is resolved in the selected exact signatures. These theorems have only the family and accuracy as parameters, and quantify `∀ δ : ℝ` after the existential threshold and after N's threshold condition, before the child binders. The same threshold therefore works jointly over every real δ and all legal children. Their cutoff remains L<2δ, and the exact exponents are 2E+8δ+ε and 2L+2E+4δ+ε, each divided by four. No sign condition on δ or classification as a stable singleton is added.
- **A.06–A.07:** the general mean bound has exponent L+ε, without a denominator or smallness premise, and its threshold precedes every child. The terminal theorem has exactly a full-length child with the existing reflexive length bound and the ambient extension via hA(N). It is a specialization of A.06, with the previously proved terminal E=0 fact available. It adds no terminal mean, singleton-family, or positive-tail condition.

The data at N=0/1 remain only the existing valid finite model's data. Every useful eventual conclusion explicitly proves its cutoff is at least two, and no low-N legality or nonzero ambient expectation is demanded. The supplied ambient word family may vary with N as specified; the threshold is for that one fixed family. The exact report correctly excludes uniformity over a further class of unrelated ambient families, retained profiles, or exploration histories without another proved uniform statement.

I accept the three-module allocation: `Asymptotic/Model.lean` for A.D01, `Asymptotic/Error.lean` for A.01–A.02, and `Asymptotic/Estimates.lean` for A.03–A.07. The selected seven-theorem dependency graph agrees with the independent reconstruction. All positivity, threshold enlargement, error-coefficient comparisons, and terminal specialization steps fit inside local proofs using the prior project theorems and trusted real logarithm/power facts. No additional named helper, instance, rate assumption, or axiom is needed.
