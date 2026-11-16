# Exact stable/numerical bridge: adversarial interface review

Reviewed `audit/STABLE_NUMERICAL_BRIDGE_STATEMENTS.md`, SHA-256 `05f5f072fb6d7061e85f4167dbe9566f6a3648a3729422f29b6e761a9ccb2138`, against the actual Riffle and TimeProfile definitions and the authorized article's ambient, side-piece, and stable-family passages. This review writes no Lean code and changes no candidate or frozen contract.

**Verdict:** approve the exact four definitions and SN1–SN16 in the candidate with the SHA-256 above. No missing scientific hypothesis or counterexample was found. The explicit model annotation in SN6, discussed below, is present in the final candidate; no remaining correction to a binder, assumption, or conclusion is requested.

## Definition inventory

| Interface | Verdict | Adversarial check |
|---|---|---|
| D1 `asCuts` | Approve | Only valid finite column and alphabet indices are read. `D.sum_counts` provides exactly the required total; no assumption about out-of-range `D.n` is needed. |
| D2 `asProfile` | Approve | Uses the given counts and `D.N`. Positivity follows from the model. Different proof witnesses of positivity cause no mathematical distinction. |
| D3 `legalVector` | Approve | Legal digits are copied exactly through the list length. The padding digit zero is alphabet-valid because `D.k≥2`; its pile may have zero mass. Only prefix legality is asserted, so that possibility causes no missing hypothesis. |
| D4 `sideProbability` | Approve | This is the literal left/right side probability sum. There is no altered endpoint convention or new side-mass model. |

For clarity, an invalid stronger variant of D3 would claim full-horizon legality of every padded vector. Take two columns, with the second assigning zero mass to digit zero, and a legal prefix of length one. Padding produces a zero-mass final digit. None of the proposed interfaces makes this invalid claim.

## Per-theorem decisions

| Interface | Verdict | Required reasoning and edge cases |
|---|---|---|
| SN1 `asProfile_prob` | Approve | NNReal coercion preserves the natural-count quotient. Its denominator is the same model `N` on both sides. |
| SN2 `legalVector_digit` | Approve | The strict length premise chooses the actual-digit branch. No claim is made beyond the list. |
| SN3 `legalVector_legal` | Approve | `hx` gives positive selected pile count below `x.length`, and SN1 plus positive `N` gives positive real probability. Empty prefixes are included. |
| SN4 `cL_prefix_eq` | Approve | Every summand lies below `u.length≤x.length≤K`, so the prefix and vector digit agree. `log(N/n_i)=digitCost(n_i/N)`. If `u.length<A.w.length`, both intervals are empty. An ambient-prefix premise is unnecessary for this literal identity, even if `A.w` is unrelated to `x`. |
| SN5 `cL_parent_eq` | Approve | `parent_prefix` and `parent_length` reduce to SN4. At `x=[]`, natural subtraction gives zero, and both extension sums are empty. The same vector is retained, as required. |
| SN6 `sampleRow_full` | Approve | Every observed sample digit has positive prescribed count by `sample_entry_count_pos`, and `fullList_length` supplies length `K`. This covers `K=0`; the final candidate includes the explicit model annotation below. |
| SN7 `expectedCount_eq_integral` | Approve | The arbitrary-set statement is valid. The sample domain is finite and measurable, and complete row words form a finite partition. It needs neither measurable `E`, a cylinder restriction on `E`, legal-only `E`, nor independence of distinct rows. Detailed check follows. |
| SN8 `expectedCount_cylinder_eq` | Approve | `u<+:x` supplies legality and `u.length≤K`; no ambient relation is needed. On actual sample rows SN6 supplies full legality, and prefix agreement is exactly the `prefixRows` predicate. |
| SN9 `expectedCount_piece_eq` | Approve | `hx`, `hwj`, and `hjx` are precisely the premises needed for `pieceEvent_iff` and the side-count identity. Agreement before `j` makes the ambient prefix automatic. Suffix coordinates after `j` must remain unrestricted. The final coordinate `j=K-1` is allowed. |
| SN10 `sideMaximum_eq` | Approve | `v<+:x` supplies the necessary upper bound `v.length≤K`. Reindex the same half-open interval and its nonnegative values. If `v.length≤A.w.length`, both suprema are zero. If larger, the word relations supply the needed ambient prefix of `v`. No extra prefix or positivity premise is required. |
| SN11 `cFAt_eq` | Approve | SN10 identifies both square roots; the two extended-log definitions have the same zero-to-bottom convention and denominator. Valid for zero or empty side maxima. |
| SN12 `cF_eq` | Approve | Raw-pair compatibility makes the join a legal ambient descendant. `hx` then gives the ambient descent needed for SN11, while `cFAt_continuation` identifies the Riffle exponent. Terminal pairs, including bottom, remain covered. |
| SN13 `rawPair_crossings` | Approve | Nonterminality gives two genuine last-coordinate crossings after the ambient prefix. Their coordinates lie in `[A.w.length,join.length)`. Each side sum contains the extreme large-pile digit with mass at least `A.chi`. No `LocalGood`, admissibility-budget, retained, or finite-exponent assumption is required. |
| SN14 `stop_stableAt` | Approve | The finite exponent equality and strict source Stop give `cL-F<delta`; SN4 transfers the cost, and strict-to-weak implication yields the proposed `StableAt`. The theorem does not replace the source stop rule or claim a converse. |
| SN15 `gamma_parentCrossing` | Approve | `gamma_first_crossing hp hroot hx` gives `join.length<x.length`, hence `0<x.length` and `join.length≤x.length-1`, plus parent non-Stop. `hx.1.1.1` really is the legal-word field of Gamma's nested `pairDesc` membership. SN5 and `not_stop_iff_sub_ge` give the final inequality. No extra nonterminal premise is needed. |
| SN16 `ambientApproximation_iff` | Approve | SN8 at `u=A.w` and the definition of `logScale` give a literal equivalence. It assumes neither the approximation nor signs of `er,eb`. The right side is independent of the continuation, and `A.b` is unchanged. |

### SN6 model annotation

The final candidate uses

```lean
Riffle.Full D (Riffle.fullList (D := D) (TimeProfile.sampleRow sample i))
```

in the SN6 signature. `fullList` has an implicit argument of type `Riffle.Model`, whereas `sampleRow sample i` has the expanded type `Fin D.K → Fin D.k`. Its dimensions alone do not uniquely determine the entire model. The explicit annotation, also used in SN7, avoids dependence on elaborator recovery through the `K`/`k` projections. This is a type-inference clarification only, not a new premise or changed mathematical theorem. I verified its presence in the final candidate. I have not run a mixed-toolchain signature compilation in this no-code pre-freeze review.

## General-set expectation identity: detailed check

For any fixed sample, each labelled row has exactly one complete vector `omega : Fin D.K → Fin D.k`. Consequently its `E`-row count is the finite sum over all such vectors of

`if fullList omega ∈ E then card(boxRows (fun j => {omega j}) sample) else 0`.

Integrate this finite identity. `fixedCount_integrable` supplies integrability of every summand on the finite sample domain, so the finite sum can be interchanged with the integral. `expected_box_count` gives each singleton-coordinate box expectation as

`D.N * ∏ j, TimeProfile.prob (asProfile D j) (omega j)`.

SN1 turns this into the real coercion of the Riffle product weight. Distributing `D.N` and coercing finite sums/conditionals yields exactly the existing `Riffle.expectedCount`, which is the left side of SN7. No unsupported iid-row assumption occurs: only the already-proved one-row product marginal and linearity are used.

This argument works for `E` containing non-full lists, out-of-alphabet words, or illegal full alphabet words. The first two are absent from the `fullList` range. The last have zero product weight and cannot occur as sampled rows. Taking `E` to be an arbitrary infinite set of lists poses no measurability problem: only its pullback to a finite sample domain is integrated. At `K=0` there is one empty word, and both sides are `N` or zero according to whether it belongs to `E`.

The stronger assertion “every raw alphabet-valued vector is a legal sample row” would be false when some piles are zero. The proposal correctly uses SN6 only for actual sampled rows. The finite partition identity itself needs no such legal-word assertion.

## Branch and boundary stress tests

1. **Terminal fallback with one zero side.** With one uniform binary column, empty ambient prefix and `y=z=[0]`, the left boundary uses fallback, the right crosses at the final coordinate, and the pair is terminal. The left maximum is zero and `cF=⊥`. SN12 still holds; SN13 correctly cannot be applied. Thus its nonterminal hypothesis must remain.

2. **Genuine crossing at the terminal coordinate.** With one uniform ternary column and `y=z=[1]`, both boundaries genuinely cross at `K`. SN9–SN12 include the coordinate `K-1`; terminality does not erase it. This is still the source singleton branch, so no full-horizon nonterminal assumption is needed.

3. **Gamma at a stopped root.** For `N=9,K=2`, uniform ternary columns, `w=[]`, `b=1`, `chi=0.1`, `delta=0.3`, and `y=z=x=[1]`, one has `cF=1/4`, `cL(x)=1/2`, and `cL(parent x)=1`. Hence `x∈Gamma`, but it is the join itself and fails the length clause of `ParentCrossing`. The proposed SN15 correctly retains `hroot`, excluding this case. Source stable membership then uses its stopped-root singleton branch.

4. **Equality at the stop threshold.** In the same uniform setup with `delta=1/4`, `x=[1]` satisfies the relaxed `StableAt` inequality at equality but does not Stop. SN14 is only the valid forward implication.

5. **Empty/ambient-terminal inputs.** At `K=0`, legal lists and joins are empty; SN4–SN12 and SN16 have their empty-product/sum/supremum values. SN13's nonterminal premise and SN15's root-not-stopped Gamma premises cannot hold. If `A.w.length=K>0`, every legal ambient continuation equals `A.w`; the extended comparisons still allow bottom. No additional positivity of `K` or strict ambient-length bound is justified.

6. **Free ambient exponent.** Empty ambient prefix has exact expected exponent one, but Setup allows arbitrary `b`. SN16 retains `abs(1-b)≤eb` rather than erasing it. None of SN1–SN16 supplies or assumes the analytic smallness of `eb`, the horizon equality, or a variational margin.

## Scope of approval

The candidate correctly separates finite representation identities from the later source horizon, analytic error budgets, and profile normalization. The arbitrary general set in SN7 is not a hidden conditional ambient law: its measure remains the exact unconditional `fixedCountMeasure (asCuts D)` printed in the interface. The side maxima remain maxima of unconditional expectations. These identities do not supply conditional hypergeometric variance, anti-concentration, localization, or the disputed large-block density theorem.

I approve the exact final four-definition/sixteen-theorem candidate, SHA-256 `05f5f072fb6d7061e85f4167dbe9566f6a3648a3729422f29b6e761a9ccb2138`, without any remaining change to its assumptions or conclusions.
