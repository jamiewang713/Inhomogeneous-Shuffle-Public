# Independent final review of the asymptotic implementation

I independently read the complete frozen asymptotic contract, the three current `Asymptotic` Lean files, every elaborated signature, the logical-dependency output, and the build log. I compared each definition, parameter, conclusion, and actual proof with the selected A.D01 and A.01–07 inventory. This review accepts the implementation verified at **2026-09-17 22:47:36 UTC**. No implementation, source, or frozen artifact was edited during the audit.

## Verification and checked snapshot

`verify_asymptotic.py` passed for exactly seven indexed theorem declarations and the one definition `EdgeLocalization.HasSizeExponent`, in exactly the three planned modules. The build uses Lean 4.24.0 and the project's pinned mathlib revision `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. Every new declaration has only `propext`, `Classical.choice`, and `Quot.sound` among its logical dependencies. No prohibited proof token or additional named helper occurs.

The verifier confirmed that the asymptotic contract and index, all four pre-code review reports, six earlier contracts, twenty-five parent implementation modules, and the three permitted mathematical sources retain their frozen hashes. The asymptotic frozen contract remains SHA-256 `659ee8a94a40e3c4cd7b607409d42297f0d0d41fe41c6414d9a3d9ca30aff8a8`.

The actual source snapshot checked before and after verification is:

| File | SHA-256 |
| --- | --- |
| `EdgeLocalization/Asymptotic/Model.lean` | `920def79ccd1b8d88d233f1bd7b814358543353eed1440634358a77b3eec0b66` |
| `EdgeLocalization/Asymptotic/Error.lean` | `0f119e3a9896944719fcd5c717bb9466c4fd30c7ceed5d9c1a97f4565a03533d` |
| `EdgeLocalization/Asymptotic/Estimates.lean` | `0b1db2065de328d80b16e4cb7bac2446da31a658d05f0c857a494ff89186a0fe` |

The complete evidence is recorded in `asymptotic_verification.json`, `asymptotic_build.log`, `asymptotic_signatures.log`, and `asymptotic_logical_dependencies.log`. I checked the literal source proof arguments as well as the printed signatures, since the ordinary pretty printer suppresses some equality and bound proof terms.

The build succeeds at default limits, with twelve unused-variable linter warnings for `hprefix`, `hx`, and `hsmall` named inside the five frozen universally quantified conclusions. The subsequent proposition does not refer to those proof variables by name, so the linter reports them. Their propositions remain explicit premises in the elaborated types; the theorem proofs introduce and use them when applying the finite bounds and scalar small-cutoff comparison. These are not unused mathematical assumptions or proof gaps. The frozen binders were not removed, renamed, or suppressed to hide the warnings.

## Definition and common family audit

**A.D01 `HasSizeExponent`** is exactly the frozen proposition

`∀ ε > 0, ∃ N0, ∀ N ≥ N0, N^(b-ε) ≤ f N ∧ f N ≤ N^(b+ε)`,

with `f : ℕ → ℝ`, `b : ℝ`, and real powers of the real cast of `N`. It contains neither an assumed logarithmic error bound nor a global positivity condition. The lower and upper sandwiches are both present. The definition itself imposes no artificial `N≥2` restriction and may discard a finite initial segment through its existential threshold.

All six family theorems retain the exact explicit parameter order `k, K, A, n, hn, hA, w, b, hsize, ε, hε`. The dependent count array and ambient word are indexed by the actual natural population; `hn` requires column sums equal to that same population for every `N`. The family length proof is `A N≤K N` for every `N`. No additional typeclass, global ambient legality, positive-size, good-column, limit-rate, or bounded-length premise appears.

In every family statement, `hsize` is applied literally to the **actual expected sorted occupancy** under `matrixLaw (n N) (hn N)`, with the already defined occupancy count and ambient prefix word. It is not silently changed into a premise about `prefixMean`, a realized count, or a conditional law. The existing exact expectation identity is used only inside the proof of A.02.

## Error statements and proof bodies

**A.01 `hasSizeExponent_eventually_log_error_le`** has the frozen generic scalar domain and concludes an existential cutoff `N0≥2` with `|log(f N)/log N-b|≤ε` for every `N≥N0`. The proof takes the sandwich at the supplied positive accuracy and explicitly chooses `max N1 2`. It separately proves the natural and real base bounds, positivity of `log N`, positivity of the lower power, and then positivity of `f N` from the lower sandwich. Thus the proof never assumes that `log(f N)` is nonnegative or that every initial `f N` is positive.

It applies trusted logarithm monotonicity to each sandwich inequality and the positive-base logarithm-of-real-power identity. Both division steps use the locally proved positive denominator. The resulting upper and lower bounds yield the frozen absolute-value estimate. Every sign and denominator condition is proved; no additional named analytic lemma or asymptotic interface is introduced.

**A.02 `ambientMeanError_eventually_abs_le`** applies A.01 to the exact actual expected-occupancy function from `hsize`. At each population beyond the returned cutoff, it rewrites that expectation using the previously proved `matrix_expected_sorted_occupancy` with the original count data, feasibility proof, ambient length proof, and ambient word. The result is definitionally the existing `ambientMeanError` bound. The proof does not assume a mean-power equality or infer an unproved independence law. It retains A.01's cutoff and therefore proves `N0≥2` as stated.

These two statements establish eventual control of the computed error from the source size condition. They do not encode that desired control as an extra hypothesis or a field of a family structure.

## Uniform density statements and proof bodies

The five density theorems retain the exact existing relative-density function, original full-population law, sorted rows, and samplewise shift

`fun ω => ambientLeft N (sortedRows (n N) ω) (prefixWord (w N))`.

Their quantified domain is precisely the frozen one. A.03 and A.06 choose `N0≥2` before quantifying `N`, `M`, `hM`, `hAM`, `x`, `hprefix`, and `hx`. A.04 and A.05 choose it before `N` and then before the unrestricted real `δ` and all those child data, followed by `hsmall`. A.07 chooses it before the population and every full-length legal extension. There is no `δ` in the hypotheses before the existential cutoff. The printed elaborated signatures independently confirm this order.

Write `L` and `E` only as display abbreviations for the existing size and tail exponents of the child. The accepted inequalities and actual proofs are:

| Item | Frozen conclusion | Proof review |
| --- | --- | --- |
| A.03 `matrix_relative_density_eventually_le_ambient_tail_exponent` | `Drel ≤ N^(4L+2E+ε)/4` | It obtains A.02 at accuracy `ε/4` **before introducing any child**, proves that accuracy positive, and retains its threshold. The upper side of the absolute error bound controls the signed error. Existing R.14 gives the finite exponent, and local real arithmetic plus trusted power monotonicity absorbs `4*error` into `ε`, retaining `/4`. |
| A.04 `matrix_relative_density_eventually_le_small_coarse_exponent` | `Drel ≤ N^(2E+8δ+ε)/4` when `L<2δ` | It obtains the A.03 threshold before introducing `N`, `δ`, or the child. The strict frozen cutoff implies the required exponent comparison `4L≤8δ`; power monotonicity supplies the displayed estimate. There is no new child-dependent or `δ`-dependent threshold. |
| A.05 `matrix_relative_density_eventually_le_small_singleton_exponent` | `Drel ≤ N^(2L+2E+4δ+ε)/4` when `L<2δ` | It retains the A.03 threshold in the same order. The scalar implication `4L≤2L+4δ` proves the conclusion. No singleton-family, stability, or endpoint hypothesis has been added. |
| A.06 `matrix_relative_density_eventually_le_ambient_size_exponent` | `Drel ≤ N^(L+ε)` | It obtains A.02 at accuracy `ε` before introducing every child, then applies existing R.17 and the upper side of the signed-error bound. It has no smallness premise, extra tail term, or denominator. |
| A.07 `matrix_relative_density_eventually_terminal_exponent` | `Drel ≤ N^(L+ε)` for full-length legal children | It specializes the already obtained A.06 uniform bound to `M=K N`, `hM=Nat.le_refl (K N)`, and `hAM=hA N`. It adds no small-mean or singleton premise and declares no new terminal helper. |

In A.03 and A.06, the finite bound writes the error with the child-derived proof `hAM.trans hM`, while A.02 uses `hA N`. These proofs establish the same natural inequality and are identified by Lean's proof irrelevance. There is no extra equality premise, no child-dependent error, and no change in the ambient word.

Both small proofs use the unchanged strict cutoff on `L`, without adding the ambient error inside that cutoff. All powers use base `N` and the already defined absolute-column tail exponent. Neither the source size exponent nor its error is redefined during absorption. The arbitrary sign of `b`, `δ`, the error, and the child exponent is preserved; only the requested accuracy is assumed positive.

## Boundary and scope review

- **Initial populations:** generic scalar values at zero and one, and arbitrary finite initial failures of positivity, remain allowed. A.01 explicitly enlarges its threshold before applying useful logarithmic inequalities. The family count laws are still required as data at every population, but no new asymptotic estimate is asserted for an initial segment.
- **Zero expected ambient size:** infinitely many zero values at unbounded populations are incompatible with the lower sandwich; eventual positivity is therefore derived. No global ambient-legality hypothesis is added. Each child density theorem retains exactly its existing child-legality premise.
- **Empty alphabet, columns, or prefix:** the existing count-feasibility and word types determine which finite data exist. No additional inhabitance assumption is used. Empty-column and root cases remain in the domain; zero unselected counts and zero tail collision factors are not excluded.
- **Negative exponents:** neither a negative `b` nor a mean below one invalidates A.01. The proof needs positivity of the mean, not positivity of its logarithm. The denominator `log N` is independently proved positive after the cutoff.
- **Uniformity:** the proof and elaborated statement both choose the cutoff before all children and, in the two small theorems, before `δ`. A finite count or union bound over prefixes is not used. No common cutoff across unrelated ambient families, changing retained-class collections, or exploration histories is asserted.
- **Terminality:** the terminal word has exactly length `K N` and uses the reflexive length proof and supplied ambient extension map. The first-moment bound is sufficient; the earlier zero tail exponent remains true without being a new premise or helper.
- **Coordinates and probability:** the original full-population law and actual ambient-relative shift remain unchanged. No random-population law, conditioning on a nonempty ambient event, equality between relative and absolute densities, or spatial smoothing estimate occurs.

The current implementation completes exactly this additive scalar asymptotic dependency. It does not complete the original goal's stable-family classification, concentration, per-edge localization, endpoint windows, negative-`c_F` gain, entropy aggregation, or exploration-conditioned argument. The seven conclusions follow from the previously proved finite estimates and the source's actual expected-size asymptotic; no stronger source assertion was substituted or marked proved.
