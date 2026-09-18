# Stable-word numerical bridge: frozen supplemental contract

Status: FROZEN at 2026-09-17T22:03:03.160926+00:00. The four definitions and SN1–SN16 below are immutable. Three independent exact-interface reviews were compared before this freeze; no implementation existed. I read the independent algebra reconstruction, the adversarial integration report, the current project Lean declarations, and the authorized unified TeX's ambient exponent, side-piece, and stable-family definitions. The proposed finite interfaces agree with both independent reports.

The finite definitions are compatible. I recommend one adapter contract containing **four definitions and sixteen theorem interfaces**, with proof-local auxiliary reindexings and row-event facts. The actual profile-to-`TimeProfile.profileH` identity should have a separate later contract. This division keeps the present task independent of analytic source inputs, horizon transport, and partition normalization.

Implementation file: `FirstMomentModel/StableNumericalBridge.lean`. Namespace: `InhomogeneousShuffle.FirstMoment.Model`. The statements below use the current `Riffle.Model`, `Riffle.Setup`, and `TimeProfile` definitions unchanged. They can be proved from existing finite project results and trusted mathlib; they do not assert that the mixed-toolchain sources have already been compiled together.

## Four adapter definitions

**D1. `asCuts (D : Riffle.Model) : TimeProfile.Cuts D.k D.N D.K`.** Its count field is exactly

```lean
fun j l => D.n j.val l.val
```

The sum field is proved from `D.sum_counts j.val j.isLt` by `Fin.sum_univ_eq_sum_range`. No count outside the finite column/alphabet range is read.

**D2. `asProfile (D : Riffle.Model) : Fin D.K → TimeProfile.Simplex D.k`.** This is exactly

```lean
(asCuts D).profile (lt_trans Nat.zero_lt_one D.one_lt_N)
```

where positivity is derived from `D.one_lt_N`. This adapter avoids exposing irrelevant proof terms in every later type. It introduces no new profile or probabilistic law: its coordinates are the given pile counts divided by the given `D.N`.

**D3. `legalVector {D : Riffle.Model} (x : Riffle.Word) (hx : Riffle.Legal D x) : Fin D.K → Fin D.k`.** At `j`, its natural digit is `Riffle.digit x j.val` when `j.val < x.length`, with alphabet bound from `hx`; otherwise it is the digit zero, with alphabet bound from `D.two_le_k`.

Only prefix legality through `x.length` will be claimed. The padded suffix is not asserted to have positive pile probabilities. There is no need to select a full legal completion or to change the actual list word. All statements about its parent or other prefixes use this same vector.

**D4. `sideProbability {k : ℕ} (s : Riffle.Side) : TimeProfile.Simplex k → Fin k → ℝ`.** It is `TimeProfile.leftProbability` for `.left` and `TimeProfile.rightProbability` for `.right`.

This is the entire proposed definition inventory. In particular there is no new ambient-data structure, replacement `b`, horizon axiom, list-facing `cE`, or redefinition of the stable family.

## Sixteen precise theorem interfaces

In the following declarations `{D : Riffle.Model}` is implicit unless it is the displayed explicit binder. All facts used to populate structure or vector proof fields are proved, not assumptions. The signatures are proposed interfaces, not declarations with omitted proofs in a Lean source file.

**SN1. `asProfile_prob`**

```lean
(D : Riffle.Model) (j : Fin D.K) (l : Fin D.k) :
  TimeProfile.prob (asProfile D j) l =
    (Riffle.prob D j.val l.val : ℝ)
```

The count-over-`N` form is definitionally available on the left. This statement gives the exact NNReal-to-real comparison needed by side indices and expected counts.

**SN2. `legalVector_digit`**

```lean
(x : Riffle.Word) (hx : Riffle.Legal D x)
(j : Fin D.K) (hj : j.val < x.length) :
  (legalVector x hx j).val = Riffle.digit x j.val
```

**SN3. `legalVector_legal`**

```lean
(x : Riffle.Word) (hx : Riffle.Legal D x) :
  TimeProfile.LegalPrefix (asProfile D) (legalVector x hx) x.length
```

SN2, `Riffle.digit_prefix`, and proof irrelevance give agreement with every prefix of `x`. A separate public prefix-encoding theorem is unnecessary.

**SN4. `cL_prefix_eq`**

```lean
(A : Riffle.Setup D) (x : Riffle.Word) (hx : Riffle.Legal D x)
(u : Riffle.Word) (hux : u <+: x) :
  Riffle.cL A u =
    TimeProfile.cL D.N (asProfile D) (legalVector x hx)
      A.b A.w.length u.length
```

This equality uses the literal existing definitions even if `u` is shorter than the ambient word; then both extension ranges are empty. Therefore an extra ambient-prefix premise is unnecessary. In the actual application, ambient descent is independently supplied by the stable facts. This equality does not identify `A.b` with an exact mass exponent.

**SN5. `cL_parent_eq`**

```lean
(A : Riffle.Setup D) (x : Riffle.Word) (hx : Riffle.Legal D x) :
  Riffle.cL A (Riffle.parent x) =
    TimeProfile.cL D.N (asProfile D) (legalVector x hx)
      A.b A.w.length (x.length - 1)
```

Use SN4, `Riffle.parent_prefix`, and `Riffle.parent_length`. The vector remains the encoding of `x`.

**SN6. `sampleRow_full`**

```lean
(D : Riffle.Model) (sample : TimeProfile.ShuffleSample (asCuts D))
(i : Fin D.N) :
  Riffle.Full D (Riffle.fullList (D := D) (TimeProfile.sampleRow sample i))
```

Every sampled digit has positive prescribed count by `TimeProfile.sample_entry_count_pos`. This theorem is what permits source cylinder and side predicates to be identified on actual sampled rows; an arbitrary alphabet-valued vector need not be legal.

**SN7. `expectedCount_eq_integral`**

```lean
(D : Riffle.Model) (E : Set Riffle.Word) :
  (Riffle.expectedCount D E : ℝ) =
    ∫ sample : TimeProfile.ShuffleSample (asCuts D),
      (TimeProfile.rowCount (TimeProfile.sampleRow sample)
        (fun row => Riffle.fullList (D := D) row ∈ E) : ℝ)
      ∂TimeProfile.fixedCountMeasure (asCuts D)
```

There is no measurability premise on `E`: the sample space and row-word space here are finite. Partition rows by their complete finite word and apply `TimeProfile.expected_box_count` to singleton coordinate sets; interchange finite sums and integrals using `TimeProfile.fixedCount_integrable`. SN1 then identifies the product weights. This proves the connection between the two expectation definitions instead of assuming it.

**SN8. `expectedCount_cylinder_eq`**

```lean
(x : Riffle.Word) (hx : Riffle.Legal D x)
(u : Riffle.Word) (hux : u <+: x) :
  (Riffle.expectedCount D (Riffle.Cylinder D u) : ℝ) =
    TimeProfile.prefixMass D.N (asProfile D) (legalVector x hx) u.length
```

On sampled rows, SN6 and the finite-prefix digit agreement identify the event with `TimeProfile.prefixRows`; then use SN7 and `TimeProfile.expected_prefix_count`. An alternative direct product proof must explicitly remove illegal zero-weight words using `Riffle.weight_eq_zero_of_not_legal`.

**SN9. `expectedCount_piece_eq`**

```lean
(A : Riffle.Setup D) (s : Riffle.Side) (x : Riffle.Word)
(hx : x ∈ Riffle.Desc D A.w) (j : Fin D.K)
(hwj : A.w.length ≤ j.val) (hjx : j.val < x.length) :
  (Riffle.expectedCount D (Riffle.PieceEvent A s x j.val) : ℝ) =
    TimeProfile.sideMass D.N (asProfile D) (legalVector x hx.1)
      A.w.length (sideProbability s) j
```

`Riffle.pieceEvent_iff` supplies the exact row event. The agreement through `j` and the ambient-prefix relation make the ambient condition automatic. Later columns remain unrestricted. Apply SN7 and the corresponding existing `TimeProfile.expected_left_side_count` or `expected_right_side_count`. No conditioning law or variance assertion is used.

**SN10. `sideMaximum_eq`**

```lean
(A : Riffle.Setup D) (s : Riffle.Side) (v x : Riffle.Word)
(hx : x ∈ Riffle.Desc D A.w) (hvx : v <+: x) :
  (Riffle.sideMaximum A s v x : ℝ) =
    TimeProfile.sideMaximum D.N (asProfile D) (legalVector x hx.1)
      A.w.length v.length (sideProbability s)
```

An additional `A.w <+: v` premise is not needed: if its length lies below the ambient length the index sets are empty, and otherwise the common-prefix facts give the required side events. Reindex the finite natural supremum to `TimeProfile.positions`; use nonnegative masses to cancel `Real.toNNReal` against the NNReal coercion. Do not interchange maximum and expectation.

**SN11. `cFAt_eq`**

```lean
(A : Riffle.Setup D) (v x : Riffle.Word)
(hx : x ∈ Riffle.Desc D A.w) (hvx : v <+: x) :
  Riffle.cFAt A v x =
    TimeProfile.cF D.N (asProfile D) (legalVector x hx.1)
      A.w.length v.length
```

SN10 on both sides gives the square-root values. Both logarithmic definitions send zero to bottom and otherwise divide the real logarithm by `log N`. Equality is in `WithBot ℝ`, including empty or zero side maxima.

**SN12. `cF_eq`**

```lean
(A : Riffle.Setup D) (y z x : Riffle.Word)
(hp : Riffle.RawPair A y z)
(hx : x ∈ Riffle.Desc D (Riffle.join y z)) :
  Riffle.cF A y z =
    TimeProfile.cF D.N (asProfile D) (legalVector x hx.1)
      A.w.length (Riffle.join y z).length
```

`Riffle.rawPair_join_desc` supplies ambient descent and `Riffle.cFAt_continuation` supplies continuation independence. No nonterminal premise is present here; bottom must remain valid for terminal pairs.

**SN13. `rawPair_crossings`**

```lean
(A : Riffle.Setup D) (y z x : Riffle.Word)
(hp : Riffle.RawPair A y z) (hnt : ¬Riffle.Terminal D y z)
(hx : x ∈ Riffle.Desc D (Riffle.join y z)) :
  TimeProfile.Crossings (asProfile D) (legalVector x hx.1)
    A.w.length (Riffle.join y z).length A.chi
```

The exact witness indices are `y.length - 1` and `z.length - 1`, lifted into `Fin D.K`. Use `Riffle.boundary_nonterminal`, `rawPair_prefix_join`, `leftIndex_mem`/`rightIndex_mem`, and the corresponding alphabet bounds. At each witness a side-probability sum contains a summand at least `A.chi`. Nonterminality guarantees that both witnesses exist; neither `Retained` alone nor an arbitrary terminal pair suffices. No admissibility budget or finite-`cF` premise is added.

**SN14. `stop_stableAt`**

```lean
(A : Riffle.Setup D) (y z x : Riffle.Word)
(hx : Riffle.Legal D x) (F : ℝ)
(hF : Riffle.cF A y z = (F : WithBot ℝ))
(hstop : Riffle.Stop A y z x) :
  TimeProfile.StableAt D.N (asProfile D) (legalVector x hx)
    A.b A.w.length x.length F A.delta
```

`hF` identifies a real representative of the existing extended exponent; it is not a new scientific assumption. In actual source applications SN12 transports the `cF = ↑F` equality returned by `source_large_margin`. Use `Riffle.stop_iff_sub_lt`, SN4 with `u=x`, and strict-to-nonstrict implication. Do not assert the converse or weaken the actual stop definition.

**SN15. `gamma_parentCrossing`**

```lean
(A : Riffle.Setup D) (y z x : Riffle.Word)
(hp : Riffle.RawPair A y z)
(hroot : ¬Riffle.Stop A y z (Riffle.join y z))
(hx : x ∈ Riffle.Gamma A y z) (F : ℝ)
(hF : Riffle.cF A y z = (F : WithBot ℝ)) :
  TimeProfile.ParentCrossing D.N (asProfile D)
    (legalVector x hx.1.1.1) A.b A.w.length
      (Riffle.join y z).length x.length F A.delta
```

Here `hx.1.1.1` is the existing legal-word component of Gamma's `pairDesc` membership. `Riffle.gamma_first_crossing hp hroot hx` gives the strict join/word length inequality, parent ambient descent, and parent non-Stop condition. These imply the first two `ParentCrossing` clauses and, by `Riffle.not_stop_iff_sub_ge` and SN5, its last clause. The root-not-stopped premise is essential and is already the branch condition of the actual stable definition. A separate nonterminal premise is unnecessary for this implication: root-not-stopped Gamma membership already forces a proper continuation. Unrestricted Gamma membership does not suffice.

**SN16. `ambientApproximation_iff`**

```lean
(A : Riffle.Setup D) (x : Riffle.Word)
(hx : x ∈ Riffle.Desc D A.w) (r er eb : ℝ) :
  TimeProfile.AmbientApproximation D.N (asProfile D) (legalVector x hx.1)
      A.w.length r A.b er eb ↔
    |(A.w.length : ℝ) / Real.log (D.N : ℝ) - r| ≤ er ∧
    |Real.log (Riffle.expectedCount D (Riffle.Cylinder D A.w) : ℝ) /
        Real.log (D.N : ℝ) - A.b| ≤ eb
```

This is an equivalence obtained from SN8 at `u=A.w`. It assumes no approximation, sign of the errors, or exact ambient normalization. Its right-hand side is precisely the finite quantitative version of the original source ambient data. The same right-hand side serves every continuation of `A.w`.

## Dependency order and proof-local helpers

The finite adapter and digit identities precede all comparisons. SN4–SN5 use finite sum reindexing and prefix agreement. SN6–SN7 provide the literal expectation identity; SN8–SN9 specialize it to cylinders and side pieces. SN10–SN12 pass through finite suprema and the extended logarithm. SN13 is independent of the expectation bridge: probability coordinates and boundary crossing witnesses suffice. SN14 and SN15 use the cost identities and existing strict stopping equivalences. SN16 uses only SN8 and the frozen ambient-approximation definition.

No additional public interval equivalence is necessary. Inside proofs, `j ↦ j.val` bijects `TimeProfile.positions D.K a b` with `Finset.Ico a b` whenever `b ≤ D.K`. The required upper bound follows from legality or a prefix length. Finite sum/product/supremum reindexings and event-predicate equalities can therefore remain local. At sampled rows, prefix equality is proved using `Riffle.fullList_digit` and `List.ext_getElem`/take equality, with SN6 supplying full legality. It must not be asserted for all raw finite words without the legality qualifier.

`TimeProfile.expected_cF_eq` alone does not prove SN12: it compares two time-profile definitions, while SN7–SN11 connect the separate Riffle definitions. Likewise positivity or a fixed-count moment theorem supplies no stochastic endpoint density or conditional ambient-law theorem.

## Actual stable-branch use

For `hpA : Riffle.AdmissiblePair A y z` and `hxS : x ∈ Riffle.Stable A y z`, derive `hp := Riffle.admissiblePair_rawPair hpA` and `hx := Riffle.stable_desc hp hxS`. This supplies the exact proof fields used by SN12 and, only in the nonterminal branch, SN13. No duplicate legality or retention hypothesis is needed in an eventual actual-word wrapper.

Stable membership alone must not be passed to SN14: terminal singleton and Lambda branches need not stop. First split the original definition. The stopped-root branch satisfies Stop. In the remaining nonterminal branch, the existing source tail theorem must exclude Lambda using the genuine analytic inputs and error budget; only then are Gamma/Stop conclusions valid. The Gamma branch comes with the exact root-not-stopped fact needed by SN15. This is a distinction of source branches, not an assumption that the stable set has cardinality greater than one.

For Lambda, `Riffle.lambda_full` supplies full legality. `TimeProfile.source_no_terminal_fallback`, after the exact adapters and source assumptions are supplied, returns a strict terminal inequality and the real exponent. SN12, SN4, and `Riffle.stop_iff_sub_lt` then contradict Lambda's original non-Stop condition. Two real values representing the same `WithBot` value are equal by coercion injectivity; no extra equality premise is needed.

Terminal pairs retain the singleton route, including final-coordinate genuine crossings and no-crossing fallback boundaries. SN12 remains valid with bottom, but SN13 is not applied. `TimeProfile.source_singleton_margin` needs no crossing/finite-fluctuation premise, and `TimeProfile.cE_terminal` handles its terminal tail. The ambient-full and `K=0` cases must remain included.

## Scientific inputs intentionally outside this finite contract

`D.K = TimeProfile.horizonDepth D.N T` is an original source relation to be represented by explicit equality transport or by constructing the model from horizon-indexed cuts. It is not a consequence of `Riffle.Model` or `Setup`, and this adapter contract introduces no horizon. The scaled terminal time remains `K/log N`; its difference from `T` is handled by the existing floor-error theorem.

The ambient time/mass bounds on the right side of SN16, the actual `AlmostLike` data, regular partition, time law, variational `FirstMomentMargin`, and explicit uniform error budgets must be supplied from their original source statements. `A.b` cannot be replaced by the exact ambient logarithm. `A.C`, the boundary admissibility constant, must remain distinct from the regular-partition oscillation constant used by `P.IsRegular` and SourceNumerical. The numerical layer's clamped times `max r (v/log N)` and `max r (n/log N)` are retained; an approximate ambient birth time does not imply the stronger exact inequality `r ≤ v/log N`.

There is no existing stable-block `Riffle.cE` to identify. Use `TimeProfile.cE D.N (asProfile D) x.length` directly. A separate later collision bridge must distinguish its squared-probability product from the generally smaller without-replacement factorial collision factor.


The algebra, statement-design and adversarial reports all approve candidate `05f5f072fb6d7061e85f4167dbe9566f6a3648a3729422f29b6e761a9ccb2138`. Their sole earlier elaboration correction made the model argument explicit in SN6 before this freeze. The sixteen exact assumptions and conclusions, four definitions and proof-local helper domains are frozen. The preexisting contracts remain unchanged. No extra scientific assumptions, axioms, unproved placeholders or additional exported helpers are authorized by this contract.
