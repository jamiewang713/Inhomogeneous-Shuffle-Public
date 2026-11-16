# LB06 deterministic rounding and finite counting completion

Completed after the coordinator gate recorded in `LB06_INTERFACE_ACK_v1.md`.
Owned source files are `Types/Rounding.lean`, `Types/Counting.lean`, and
`Types/Construction.lean`. No shared source, frozen contract, manuscript, or
dependency configuration was edited by this worker.

## Checked exports

All names below have prefix `RiffleLowerV2.Types.`.

* `roundingPrefix n q a` and `roundedCount n q l` define deterministic
  digit-order cumulative-floor rounding.
* `roundedCount_sum n q hq hsum` proves exact total n.
* `roundedCount_zero n q l hl` preserves zero coordinates.
* `roundedCount_error_lt n q hq l` proves strict error less than one;
  `roundedCount_error` gives the required non-strict version.
* `exists_supported_rounding` bundles exact total, support, and coordinate error.
* `prescribedWords_nonempty` and `prescribedWords_card_mul` prove existence and
  the exact identity `card(words) * product(c_a!) = card(J)!` on any finite
  domain J with prescribed multiplicities summing to card(J).
* `prescribedWords_card` gives the exact natural factorial quotient.
* `prescribedCellWords_nonempty` and `prescribedCellWords_card` split the finite
  domain into arbitrary cell fibers and give the exact product of quotients.
* `cellPositionCount_eq_fiberCard`, `wordCellCount_eq_fiberCard`, and
  `roundedClass_eq_prescribedCellWords` adapt these statements to the frozen
  concrete definitions.
* `roundedClass_nonempty cuts hN P I D htotal` proves nonemptiness.
* `roundedClass_card cuts hN P I D htotal` proves exactly

```lean
(roundedClass cuts hN P I D).card =
  ∏ i : Fin P.cellCount, (cellPositionCount cuts hN P I i).factorial /
    ∏ l : Fin k, (D.count i l).factorial
```

Here `htotal` is precisely

```lean
∀ i, ∑ l, D.count i l = cellPositionCount cuts hN P I i
```

No positivity of individual counts, cell sizes, or the selected position set is
assumed. Empty cells and the empty position set are included.

`initialTypeData cuts hN P I xi alpha` stores these deterministic counts and
temporary bin index zero. `constructedTypeData cuts hN hk P I hxi hxiK alpha`
replaces that index by MassBins' least maximal mass bin. The actual proof

```lean
constructedTypeData_spec cuts hN hN2 hk P I hxi hxiK hreg alpha
```

has conclusion

```lean
TypeDataSpec cuts hN P I xi alpha
  (constructedTypeData cuts hN hk P I hxi hxiK alpha)
```

Its hypotheses are N≥2, k≥2, 0<xi<1/(4k), and P.IsRegular xi C. It works for
every real alpha; the restricted denominator is positive because a retained
simplex coordinate is positive, so no tilt interval is needed for these exact
finite properties. `exists_typeDataSpec` packages the existential conclusion.
The [2,4] tilt interval is still required by the approximation theorem, which
is outside this worker's construction result.

## Proof route and provenance

These sources are new local proofs. No old project proof text or old compiled
cache was ported. Counting uses equivalences J≃(Σ a, Fin(c_a)); the fiber over
a prescribed word is a product of equivalence types of cardinalities c_a!.
Counting the whole equivalence type gives the exact multiplication identity,
and only then natural division yields the quotient. A second equivalence
splits words across cell fibers. This proves a genuine lower count as well as
the upper count and does not infer the former from a mass-sum bound.

The generic counting implementation uses the already checked
`Mathlib.Data.Fintype.Perm`, `Equiv.ofFiberEquiv`, `Equiv.sigmaFiberEquiv`,
`Fintype.card_equiv`, `Fintype.card_sigma`, and `Fintype.card_pi`. It does not
need the coordinator's newly available Multinomial module.

Construction consumes checked local retained-law normalization from Truncation
and the explicit binning assembly theorem from MassBins. It discharges every
counting, support, normalization, nonemptiness, and exact cardinality premise
of that assembly theorem for concrete Cuts and the frozen class definitions.

## Verification

The following assigned-lane commands all returned `LB06 BUILD_OK`:

```text
python3 scripts/lane.py LB06 RiffleLowerV2.Types.Rounding
python3 scripts/lane.py LB06 RiffleLowerV2.Types.Counting
python3 scripts/lane.py LB06 RiffleLowerV2.Types.Construction
```

Compilation uses the assigned `.build/lanes/LB06/lib/lean` overlay and pinned
Lean 4.33.1 runtime. The final construction command recursively compiled all
three new sources with their checked local prerequisites.

`counting-axioms-v1.log` contains direct Lean `#print axioms` output for fourteen
substantive exports including both exact class cardinality theorems and the
full constructed TypeDataSpec. Every reported closure is exactly
`propext`, `Classical.choice`, and `Quot.sound`.

The full LB06 approximation and its uniform constants remain the responsibility
of the lane assembly. This report certifies the implemented rounding, counting,
and exact finite-specification construction only.
