# LB06 independent final review: rounding, counting, construction

Date: 2026-10-01. Reviewer: mathematical/truncation worker, independently of the combinatorial implementation author. Scope: read-only proof and interface review of the final versions listed below. No implementation source was changed.

## Source identity and verdict

| Reviewed file | SHA-256 |
|---|---|
| `RiffleLowerV2/Types/Rounding.lean` | `75494b90c3a320130dea75af42c0a1614b31e7ce777738332736c72ce5ec5ad4` |
| `RiffleLowerV2/Types/Counting.lean` | `c9447f614ac6458dd4b7a8d2512258a012a736ad8c8b62cf00520e87db05226c` |
| `RiffleLowerV2/Types/Construction.lean` | `0036eea61d471f585da911739d6f03da65d1cd91ba56b190c7ae044ad0513d66` |

**Approved.** No mathematical defect, circular counting argument, hidden positivity-of-occupancy condition, or strengthening of the frozen hypotheses was found. The exact cardinality and nonemptiness conclusions are proved from compatible integer totals, then specialized to the actually constructed retained-law counts. The coordinator reports a clean complete `Types.Main` build; compilation and full-environment axiom closure are recorded separately by the coordinator and are not inferred from this source review.

## Deterministic rounding

`roundedCount` is the difference of consecutive natural floors of cumulative masses in the fixed `Fin k` digit order. This is a deterministic function of `n` and `q`; it does not select a vector by assuming the desired rounding predicate.

The potential natural-subtraction problem is addressed correctly. `roundingPrefix_step` proves monotonicity from coordinatewise nonnegativity, and `Nat.floor_mono` permits exact cancellation of the differences and their casts. `roundingPrefix_total` uses the supplied normalization once to identify the last prefix with the integer `n`; telescoping then proves the exact total.

Zero weights yield identical adjacent prefixes, so `roundedCount_zero` preserves support exactly. The coordinate error theorem uses both lower and strict upper floor inequalities to give the stronger bound `<1`, and the required `<=1` theorem follows. It requires no lower bound on `n`, no lower bound on an individual positive weight, and no occupancy assumption. When `n=0`, every prefix and count is zero, so all conclusions remain valid.

The cumulative construction is an admissible implementation of the source's supported rounding requirement and the reviewed frozen interface. It need not coincide coordinatewise with one particular floor-then-distribute convention: the source and target require deterministic supported counts with exact total and error at most one, all of which are proved.

## Exact finite counting

`prescribedWords_nonempty` uses the given equality between the sum of counts and the cardinality of the position domain to construct an equivalence with the labelled disjoint union `Sigma a, Fin(c a)`. Projecting its image to the letter gives a word with the prescribed counts. The assumed equality is an exact-total condition, not an assertion about the cardinality or existence of the desired word class.

`prescribedWords_card_mul` counts all equivalences between the position domain and that labelled union. The map to a prescribed word has fibers in bijection with a product of equivalence spaces, one for every letter. Each factor has exactly `c a` elements in its source and target and hence `(c a)!` equivalences. The disjoint union of these fibers is equivalent to the entire equivalence space, whose cardinality is `|J|!`. This proves the integer multiplicative identity

```
|prescribedWords| * product_a (c a)! = |J|!.
```

Only after that identity does `prescribedWords_card` divide by the product of factorials, whose positivity is proved with `Nat.factorial_pos`. Thus the natural quotient is exact; no real-to-natural division replacement or unproved divisibility premise is used.

The cell-level class is explicitly equivalent to a dependent product of the single-cell classes. The forward map restricts to each actual classifier fiber; the inverse evaluates the cell's word at that same position. Both inverse laws are proved, and the digit fibers are identified by genuine subtype equivalences. Therefore the cell factorization counts distinguished positions correctly and introduces neither missing factors nor unused-coordinate choices.

`cellPositionCount_eq_fiberCard`, `wordCellCount_eq_fiberCard`, and `roundedClass_eq_prescribedCellWords` connect this generic argument to the unchanged frozen definitions. In particular, the position domain is the subtype of the selected `Finset I`, rather than all `Fin K`. The class cardinality theorem is exactly the product of per-cell natural factorial quotients appearing in `TypeDataSpec`.

## Empty and degenerate cases

- Empty cells force all their natural counts to zero by the exact-total hypothesis. Their one-cell class contains the unique function on the empty domain, and their quotient is `0!/(product 0!)=1`.
- If the selected set `I` is empty, `WordOn k I` has exactly one member and every cell count is zero. Both generic nonemptiness and product-cardinality arguments cover this case without a separate nonempty-domain premise.
- Generic empty letter or cell index types cause no invalid invocation of a chosen element. In inconsistent nonempty-domain cases the exact-total hypothesis is impossible; in the consistent empty-domain cases the equivalence and product arguments give the unique empty function.
- There is no requirement that every retained digit occur in every cell. A positive retained weight may receive count zero for a short block; support only requires that omitted digits receive zero count.

The separate `Empty.lean` convenience statements were inspected as supporting context. They correctly state singleton raw/selected classes, empty-word mass 1, and zero exponents for explicit zero-count/zero-bin data. The reviewed construction's empty behavior also follows directly from its cumulative counts and least-maximal-bin rule: its sole word has mass 1 and bin index 0.

## Specialization and absence of assumed conclusions

`initialTypeData` sets every count to the explicit `roundedCount` of the actual cell position count and the frozen retained law. Its total, support, and rounding-error theorems are direct applications of the proved normalization/support and rounding lemmas. Its nonemptiness theorem invokes the independently proved counting result.

`constructedTypeData` changes only the bin index through `selectBinData`. The count equality and raw-class equality are definitional, so bin selection cannot invalidate the combinatorial class that was counted. The `MassBins` dependency uses `Nat.find` to choose the least globally maximizing natural index; its proved tie rule and positive selected size establish the requested deterministic interpretation.

`typeDataSpec_of_counts` has abstract nonemptiness and cardinality inputs, but `constructedTypeData_spec` discharges both with `initialTypeData_nonempty` and `roundedClass_card` applied to `initialTypeData_total`. Likewise every normalization, support, and coordinate-error input is supplied by a theorem about the actual constructed counts. Consequently the final `exists_typeDataSpec` theorem does not leave a desired counting conclusion as a caller assumption.

The construction theorem assumes only `k>=2`, `N>=2`, the stated positive cutoff range, an actual regular partition, and the cut-array/selected-set data. It proves the exact finite specification for every real `alpha`; this is stronger than the target's analytic tilt interval and is justified because retained base probabilities are positive. The `[2,4]` restriction is applied separately by the analytic approximation layer. No temporal profile, LB05 theorem, or asymptotic occupancy condition is introduced here.

## Final obligation ledger

| Obligation | Reviewed evidence | Verdict |
|---|---|---|
| Deterministic supported integer counts | `roundedCount`, its sum/zero/error theorems | Discharged |
| Nonempty raw class | Labelled finite equivalence construction | Discharged |
| Exact natural multinomial quotient | Multiplicative factorial identity, then positive division | Discharged |
| Product over cells | Explicit restriction/assembly equivalence | Discharged |
| Arbitrary selected columns | Exact subtype/fiber adapters to `WordOn` | Discharged |
| Empty cells and empty selected set | Uniform finite constructions with no nonempty-domain assumptions | Discharged |
| Generic hypotheses specialized to actual counts | `constructedTypeData_spec` theorem arguments | Discharged |
| Lower entropy estimate | Supplied by separate entropy module; not claimed by these files | Separate reviewed integration obligation |

No change request remains from this review.
