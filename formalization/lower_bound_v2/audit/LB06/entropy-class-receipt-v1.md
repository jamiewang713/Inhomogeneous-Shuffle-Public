# LB-06 concrete class entropy adapter: receipt v1

Module `RiffleLowerV2.Types.ClassEntropy` is complete and checked. Source SHA-256: `8cbc701b627ede6e0ffac138e72a04d8e92aa2af92b218304c16fa13ba220074`.

The module imports checked `EntropyBounds` and `Counting`. It proves four public declarations in namespace `RiffleLowerV2.Types`:

- `multinomial_quotient_pos`: exact natural counts with total `n` imply the factorial quotient `n! / ∏ c_l!` is positive.
- `log_multinomial_quotient`: under the same exact-total hypothesis, the real logarithm of that natural quotient is exactly `log(n!) - Σ log(c_l!)`.
- `roundedClass_log_card`: exact cell totals imply the frozen raw class has logarithm equal to the sum of those per-cell factorial expressions.
- `roundedClass_entropy_error`: for arbitrary cuts, partition, chosen column set and data `D`, and arbitrary `q : Fin P.cellCount → Fin k → ℝ`, exact cell totals, nonnegative normalized `q_i`, and coordinate rounding errors at most one imply

```text
|log ((roundedClass cuts hN P I D).card)
  - Σ i, cellPositionCount cuts hN P I i * shannonEntropy (q i)|
≤ P.cellCount * (2*k+1) * (log(I.card+1)+2).
```

These are real-valued expressions with explicit casts in the Lean source. Empty cells, the empty selected set and zero coordinates are covered. The error is two-sided; there is no assumed entropy estimate.

The natural-division adapter derives its log identity from the actually checked multiplicative fiber-cardinality equality `prescribedWords_card_mul`, positivity of the finite class, and positivity of factorials. It does not apply real division rules directly to a potentially inexact natural quotient. `roundedClass_log_card` uses the exact `Counting.roundedClass_card` theorem. The error then follows by summing `multinomial_log_entropy_error` over cells and using the elementary bound `cellPositionCount≤I.card`.

Successful verification command from the package root:

```text
python3 scripts/lane.py LB06 RiffleLowerV2.Types.ClassEntropy
```

Final output was `LB06 BUILD_OK` with no warnings. Its recursive owned-module build also rechecked `EntropyBounds`, `Rounding` and stable `Counting`. Initial attempts met the owner lock, a then-active upstream adapter repair, and routine coercion simplifications; those failed attempts were not treated as validation.

The successful independent compiler check `audit/LB06/entropy-class-axioms-v1.lean` printed every substantive declaration's axiom closure; the exact output is in `entropy-class-axioms-v1.log`. Each closure is `propext`, `Classical.choice`, and `Quot.sound` only.

The remaining caller obligations are to substitute the concrete normalized retained law and rounded counts, sum the spatial replacement errors, and include mass-bin loss. Neither the final target nor a desired class entropy estimate occurs as an assumption of this adapter.
