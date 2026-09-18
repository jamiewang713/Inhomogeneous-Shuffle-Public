# Independent representation review of S01–S05

I read `FINITE_SOURCE_ADAPTERS_CANDIDATE.md`, the corresponding frozen
`RiffleProfiles.Estimates` definitions/theorems, and the existing
`TimeProfile.Base`/`TimeProfile.Ambient` representations. All five candidate
specializations are mathematically valid with the stated hypotheses. No
Lean adapter code was written during this review.

The original F01–F20 contract remains unchanged. These adapters introduce
no time-law measurability, integral, expected shuffle mass, asymptotic
limit, or alternate stopping rule.

## Shared representation choices

Keep the existing full-word function types
`p : Fin K -> TimeProfile.Simplex k` and `x : Fin K -> Fin k`.
Use `TimeProfile.positions` directly; do not introduce a shifted copy of
the position convention. Paper column `j` is Lean column `j-1`, so
`positions K a b` means paper columns `a<j<=b`.

Use the existing classifier `P.classify` and representatives `P.rep`.
The cell type is `Fin P.cellCount`; the target values and discrepancy
bounds have type `Fin P.cellCount -> Real`. Each cell count in S02/S03
is the natural cardinality of the corresponding filtered position set,
cast to the reals before division by `TimeProfile.logScale N`.

The identity `TimeProfile.digitCost z = RiffleProfiles.cost z` follows
from `Real.log_inv` and `one_div`. Because both real functions are
totalized in Lean, this identity is valid for all real `z`; it does not
grant positivity or a physical interpretation at zero. Every positivity
premise of the frozen finite inequalities is still discharged from
legality where needed.

## S01: approve

Take any finite position set `J : Finset (Fin K)`, actual selected values
`j -> TimeProfile.prob (p j) (x j)`, and representative selected values
`j -> TimeProfile.prob (P.rep (P.classify (p j))) (x j)`.

The target is exactly `RiffleProfiles.RegularDigits J actual rep chi
(C*chi)`. Its three fields are supplied as follows:

- `threshold_pos` is the candidate `chi>0` premise;
- `good_bound` is `P.IsRegular.good_digit` at cell `P.classify(p j)`,
  with the cost identity applied to its absolute-error component;
- `exceptional_bound` is `P.IsRegular.exceptional_digit` at that same
  cell, using the candidate's non-strict exceptional threshold.

No legality premise is required merely to build this regularity object.
The later cost/length results impose legality separately, exactly as the
frozen contract requires. No `C>=0` premise needs to be added.

## S02: approve

Set `J=TimeProfile.positions K M K`, `L=TimeProfile.logScale N`,
`cell j=P.classify(p j)`, actual values `TimeProfile.psi(p j,2)`, and
representative values `TimeProfile.psi(P.rep i,2)`.

`TimeProfile.logScale_pos` supplies `L>0` from `N>=2`.
`BorelPartition.IsRegular.psi_rep_error` supplies the uniform error
`C*chi`, since `2` belongs to `[2,4]`. The cell-count inequalities are
exactly the frozen F06 premises; target values may be arbitrary reals.

Use `RiffleProfiles.tail_cell_replacement`, or F06 followed by the
negation identity, and unfold `TimeProfile.cE`. Its definition
`-(sum psi)/L` equals the negative of the normalized sum. The desired
`|cE + sum target*repPsi|` is therefore precisely the absolute error.
Preserve the full sum `sum_i |repPsi_i|*delta_i`.

The candidate correctly does not assume `M<=K`, `chi>0`, `C>=0`, or
nonnegative target weights for this finite specialization. When the tail
position set is empty, the same F06 statement handles it. Regularity is
the entire premise needed for the representative oscillation bound.

## S03: approve

Set `J=TimeProfile.positions K w M`. For each member `j`, the position
membership proves `j.val<M`, so `TimeProfile.LegalPrefix p x M` supplies
a strictly positive selected mass. `TimeProfile.prob_le_pileMax` supplies
its domination by the maximal mass.

Apply `RiffleProfiles.maximal_pile_domination` with the selected masses
and `j -> TimeProfile.pileMax(p j)`. The cost identity turns its left
side into the existing `TimeProfile.cL` and the right observable into
`TimeProfile.maxCost`.

Apply `RiffleProfiles.cell_replacement` to the maximal cost, using
`BorelPartition.IsRegular.maxCost_rep_error`. Finally use
`RiffleProfiles.maximal_pile_target` to get the displayed one-sided
bound, with the unchanged explicit discrepancy term.

No additional `w<=M`, `M<=K`, `chi>0`, `C>=0`, or `delta_i>=0` assumption
is needed by the stated finite inequality. The actual set membership is
enough to invoke legality. This does not change the source's intended
domain; it avoids adding irrelevant premises to the already frozen
finite proof.

## S04: approve

The arbitrary real-valued `side` function must remain arbitrary away
from the witness. In particular, do not add a global nonnegativity or
upper-bound assumption for `side`.

From the witness membership derive `w<=j.val<v<=K`. Define the common
earlier mass as

`earlier = prefixMass(N,p,x,w) * product_{h in positions K w j.val} selected_h`.

The required factorization is

`prefixMass(N,p,x,v) = earlier * product_{h in positions K j.val v} selected_h`.

The second product includes the crossing column `j`; excluding that
column would give the wrong factorization. It follows by splitting the
actual prefix positions into `0..w`, `w..j`, and `j..v`, proving the
finite unions disjoint, and using product-over-union identities.

`earlier` is nonnegative by simplex coordinate nonnegativity and natural
`N`. Multiplying the witness's `chi<=side(p j)(x j)` by this earlier
mass gives the frozen F10 side premise. Every continuation factor is
in `[0,1]`; F10 therefore yields

`chi * prefixMass(N,p,x,v) <= sideMass(N,p,x,w,side,j)`.

Legality and `N>=2` make the prefix mass strictly positive, and `chi>0`
then makes the witness side mass strictly positive. Establish that fact
before rewriting its `Real.toNNReal` coercion back to the original real
number. The finite supremum contains the witness, so it dominates that
side mass. This proves S04 exactly.

No separate `w<v` premise is needed: the witness already entails it.
When no witness can exist, the statement remains correctly vacuous.

## S05: approve, with explicit coercion in the Lean statement

The entire displayed real left-hand expression must be cast to
`WithBot Real`. Its type should be represented as

`coeWithBot( (cL(N,p,x,b,w,v)`
`  + (log(prefixMass(N,p,x,w))/L - b) + log(chi)/L) / 2 )`
`  <= TimeProfile.cF N p x w v`.

Here `coeWithBot` denotes only the ordinary coercion from `Real` to
`WithBot Real`, not a new definition. A real type annotation inside the
expression is insufficiently explicit for an unambiguous elaborated
statement; use an outer `WithBot Real` coercion. This is a typing
clarification of the candidate's stated order, not a mathematical change.

Let `Mmass=prefixMass(N,p,x,v)` and let `U,V` be the two existing
`sideMaximum` values. Extract the two witnesses from `Crossings` and
apply S04 with `leftProbability` and `rightProbability`, obtaining
`chi*Mmass<=U,V`.

Legality and positive `N` prove `Mmass>0`; positive `chi` gives
`U,V>0`. Their square roots are consequently strictly positive.
Thus both calls of `TimeProfile.logExponent` take their nonzero branch
and are real coercions, not bottom.

Use the exact real identity `log(sqrt U)=log U/2`, and likewise for V.
After division by `L`, the existing `cF` becomes the `WithBot` minimum
of the coercions of `log U/(2L)` and `log V/(2L)`.

`RiffleProfiles.fluctuation_log_comparison` gives the real inequality

`(log Mmass + log chi)/(2L) <= min(log U/(2L),log V/(2L))`.

`TimeProfile.cL_exact_mass_exponent`, with exact lengths `w<=v<=K`,
identifies `log Mmass/L` with
`cL(N,p,x,b,w,v) + (log(prefixMass(N,p,x,w))/L-b)`.
Real arithmetic therefore identifies the displayed S05 left side with
the left side of F11. Lift the real inequality through the order
embedding into `WithBot`; equivalently prove its two `le_min` components
using the real comparison and the coercion-order equivalence.

Keep arbitrary real `b` and the exact ambient discrepancy. Do not add an
ambient approximation bound, require that the discrepancy tends to zero,
or replace the real lower bound by a weaker asymptotic statement. Also do
not infer a variance or anti-concentration result from this deterministic
mass-exponent comparison.

## Approval

All S01–S05 candidate statements are approved with their current
mathematical hypotheses. The only representation clarification is the
explicit outer `WithBot Real` coercion in S05. The proof obligations above
show where positivity and finite factorization are derived, so none needs
to be introduced as a new assumption during implementation.
