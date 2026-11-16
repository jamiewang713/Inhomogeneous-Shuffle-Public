# Frozen finite source adapters — version 1

These are applications of F01–F11 to newly available project definitions.
They introduce no time law, integral, stochastic expectation, asymptotic
premise, or changed stopping definition. The original F01–F20 contract is
unchanged. All three independent reviews have been compared. S01–S05 are now
frozen before their implementation. The S05 real expression is explicitly
coerced as a whole into `WithBot Real`.

Use the existing `TimeProfile` definitions from `RiffleTimeProfile.Base`
and `RiffleTimeProfile.Ambient`. Let `p : Fin K -> Simplex k`,
`x : Fin K -> Fin k`, `P : BorelPartition k`, and `L=logScale N`.
Positions and prefix lengths use the existing zero-based convention.
Below, `J=positions K w M`, and
`n_i=card {j in J : P.classify (p j)=i}`.

S01 (F01–F04). If `chi>0` and `P.IsRegular chi C`, the actual masses
`prob(p j)(x j)` and representative masses
`prob(P.rep(P.classify(p j)))(x j)` form `RiffleProfiles.RegularDigits`
on any finite position set, with parameters `chi` and `C*chi`.
Prove the equality `digitCost z = RiffleProfiles.cost z` directly;
physical positivity is supplied where each frozen estimate requires it.

S02 (F06/F08). If `N>=2`, `P.IsRegular chi C`, and for every cell
`|n_i/L-m_i|<=delta_i` on `J=positions K M K`, then

`|cE N p M + sum_i m_i * psi(P.rep i,2)|`
` <= card(J)*C*chi/L + sum_i |psi(P.rep i,2)|*delta_i`.

The `m_i` are arbitrary finite target weights, as in F06. No integral
interpretation or extra positivity is attached to them.

S03 (F06/F09). If `N>=2`, `P.IsRegular chi C`, `LegalPrefix p x M`, and
for every cell `|n_i/L-m_i|<=delta_i` on `J=positions K w M`, then

`cL N p x b w M <= b - sum_i m_i * maxCost(P.rep i)`
` + (card(J)*C*chi/L + sum_i |maxCost(P.rep i)|*delta_i)`.

The legal source prefix supplies the positive selected masses; simplex
membership supplies domination by the maximal mass. No artificial
time ordering or full-support assumption is added.

S04 (F10). If `N>=2`, `chi>0`, `w<=v<=K`, `LegalPrefix p x v`, and a
witness `j in positions K w v` satisfies `chi<=side(p j)(x j)`, then

`chi * prefixMass N p x v <= sideMaximum N p x w v side`.

Here `side : Simplex k -> Fin k -> Real` may in particular be the existing
`leftProbability` or `rightProbability`. The witness is exactly the
corresponding component of the existing `Crossings` definition. The
proof must factor the actual prefix product at j, retaining the crossing
factor among the continuation factors, and establish positivity before
using the conversion through `Real.toNNReal`.

S05 (F11). If `N>=2`, `chi>0`, `w<=v<=K`, `LegalPrefix p x v`, and
`Crossings p x w v chi`, then, as an inequality in `WithBot Real`,

`((cL N p x b w v`
`   + (log(prefixMass N p x w)/L-b) + log chi/L)/2 : Real)`
` <= cF N p x w v`.

The ambient error is displayed exactly, as frozen in F11; it is not
assumed to vanish. Positivity of both side maxima and their square roots
must follow from S04 and legality. This concerns the defined deterministic
mass exponent only and implies no variance or anti-concentration theorem.
