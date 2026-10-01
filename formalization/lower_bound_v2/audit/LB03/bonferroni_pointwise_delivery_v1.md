# LB03 pointwise Bonferroni delivery v1

`RiffleLowerV2/Factorial/Bonferroni.lean` passed the lane compiler during the v3 and v4 builds of `RiffleLowerV2.Factorial.PoissonPolynomial`. Those builds subsequently failed in the scalar module, so neither log is a complete LB03 or complete two-module receipt.

Completed frozen exports:

- `RiffleLowerV2.Factorial.bonferroniSandwich : RiffleLowerV2.Targets.BonferroniSandwich`.
- `RiffleLowerV2.Factorial.bonferroniProduct : RiffleLowerV2.Targets.BonferroniProduct`.

The proof establishes the exact finite identity

`U_(m+1)(n+2) = 1 + (-1)^(m+1) [choose(n,m) + m choose(n+1,m+1)]`.

Its induction uses Pascal's identity only. The bracket is manifestly nonnegative, so the odd/even adjacent bounds include all counts without truncating a tail event. Counts 0 and 1 and truncation degree 2 are handled explicitly.

The public helper `product_remainder` proves the algebraic statement for real `u,v,a,b,dx,dy`:

`0≤a≤1`, `0≤b≤1`, `0≤u−a≤dx`, `0≤v−b≤dy` imply
`0≤uv−ab≤dx+dy+dx*dy`.

This helper is also available for the scalar benchmark in the finite central comparison. No sibling proof lane or historical source was imported. The immutable target statements were retained. The complete scalar module build and an explicit axiom report remain pending at this delivery checkpoint.
