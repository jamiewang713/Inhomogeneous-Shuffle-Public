# LB09 Words and Bridge delivery v1

`RiffleLowerV2.Localization.Words` and `RiffleLowerV2.Localization.Bridge` compile successfully without warnings using the acknowledged unchanged v1 contract.

Verified command, run from the integration package:

```text
python3 audit/LB09/serial_build.py RiffleLowerV2.Localization.Bridge
LB09 BUILD_OK
```

The main concrete constructor is `Localization.exists_bridgeGeometry`. It takes actual cuts, `2≤N`, `0<N`, `2≤k`, positive rho/chi, a partition and witness, a canonical ambient word, two rounded-type data objects, and the proved `WitnessSpec`. It constructs `G : ColdGeometryData K P W` with the prescribed ambient and types, proves `BridgeSpec`, and proves that every coordinate of each central/reserve bridge has probability at least `min chi (1/k)`. Each reserve changes exactly its designated good column. The constructor proves the strict lexicographic inequalities, the product bound `chi^2*k^(-bridgeLength)`, and the exact frozen bridge logarithmic bound.

The reusable exports in `Localization.Words` include:

- `columnSet_card`, `columnSet_union`, `columnSet_disjoint`, `prod_columnSet_split`.
- `massOn_restrictWord`, `prefixMass_split`.
- `joinColdWord_get_prefix`, `joinColdWord_get_bridge`, `joinColdWord_get_tail`, `joinColdWord_get_ambient`.
- `restrict_join_prefix`, `restrict_join_bridge`, `restrict_join_tail`, `prefixAt_joinColdWord`.
- `joinColdWord_injective`, `coldFullFamily_card`.
- `reservePrefix_mean`: exact ambient-prefix mean times prefix mass times reserve bridge mass.
- `joinColdWord_mass`: exact ambient-prefix mass times prefix, bridge, and tail masses.
- `canonical_digit_eq_pileMax`, `canonical_digit_ge_inv`, `canonical_prefixMean_eq_rpow_beta`.

`canonical_prefixMean_eq_rpow_beta` applies at every `m≤K`, with `N≥2`, and proves the exact mean `(N:Real)^(beta cuts hN (gridTime N m))` of any canonical ambient prefix. It adapts the maximizing-coordinate/log-product argument from the checked LB02 `Thinning/MaximalWord.lean` and uses the checked shared `empiricalIntegral_grid` theorem. No old-package binary output is imported.

`Bridge.goodColumn_ordered_digits` and `bridge_log_bound` expose the ordered-good-digit selection and logarithmic bridge estimate separately. All new declarations are proved from concrete data; no target-valued or localization premise was introduced. Full-family mass/digit consequences and asymptotic absorption of reserve means are being assembled separately by the geometry worker. The final whole-lane compiled-declaration and axiom-closure audit remains the coordinator's deliverable.
