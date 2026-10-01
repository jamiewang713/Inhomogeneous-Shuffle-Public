# LB04 proof obligations and build plan v1

This records planned work, not checked results. Dependent proofs await the three-review comparison and coordinator acknowledgement.

1. Finite PMF utilities on the existing real expectation and probability: linearity, monotonicity, complement and union bounds. Standard normalization is proved from PMF, never supplied as a conclusion-shaped assumption.
2. Relative-order law on arbitrary disjoint finite position sets: exact fiber/double counting; uniform factorial probabilities; factorization for functions of relative orders. Deduce the A-before-B probability including empty sets.
3. Deterministic path geometry: component-index constancy inside graph edges and strict increments outside; component sorting preserves each component's label set and is increasing there. Express retained intercomponent indicators using separation of the two entire components. Prove disjointness for equal-parity component-pair supports and bound their number by |H|.
4. Analytic finite machinery: Bernoulli centered MGF, product MGF on independent sets, finite weighted Cauchy–Schwarz between the two parity classes, Markov optimization with B>0, and constant statistic when B=0. Preserve the exact frozen exp(-t²/M) constant.
5. Clipped expectation: inject partial components into integer boundary edges; bound bad retained intercomponent edges by twice the partial count; prove the binomial deficit at small sizes and the automatic large-size case; charge full-component internal edges at most twice while retaining every internal graph edge, including clipped ones.
6. Uniform scan and conditional comparison: uniform two-position symmetry gives exact mean; the edgeless component sort is identity; union over Fin(N+1). Derive the comparison FAILURE event by event inclusion and the lower tail. Deduce the two-sided bound by union.
7. Deterministic least successful translate with default on unsuccessful G. Finite source and codomain yield measurability under their discrete spaces. Choice depends on G and fixed geometry only.
8. Uniform asymptotics: for fixed D≥0, δ>0, M≥1 and M^δ≥max(576,24D), obtain Delta≥M^(1/2+δ)/12. Thus failure≤exp(-M^(2δ)/144). Choose N0≥1 before N,H0,G using M≥N^a. Separately show the uniform scan error (N+1)exp(-N^(aδ)) tends to zero. A generic graph-mixture event/TV consequence will explicitly retain any law-identity premise.

Every concrete target must discharge all abstract factorization, geometry and distribution inputs. No conditional intermediate theorem counts as one of the ten frozen target exports. The manuscript and other lane files remain read-only. Lane compilation is serialized via scripts/lane.py LB04 and preserves previous audit versions.
