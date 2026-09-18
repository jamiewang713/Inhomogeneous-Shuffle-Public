# A03–A04 implementation coverage

Implementation: `lean_formalization/RiffleProfiles/TailLimits.lean`.
SHA-256: `c5e2b0a3a523d4d8ad6acf8ba7401b22bdc5c1bdbe5ed22576a00afffccb8b76`.
Contract: `FROZEN_ASYMPTOTIC_CONTRACT.md`, frozen SHA-256
`7074bcb2888043662af650e8c390e3a7c36edba602c13786a9604d1397fcefb1`.

The implementation adds exactly the two public conclusions assigned to
this module. It imports the unchanged, checked A01/cutoff interface in
`RiffleProfiles.AsymptoticFinite`.

| Frozen statement | Public declaration | Coverage |
| --- | --- | --- |
| A03 | `RiffleProfiles.boundary_tailWeight_small_chi` | For natural `k`, `T>=0`, `C>0`, and `epsilon>0`, supplies `0<chi0<1` before all `chi,N,K`. The tail threshold is exactly `floor((C/chiLog chi)*logScale N)+1`, weight exactly `k*chi`, and conclusion exactly `N*tailWeight <= N^(1-C+epsilon)`. |
| A04 | `RiffleProfiles.exceptional_tailWeight_small_chi` | For natural `k`, `T>=0`, and arbitrary real `C0`, supplies `0<chi0<1` before all `chi,N,K`. The threshold is exactly `floor(exceptionalAllowance chi*logScale N)+1`, weight exactly `k*(3*chi)`, and conclusion exactly `N*tailWeight <= N^(-C0)`. |

Both declarations require only `N>=2` and `K<=T*logScale N` after the
parameter choice. The domain permits `k=0`, `T=0`, and `K=0`. No
positivity of a pile count, partition hypothesis, or stochastic law is
introduced.

## Derived helpers and proof structure

Two private helpers implement the reviewed catalogue:

* `exponential_error_cutoff A delta eta` retains local assumptions
  `A>=0`, `delta>0`, `eta>0` and proves existence of `U>=1` with
  `A*exp(-delta*u)<=eta` for every `u>=U`. It uses mathlib's exponential
  limit and the eventual-at-top characterization. There is no division
  by `A`, so its zero case is included.
* `exceptional_exponent_cutoff A C0` retains `A>=0` and unrestricted
  real `C0`. It proves an eventual upper bound `-C0` for
  `1+A*exp(-u/2)-sqrt(u)/2`. After the exponential error is at most
  one, a squared maximum supplies the explicit square-root cutoff.
  No positivity assumption on `C0` is needed.

A03 sets `delta=min(1/2,epsilon/(2*C))`, chooses the exponential cutoff
with `A=T*k` and tolerance `epsilon/2`, and obtains `chi0` from the
shared `exists_chiLog_cutoff`. It applies A01 at
`z=exp((1-delta)*chiLog chi)`. The identities for `chi*z` and the
boundary exponent are proved before using `log(1+x)<=x`. Power
monotonicity gives the exact conclusion.

A04 uses the second helper with `A=3*T*k`, applies A01 at
`z=exp(chiLog chi/2)`, and proves the cancellation
`exceptionalAllowance chi * log(z) = sqrt(chiLog chi)/2` using the
strict positivity of `chiLog chi`. It retains the factor `N` in A01
throughout. All cancellations occur on proved positive logarithms or
square roots; no zero-log convention is used as a positivity shortcut.

## Validation

The command

`python3 lean_formalization/check_lean.py lean_formalization/RiffleProfiles/TailLimits.lean`

completed successfully with exit code zero and `warningAsError=true`
under the project's pinned Lean 4.19/mathlib runtime. The compiled
`.olean` is available to downstream modules. The source contains no
`axiom`, `sorry`, `admit`, or placeholder declaration. A separate root
audit will report kernel axiom dependencies for the integrated batch.

No frozen contract, source definition, or other agent's implementation
was changed. No remaining A03/A04 proof obligation is deferred by this
module.
