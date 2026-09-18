# Independent final integration audit

Reviewer: threshold/hidden-assumption agent. Reviewed `RiffleLower/LowerBounds.lean` against frozen endpoints L01/L02 and their shared model, including the actual definitions in `FixedColumns.lean` and `Sorting.lean`.

**Mathematical and statement-level verdict: approve L01 and L02 exactly as implemented.** The integration file was awaiting the root's kernel build when this review was written; this report does not substitute for that build.

* `shuffleLaw` is the pushforward of the uniform law on `Fin K -> Perm (Fin N)`. Thus column randomizations are independent and have the prescribed multiset counts. No row-independence assumption is introduced.
* `inverseShuffle` stably sorts complete `Fin K -> Fin k` row words in lexicographic order. Its permutation maps sorted positions to original row labels; the proof uses this orientation consistently.
* L01 preserves every frozen assumption: `N>=2`, `1<=m<=N`, and the strict real inequality `m<wordMean c w`. Its conclusion is precisely the frozen finite TV lower bound with `(N-m+1)/m!`. Zero piles and `K=0` remain permitted.
* The repeated-word event is transferred to a genuinely observable contiguous increasing-run event using the proved stable-sort theorem. The witness is a complete word, never a proper prefix.
* The quantitative success estimate is obtained from the proved exact fixed-column moment/variance chain. The integration does not assume the desired success probability or invoke an unproved concentration theorem.
* L02 preserves arbitrary finite random environments and all frozen error/typical-set assumptions. Every environment is tested by the same increasing-run event with the same `m`; neither the word witness nor the environment is observed by the test.
* L02 applies `mixture_common_event` before the TV test. It does not average conditional TV distances. Its single uniform false-positive penalty is paid once, without an unnecessary factor equal to the number of environments.
* Neither endpoint claims a cold-spot asymptotic lower bound, matching cutoff, bridge localization, or exponential ascent concentration. Imports of the finite profile/cold modules do not turn those unfinished mathematical claims into hypotheses.

No mathematical correction to either endpoint is requested. No mathematical source was edited during this audit.

One ancillary signature observation, outside L01/L02: the current M02 declaration `uniform_pi_expect_prod` exposes `[DecidableEq T]`, while the frozen contract permits equality to be supplied classically. This is not a substantive mathematical restriction, but moving it to a local classical instance would make the exported assumption list match the frozen wording literally. The root was notified before final delivery.
