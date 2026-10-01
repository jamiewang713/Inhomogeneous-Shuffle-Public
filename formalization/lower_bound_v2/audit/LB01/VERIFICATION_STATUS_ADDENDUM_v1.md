# LB-01 verification metadata correction

LB-00's independent receipt review identified stale ownership statuses in `VERIFICATION_v1.json.required_targets_checked`. Those eight entries copied `PENDING` from the immutable LB-00 ownership inventory, although the same verification run checked that each named declaration exists as a theorem with its exact required type. The top-level verification result, compiled logs and completed-input receipt already correctly reported the proofs as verified/proved.

`VERIFICATION_v2.json` corrects only these eight status strings to `PROVED` and records its relationship to v1. No Lean source, theorem statement, build result or axiom closure changed. Every original audit, the v1 completed-input receipt and the frozen ownership record are preserved. `COMPLETED_INPUT_v1.json.required_exports` already has the correct status for all eight targets and remains valid.

Use the v2 verification metadata together with the original build logs and compiled declaration inventory. This is a visible metadata correction, not a change to the mathematical scope or the completed-input claim.
