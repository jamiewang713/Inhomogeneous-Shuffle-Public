# Independent comparison of the T09 union proof repair

The original rewrite tactic could not identify two extensionally identical finite-row predicates because union membership and its decision instances were elaborated differently. Root asked both the representation and adversarial agents for an independent proof-only repair.

The adversarial agent checked the unchanged theorem with `simpa only [Set.mem_union]` applied to the exact expected-count identity followed by its union bound. This compiled with warnings as errors. The representation agent independently confirmed the diagnosis, rejected its first narrower decision-instance-only rewrite, and approved normalization of union membership.

The final implementation uses the checked normalization. Its theorem statement, event, law, bound, and all assumptions are unchanged. No new mathematical intermediate statement was introduced.
