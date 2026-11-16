"""Independent exhaustive arithmetic audit of frozen LB-01 definitions.

This is a counterexample search and regression check, not a Lean proof.
Permutations are tuples mapping sorted/output position to original label.
Run from any directory; the JSON report is written beside this script.
"""
from collections import Counter, defaultdict
from itertools import permutations, product
from math import factorial, prod
from pathlib import Path
import json


def compose(f, g):
    return tuple(f[g[i]] for i in range(len(f)))


def inverse(p):
    q = [0] * len(p)
    for i, j in enumerate(p):
        q[j] = i
    return tuple(q)


def stable_sort(f):
    return tuple(sorted(range(len(f)), key=lambda i: (f[i], i)))


def matrix_sort(cols, n):
    return stable_sort(tuple(tuple(col[i] for col in cols) for i in range(n)))


def words(cols, n):
    return tuple(tuple(col[i] for col in cols) for i in range(n))


def graph_from_sorted_keys(keys):
    return tuple(keys[i] == keys[i + 1] for i in range(len(keys) - 1))


def components(graph, n):
    if not n:
        return ()
    blocks, start = [], 0
    for i, edge in enumerate(graph):
        if not edge:
            blocks.append(tuple(range(start, i + 1)))
            start = i + 1
    return tuple(blocks + [tuple(range(start, n))])


def component_sort(graph, p):
    result = []
    for block in components(graph, len(p)):
        result.extend(sorted(p[i] for i in block))
    return tuple(result)


def shared_component_sort(graph, p):
    indices = tuple(sum(not graph[e] for e in range(i)) for i in range(len(p)))
    return compose(p, stable_sort(tuple((indices[i], p[i]) for i in range(len(p)))))


def physical_inverse(cols, n):
    deck = tuple(range(n))
    for col in cols:
        deck = compose(deck, inverse(stable_sort(col)))
    return inverse(deck)


def pulled_columns(cols, n):
    """Inverse steps in reverse time, pulling current-position digits to labels."""
    deck, pulled = tuple(range(n)), [None] * len(cols)
    for j in reversed(range(len(cols))):
        deck_inv = inverse(deck)
        pulled[j] = tuple(cols[j][deck_inv[label]] for label in range(n))
        deck = compose(deck, stable_sort(cols[j]))
    assert deck == physical_inverse(cols, n)
    return tuple(pulled)


def profile(cols, k):
    return tuple(tuple(col.count(a) for a in range(k)) for col in cols)


def report_example(n, k, cols, **extra):
    return {"N": n, "k": k, "columns": cols, "profile": profile(cols, k), **extra}


report = {
    "kind": "exhaustive finite arithmetic checks; not formal proof",
    "fixtures": [],
    "generic_graph_checks": 0,
    "profile_law_checks": 0,
    "full_multiset_fiber_checks": 0,
    "sample_checks": 0,
    "counterexamples_to_stronger_or_wrong_claims": {},
}

graph_cache = {}
for n in range(6):
    perms = tuple(permutations(range(n)))
    for graph in product((False, True), repeat=max(0, n - 1)):
        law = Counter(component_sort(graph, p) for p in perms)
        fiber_size = prod(factorial(len(c)) for c in components(graph, n))
        assert set(law.values()) == {fiber_size}
        assert all(shared_component_sort(graph, p) == component_sort(graph, p) for p in perms)
        if not any(graph):
            assert all(component_sort(graph, p) == p for p in perms)
        if n and all(graph):
            assert set(law) == {tuple(range(n))}
        graph_cache[n, graph] = law
        report["generic_graph_checks"] += len(perms)

fixtures = sorted(set(
    [(n, k, K) for n in range(5) for k in range(3) for K in range(4)]
    + [(n, 3, K) for n in range(5) for K in range(3)]
    + [(3, 3, 3), (5, 2, 2)]
))
for n, k, K in fixtures:
    columns = tuple(product(range(k), repeat=n))
    profiles = defaultdict(list)
    for cols in product(columns, repeat=K):
        profiles[profile(cols, k)].append(cols)
    report["fixtures"].append({"N": n, "k": k, "K": K, "profiles": len(profiles),
                               "samples": sum(map(len, profiles.values()))})
    for counts, samples in profiles.items():
        matrix, physical, wrong_time, graphs = Counter(), Counter(), Counter(), Counter()
        multisets = defaultdict(Counter)
        pulled = set()
        for cols in samples:
            ws = words(cols, n)
            s = matrix_sort(cols, n)
            sorted_ws = tuple(ws[i] for i in s)
            graph = graph_from_sorted_keys(sorted_ws)
            p = physical_inverse(cols, n)
            newcols = pulled_columns(cols, n)
            assert profile(newcols, k) == counts
            assert matrix_sort(newcols, n) == p
            pulled.add(newcols)
            matrix[s] += 1
            physical[p] += 1
            wrong_time[matrix_sort(tuple(reversed(cols)), n)] += 1
            graphs[graph] += 1
            multisets[sorted_ws][s] += 1
            report["sample_checks"] += 1
            if p != s and "pointwise_physical_equals_matrix" not in report["counterexamples_to_stronger_or_wrong_claims"]:
                report["counterexamples_to_stronger_or_wrong_claims"]["pointwise_physical_equals_matrix"] = report_example(
                    n, k, cols, physical_inverse=p, matrix_sort=s, pulled_columns=newcols)
            for depth in range(K + 1):
                for prefix in product(range(k), repeat=depth):
                    lo = sum(w[:depth] < prefix for w in ws)
                    hi = sum(w[:depth] <= prefix for w in ws)
                    positions = tuple(i for i, w in enumerate(sorted_ws) if w[:depth] == prefix)
                    assert positions == tuple(range(lo, hi))
        assert matrix == physical
        assert pulled == set(samples)
        mixture = Counter()
        for graph, multiplicity in graphs.items():
            for p, fibers in graph_cache[n, graph].items():
                mixture[p] += multiplicity * fibers
        assert mixture == Counter({p: count * factorial(n) for p, count in matrix.items()})
        if matrix != wrong_time and "earlier_and_later_priority_same_law" not in report["counterexamples_to_stronger_or_wrong_claims"]:
            p = next(p for p in set(matrix) | set(wrong_time) if matrix[p] != wrong_time[p])
            report["counterexamples_to_stronger_or_wrong_claims"]["earlier_and_later_priority_same_law"] = {
                "N": n, "k": k, "profile": counts, "permutation": p,
                "earlier_priority_numerator": matrix[p], "later_priority_numerator": wrong_time[p],
                "denominator": len(samples)}
        for sorted_ws, actual in multisets.items():
            graph = graph_from_sorted_keys(sorted_ws)
            fibers = prod(factorial(m) for m in Counter(sorted_ws).values())
            assert set(actual.values()) == {1}
            assert len(actual) * fibers == factorial(n)
            assert graph_cache[n, graph] == Counter({p: count * fibers for p, count in actual.items()})
            report["full_multiset_fiber_checks"] += 1
        report["profile_law_checks"] += 1

# Nonindependent pi can fail even when its marginal is uniform.
# Two generic path graphs (True,False) and (False,True), each with
# probability 1/2, correlate with the six permutations using the first
# three and last three in lexicographic order, respectively.
perms = tuple(permutations(range(3)))
graph_a, graph_b = (True, False), (False, True)
dependent = Counter(component_sort(graph_a if i < 3 else graph_b, p) for i, p in enumerate(perms))
independent = Counter()
for graph in (graph_a, graph_b):
    independent.update(component_sort(graph, p) for p in perms)
assert Counter({p: count * 2 for p, count in dependent.items()}) != independent
report["counterexamples_to_stronger_or_wrong_claims"]["independence_omitted"] = {
    "N": 3, "graphs": [graph_a, graph_b], "uniform_pi_correlated_by_lex_halves": True,
    "dependent_counts_denominator_6": [[p, count] for p, count in sorted(dependent.items())],
    "independent_counts_denominator_12": [[p, count] for p, count in sorted(independent.items())]}
report["status"] = "PASS"
output = Path(__file__).with_name("hypotheses_small_model_results_v1.json")
output.write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps({key: value for key, value in report.items() if key != "fixtures"}, indent=2))
