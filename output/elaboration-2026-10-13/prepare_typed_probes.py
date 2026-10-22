"""Prepare alternate explicit-argument candidates outside the active source tree."""
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
PROBES = HERE.parents[2] / 'elaboration-bench/probes'
original = (HERE / 'ab-13-future-bridge/original.txt').read_text(encoding='utf-8')
needle = '''    exact inducedMatrix_uniform cuts R (x a) ω₀
      (fun σ => F ((shuffleEdges σ).image (fun e => (lowerRank (x a) ω₀:ℤ)+e.val)))'''
variant = '''    exact inducedMatrix_uniform cuts R (x a) ω₀
      (fun (σ : Sample (inducedCuts cuts R (x a) ω₀)) =>
        F ((shuffleEdges σ).image (fun e => (lowerRank (x a) ω₀:ℤ)+e.val)))'''
assert original.count(needle) == 2
(PROBES / 'FutureGraphTyped.lean').write_text(original.replace(needle, variant), encoding='utf-8')
original = (REPO / 'formalization/lower_bound_v2/RiffleLowerV2/Witness/EmpiricalTilt.lean').read_text(encoding='utf-8')
needle = '  exact (continuous_empiricalIntegral _).comp (continuous_const.prodMk continuous_id)'
assert original.count(needle) == 3
for name, function in [('J', 'tiltedCost'), ('B', 'psi'), ('H', 'tiltedEntropy')]:
    variant = f'''  exact (continuous_empiricalIntegral (fun j => {function} (cuts.profile hpos j) a)).comp
    (continuous_const.prodMk continuous_id)'''
    original = original.replace(needle, variant, 1)
(PROBES / 'EmpiricalTiltTyped.lean').write_text(original, encoding='utf-8')
print('Prepared two typed-argument candidates outside the active roots')
