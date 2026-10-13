from pathlib import Path
import csv
import json
import re
from collections import Counter

root = Path(__file__).resolve().parent.parent
scratch = root / 'tmp'
parts = ['paper_intro.tex', 'paper_setup.tex', 'paper_model.tex', 'paper_upper.tex', 'paper_lower.tex']
text = '\n\n'.join((scratch / name).read_text(encoding='utf-8-sig') for name in parts)
# Use the source article's notation for the tilted distribution and its costs.
text = text.replace('q_i(p,\\theta)', 'p_i^{[\\theta]}')
text = text.replace('j_p(\\theta)', 'I_p(\\theta)').replace('h_p(\\theta)', 'H_p(\\theta)')
text = text.replace('j_{p_N(t)}(\\theta)', 'I_{p_N(t)}(\\theta)')
text = text.replace('h_{p_N(t)}(\\theta)', 'H_{p_N(t)}(\\theta)')
text += r'''

\begin{thebibliography}{1}
\bibitem{SSW}
Mark Sellke, Jialu Shi, and Jiamin Wang.
\newblock Universality of cutoff for riffle shuffling.
\newblock \href{https://arxiv.org/abs/2510.22783v1}{arXiv:2510.22783v1}, 2025.
\end{thebibliography}
\end{document}
'''

# Preserve source correspondence in comments, without implementation names in
# the rendered article. The source map is also retained as a review artifact.
mapping = []
missing_maps = []
for filename in ['paper_setup_map.tsv', 'paper_model_map.tsv', 'paper_upper_map.tsv', 'paper_lower_map.tsv']:
    if not (scratch / filename).exists():
        missing_maps.append(filename)
        continue
    raw = (scratch / filename).read_text(encoding='utf-8-sig')
    if '\t' not in raw.splitlines()[0] and r'\t' in raw.splitlines()[0]:
        raw = raw.replace(r'\t', '\t')
    rows = list(csv.reader(raw.splitlines(), delimiter='\t'))
    for row in rows[1:]:
        if len(row) >= 3:
            mapping.append(row[:3])
by_label = {}
for label, path, declarations in mapping:
    by_label.setdefault(label, []).append((path, declarations))
for label, sources in by_label.items():
    token = '\\label{' + label + '}'
    if token in text:
        comments = '\n'.join('% Lean: ' + path + ' :: ' + decl for path, decl in sources)
        text = text.replace(token, comments + '\n' + token, 1)

out = root / 'time_inhomogeneous_riffle_shuffle_lean_paper.tex'
out.write_text(text, encoding='utf-8')
with (root / 'time_inhomogeneous_riffle_shuffle_lean_sources.tsv').open('w', encoding='utf-8', newline='') as f:
    writer = csv.writer(f, delimiter='\t')
    writer.writerow(['paper_label', 'Lean_source', 'Lean_declarations'])
    writer.writerows(mapping)

labels = re.findall(r'\\label\{([^}]+)\}', text)
refs = re.findall(r'\\(?:eqref|ref|[cC]ref)\{([^}]+)\}', text)
refs = [r.strip() for ref in refs for r in ref.split(',')]
duplicates = [x for x, n in Counter(labels).items() if n > 1]
missing = sorted(set(refs) - set(labels))
statements = []
for match in re.finditer(r'\\begin\{(theorem|lemma|proposition|corollary)\}(.*?)\\end\{\1\}', text, re.S):
    found = re.findall(r'\\label\{([^}]+)\}', match.group(2))
    statements.append({'kind':match.group(1),'labels':found,
                       'mapped':any(label in by_label for label in found)})
source_files_missing = sorted({path for _, path, _ in mapping if not (root / path).exists()})
report = {'file':str(out),'characters':len(text),'statements':statements,
          'missing_map_files':missing_maps,
          'duplicate_labels':duplicates,'missing_references':missing,
          'source_files_missing':source_files_missing,
          'sections':re.findall(r'\\section\{([^}]+)\}',text)}
(scratch / 'paper_structure_check.json').write_text(json.dumps(report,indent=2),encoding='utf-8')
print(json.dumps({key:value for key,value in report.items() if key!='statements'},indent=2))
print('Numbered statements:',len(statements))
print('Statements without mapping:',[s for s in statements if not s['mapped']])
