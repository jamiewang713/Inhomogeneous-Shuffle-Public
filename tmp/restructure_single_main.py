from pathlib import Path
import re
import json

root = Path(__file__).resolve().parent.parent
scratch = root / 'tmp'
source = root / 'time_inhomogeneous_riffle_shuffle_lean_paper.tex'
old = (scratch / 'paper_before_single_main_20261003.tex').read_text(encoding='utf-8-sig')
intro_start = old.index(r'\section{Introduction}')
body_start = old.index(r'\section{Preliminaries}')
old_intro = old[intro_start:body_start]
statements = {}
for env, label in [
    ('theorem', 'thm:upper-profile'),
    ('theorem', 'thm:macroscopic-lower'),
    ('theorem', 'thm:upper-empirical'),
    ('theorem', 'thm:empirical-lower'),
    ('corollary', 'cor:upper-critical'),
]:
    pattern = (r'\\begin\{' + env + r'\}(?:(?!\\end\{' + env +
               r'\}).)*?\\label\{' + re.escape(label) + r'\}.*?\\end\{' + env + r'\}')
    matches = list(re.finditer(pattern, old_intro, re.S))
    assert len(matches) == 1, label
    statements[label] = matches[0].group()

overview = old_intro[old_intro.index(r'\subsection{Proof Techniques and Challenges}'):]
overview = overview.replace(
    'has mean occupancy $N^{\\beta^{(N)}(S_N)}$; when this mean grows as a\npositive power of $N$, concentration',
    'has mean occupancy $N\\prod_{j=1}^K\\max_i p_i^{(j)}$, where\n$p^{(j)}=\\vec n^{(j)}/N$. When this mean grows as a positive power\nof $N$, concentration')
overview = overview.replace(
    'argument does not already apply, a fixed positive lower bound on\n$\\Lambda_1^{(N)}$ supplies times $s\\le u$ and a tilt',
    'argument does not already apply, the empirical form of the positive\ncold margin supplies times $s\\le u$ and a tilt')
overview = overview.replace(
    'sorting and a uniform bound for the translate scan complete the lower\nbound.',
    'sorting and a uniform bound for the translate scan complete the\ndeterministic lower bound.\n\n'
    'To handle random pile sizes, we take the union of these tests over all\n'
    'admissible deterministic cut sequences. There are only\n'
    '$\\exp(O((\\log N)^2))$ such sequences up to time $T\\log N$, while\n'
    'each cold-spot test has probability at most $\\exp(-N^c)$ of detecting\n'
    'a uniformly random deck, for one fixed $c>0$. Thus the union still\n'
    'has probability tending to zero under uniform measure. It detects\n'
    'the shuffled deck with probability tending to one whenever the\n'
    'realized cut sequence is admissible. This gives a single hypothesis\n'
    'test for the law averaged over the random pile sizes.')
overview = overview.replace(
    'For the first moment, we may assume the initial shuffle is good, so\nthat each of its piles leaves a positive fraction of the cards outside',
    'For the first moment, we may assume the initial shuffle is good, in\nthe sense that two piles each contain a positive fraction of the cards.\nThus each of its piles leaves a positive fraction of the cards outside')

intro = (scratch / 'single_main_intro.tex').read_text(encoding='utf-8')
text = old[:intro_start] + intro + '\n' + overview + old[body_start:]
for label, block in statements.items():
    kind = 'Corollary' if label.startswith('cor:') else 'Theorem'
    marker = r'\begin{proof}[Proof of ' + kind + r'~\ref{' + label + '}]'
    assert text.count(marker) == 1, label
    text = text.replace(marker, block + '\n\n' + marker, 1)

text = text.replace(
    'A time profile is a family $(\\mu_t)_{t\\in\\mathbb R}$ of probability\n'
    'measures on $D_k$. No regularity in $t$ is implicit in this definition.\n'
    'Whenever the scalar functions concerned are integrable, write',
    'The deterministic profile estimates below also apply to families\n'
    '$(\\mu_t)$ of probability measures on $D_k$ under only the stated\n'
    'scalar integrability assumptions. In this part of the argument we do\n'
    'not require the full measurability assumed in the introduction.\n'
    'Whenever the scalar functions concerned are integrable, write')

needle = (' 0\\le\\Lambda_1(S)-\\Lambda_1(T)\\le8\\log k\\,(T-S).\n'
          '\\end{equation}\n\\end{lemma}')
replacement = (' 0\\le\\Lambda_1(S)-\\Lambda_1(T)\\le8\\log k\\,(T-S).\n'
               '\\end{equation}\n'
               'More precisely,\n'
               '\\begin{equation}\\label{eq:strict-margin-decrease}\n'
               ' \\Lambda_0(T)=\\Lambda_0(S)-A(S,T),\\qquad\n'
               ' \\Lambda_1(T)\\le\\Lambda_1(S)-2A(S,T).\n'
               '\\end{equation}\n\\end{lemma}')
assert needle in text
text = text.replace(needle, replacement, 1)
needle = ('suprema give $\\Lambda_1(T)\\le\\Lambda_1(S)$. The same argument, with\n')
replacement = ('suprema give $\\Lambda_1(T)\\le\\Lambda_1(S)$. In fact, on the\n'
               'removed part of $[S,T]$, the three possible cost terms are\n'
               '$((\\theta+3)/2)a(t)$, $\\int\\psi_p(\\theta)\\,d\\mu_t(p)$,\n'
               'and $2\\int\\psi_p(2)\\,d\\mu_t(p)$. Each is at least $2a(t)$\n'
               'for $\\theta\\in[3,4]$. The clipped expression therefore exceeds\n'
               'the original one by at least $2A(S,T)$, proving\n'
               '\\eqref{eq:strict-margin-decrease}; its first identity follows\n'
               'directly from the definition of $\\Lambda_0$. The same argument, with\n')
assert needle in text
text = text.replace(needle, replacement, 1)

bridge = (scratch / 'random_profile_bridge.tex').read_text(encoding='utf-8')
bridge = bridge.replace('lem:random-profile-bridge', 'lem:randomized-profile-inputs')
bridge = '\\subsection{Randomized profiles and empirical estimates}\n\n' + bridge
needle = r'\subsection{Shuffle matrices}'
assert text.count(needle) == 1
text = text.replace(needle, bridge + '\n\n' + needle, 1)

ending = (scratch / 'random_lower_extension.tex').read_text(encoding='utf-8')
ending += '\n\n' + (scratch / 'single_main_proof.tex').read_text(encoding='utf-8')
needle = r'\begin{thebibliography}{1}'
assert text.count(needle) == 1
text = text.replace(needle, ending + '\n\n' + needle, 1)

new_intro = text[text.index(r'\section{Introduction}'):text.index(r'\section{Preliminaries}')]
assert new_intro.count(r'\begin{theorem}') == 1
assert r'\begin{corollary}' not in new_intro
for label, block in statements.items():
    assert text.count(block) == 1, label
labels = re.findall(r'\\label\{([^}]+)\}', text)
refs = re.findall(r'\\(?:eqref|ref)\{([^}]+)\}', text)
assert len(labels) == len(set(labels)), 'duplicate labels'
assert not set(refs) - set(labels), sorted(set(refs) - set(labels))
source.write_text(text, encoding='utf-8')
print(json.dumps({'intro_theorems': 1, 'relocated_statements': list(statements),
                  'new_support': ['lem:randomized-profile-inputs', 'eq:strict-margin-decrease',
                                  'cor:lower-random', 'thm:main'],
                  'missing_references': [], 'duplicate_labels': []}, indent=2))
