from pathlib import Path
import re, json, hashlib

scratch = Path(__file__).resolve().parent
intro = (scratch/'paper_intro.tex').read_text(encoding='utf-8')
upper = (scratch/'paper_upper.tex').read_text(encoding='utf-8')
lower = (scratch/'paper_lower.tex').read_text(encoding='utf-8')
before_proofs = {}
statements = {}

def relocate(text, env, label):
    pattern = r'\\begin\{'+env+r'\}(?:(?!\\end\{'+env+r'\}).)*?\\label\{'+re.escape(label)+r'\}.*?\\end\{'+env+r'\}'
    matches = list(re.finditer(pattern, text, re.S))
    assert len(matches) == 1, (label, len(matches))
    m = matches[0]
    statements[label] = m.group()
    tail = text[m.end():]
    p = re.search(r'\\begin\{proof\}(.*?)\\end\{proof\}',tail,re.S)
    assert p and not tail[:p.start()].strip(), label
    before_proofs[label] = hashlib.sha256(p.group(1).encode()).hexdigest()
    title = 'Corollary' if env == 'corollary' else 'Theorem'
    tail = tail[:p.start()] + tail[p.start():].replace(r'\begin{proof}',r'\begin{proof}[Proof of '+title+r'~\ref{'+label+'}]',1)
    return text[:m.start()] + tail

for env,label in [('theorem','thm:upper-empirical'),('theorem','thm:upper-profile'),('corollary','cor:upper-critical')]:
    upper = relocate(upper,env,label)
for label in ['thm:empirical-lower','thm:macroscopic-lower']:
    lower = relocate(lower,'theorem',label)

profile = statements['thm:upper-profile'].replace(r'\beta(T)',r'\Lambda_0(T)')
profile = profile.replace('every regular Borel partition of\nmesh', 'every regular Borel partition $\\mathcal P$ of\nmesh')
profile = profile.replace('$(\\mu,T,\\rho,\\varphi)$-almost like the profile', '$(\\mathcal P,\\rho,\\varphi)$-almost like $\\mu$ on $[0,T]$')
macro = statements['thm:macroscopic-lower']
macro = macro.replace('Fix $\\eta>0$.', 'Fix $k\\ge2$, $T>0$ and $\\eta>0$.')
macro = macro.replace('conditions of Proposition~\\ref{prop:profile-transfer}', 'condition~\\eqref{eq:scalar-integrability} on $[0,T]$')
macro = macro.replace('and all cut arrays which are', 'and all cut arrays with $K=\\lfloor T\\log N\\rfloor$ which are')
macro = macro.replace('$(\\mathcal R,\\rho,\\varphi)$-almost-profile-like', '$(\\mathcal R,\\rho,\\varphi)$-almost like $\\mu$ on $[0,T]$')
empirical_lower = statements['thm:empirical-lower']
empirical_lower = empirical_lower.replace('Fix positive margins', 'Fix $k\\ge2$, $T>0$, positive margins')
empirical_lower = empirical_lower.replace('and all deterministic cut arrays have', 'and all deterministic cut arrays with $K=\\lfloor T\\log N\\rfloor$ have')
critical = statements['cor:upper-critical'].replace(r'\beta(T)',r'\Lambda_0(T)')
critical = critical.replace(r'\begin{corollary}',r'\begin{corollary}[Critical-time upper bound]',1)

start = intro.index(r'\subsection{Main results}')
end = intro.index(r'\subsection{Consequences and discussion}')
main = r'''\subsection{Main results}

Fix $k\ge2$ and $N\ge2$. All logarithms are natural. A cut array
consists of nonnegative integers $n_i^{(j)}$ with
$\sum_{i=0}^{k-1}n_i^{(j)}=N$. Write
$p^{(j)}=(n_0^{(j)},\ldots,n_{k-1}^{(j)})/N$ for its pile proportions.
Let $P_N^K$ denote the law of the inverse of the chronological
composition of the first $K$ shuffles, started from the identity deck,
and let $\nuUnif$ be uniform on permutations of $N$ cards.
Inversion preserves total variation, so every bound below also holds
for the forward shuffle. We write $\dTV$ for total-variation distance.

For $p\in D_k=\{p\in[0,1]^k:\sum_i p_i=1\}$, write
\[
 a_p=\log\frac1{\max_i p_i},\qquad
 \psi_p(\theta)=-\log\sum_i p_i^\theta.
\]
A time profile $(\mu_t)$ is a family of probability measures on $D_k$.
Let $A(r,s)=\int_r^s\E_{\mu_t}a_p\,dt$ and
$B_\theta(r,s)=\int_r^s\E_{\mu_t}\psi_p(\theta)\,dt$.
The two relevant margins are
\begin{align*}
 \Lambda_0(T)&=1-A(0,T),\\
 \Lambda_1(T)&=\sup_{0\le s\le u\le T}\inf_{\theta\in[3,4]}
 \left\{\frac{\theta+3}{2}\bigl(1-A(0,s)\bigr)
       -B_\theta(s,u)-2B_2(u,T)\right\}.
\end{align*}

A column is $g$-good if two distinct piles each contain at least
$gN$ cards. The local $(g,\gamma,\rho)$-good condition on $[r,T]$
requires at least $\gamma\rho\log N$ good columns with
$j/\log N\in[a,a+\rho]$, for every real $a$ with
$[a,a+\rho]\subseteq[r,T]$.
Regular partitions, scalar integrability, and almost-likeness mean
\eqref{eq:partition-regularity}, \eqref{eq:scalar-integrability}, and
\eqref{eq:almost-like}, respectively. The same selected partition is
used in these conditions. Almost-likeness asks that its cell frequencies
on each $\rho$-grid interval approximate the integrated profile masses,
with error at most $\varphi$ times the interval length plus $1/\log N$.

Our main upper and lower bounds apply on opposite sides of the zero
margin. Their proofs are given in Sections~\ref{sec:upper-bound}
and~\ref{sec:lower-bound}.

''' + profile + '\n\n' + macro + r'''

The finite-array versions of these results use the actual sequence of
pile sizes. Put $S_N=K/\log N$ and let $p_N(t)=p^{(j)}$ on
$((j-1)/\log N,j/\log N)$. Define
\[
 A^{(N)}(r,s)=\int_r^s a_{p_N(t)}\,dt,\qquad
 B^{(N)}_\theta(r,s)=\int_r^s\psi_{p_N(t)}(\theta)\,dt
 \quad(0\le r\le s\le S_N),
\]
and
\begin{align*}
 \beta^{(N)}(s)&=1-A^{(N)}(0,s),\\
 \Lambda_1^{(N)}&=\sup_{0\le s\le u\le S_N}\inf_{\theta\in[3,4]}
 \left\{\frac{\theta+3}{2}\beta^{(N)}(s)
       -B^{(N)}_\theta(s,u)-2B^{(N)}_2(u,S_N)\right\}.
\end{align*}
For the upper bound, empirical margin at least $\eta$ means
$\beta^{(N)}(S_N)\le-\eta$ and that the expression after the supremum
in this display is at most $-\eta$ for every grid pair
$s=i/\log N$, $u=j/\log N$, $0\le i\le j\le K$.
The lower bound uses the displayed supremum over all real endpoints.

''' + statements['thm:upper-empirical'] + '\n\n' + empirical_lower + '\n\n'
intro = intro[:start] + main + intro[end:]
old_start = intro.index('For a consistent sequence of cuts admitting arbitrarily fine local')
old_end = intro.index('Uniformity in the cut array also gives the random-pile upper bound.')
intro = intro[:old_start] + critical + r'''

The lower bound applies at every time with a strictly positive margin
and the specified approximation conditions.

''' + intro[old_end:]

upper = upper.replace(r'\section{Upper bound}',r'\section{Upper bound}\label{sec:upper-bound}',1)
lower = lower.replace(r'\section{Lower bound}',r'\section{Lower bound}\label{sec:lower-bound}',1)

after_proofs = {}
for label in before_proofs:
    combined = upper+'\n'+lower
    match = re.search(r'\\begin\{proof\}\[Proof of (?:Theorem|Corollary)~\\ref\{'+re.escape(label)+r'\}\](.*?)\\end\{proof\}',combined,re.S)
    assert match, label
    after_proofs[label] = hashlib.sha256(match.group(1).encode()).hexdigest()
assert before_proofs == after_proofs

for name,content in [('paper_intro.tex',intro),('paper_upper.tex',upper),('paper_lower.tex',lower)]:
    (scratch/name).write_text(content,encoding='utf-8')
(scratch/'paper_relocation_audit.json').write_text(json.dumps({'moved_statements':list(statements),'proof_bodies_unchanged':before_proofs==after_proofs,'proof_body_hashes':after_proofs},indent=2),encoding='utf-8')
print('Moved five main statements into the introduction; all five proof bodies are unchanged.')
