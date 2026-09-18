# What the result means in the complete article

This clarification follows a whole-file review of the authorized TeX, comparison with the two authorized PDFs, and a further independent mathematical review. No source assumptions or theorem statements were changed. No Lean file was written, modified, or tested by this recovery task.

## The source-level recovery target

The context identifies the intended local result: **component-sorting ascent concentration**, labelled **lem:permutation-bd**, at TeX lines 4979–4995.

The false statement **lem:block-bd** is a proposed helper. Its only reference is at line 5018, in the proof of component-sorting concentration. The concentration lemma's only reference is at line 5097, in the Lalley component comparison. Thus the relevant mathematical target can be identified without asking the user to supply a label. This does not identify or certify a particular existing Lean declaration.

The dependency chain is:

1. Component-sorting ascent concentration, **lem:permutation-bd**.
2. Expected ascent excess and high-probability detection, **lem:lalley-comparison**.
3. A test scanning deterministic translates, **lem:lalley**.
4. The cold-spot lower bound, **prop:cold-lower**.
5. The buffered reduced lower bound, **thm:buffered-reduced-lower-bound**.

The earlier inability to identify a mathematical target is superseded by this contextual reading. The false general helper remains a mathematical obstruction to the proof as written.

## Exact objects and probability law

The common setup at lines 87–123 defines the shuffle law as the law of the **inverse** shuffle. Thus the graph representation and the ascent test use the same permutation convention.

Fix a deterministic subgraph \(G\) of the path on \([N]\), and a deterministic subset \(H\subseteq[N]\). The source defines

\[
E(H)=\{(i,i+1):i,i+1\in H\},
\qquad
\partial H=\{(i,i+1):\mathbf 1_H(i)\ne\mathbf 1_H(i+1)\}.
\]

The TeX uses an edge boundary in the integer path. This differs from the vertex-boundary convention on page 37 of 2103.05068v3.pdf; these conventions must not be silently identified in Lean.

Take a uniformly random permutation \(\pi\in\mathfrak S_N\). Sort its values increasingly inside each connected component of \(G\), giving \(\pi_G\), and set

\[
X_{G,H}(\pi)
=\#\{(i,i+1)\in E(H):\pi_G(i)<\pi_G(i+1)\}.
\]

The concentration claim is that an absolute \(c>0\) works uniformly in \(N,G,H,M\):

\[
\mathbb P_\pi\!\left(
 |X_{G,H}-\mathbb E_\pi X_{G,H}|\ge t
\right)
\le 2\exp(-c\,t^2/M).
\]

The printed hypotheses are \(|H|\le M\) and \(|\partial H|=O(\sqrt M)\). The displayed quotient is intended on \(M>0\), and concentration thresholds are intended to satisfy \(t\ge0\); neither domain is printed explicitly. The actual application supplies \(M\ge N^a\), with fixed \(a>0\). The asymptotic boundary condition means \(|\partial H|\le D\sqrt M\) for a fixed constant \(D\), uniformly over the relevant family.

These domain and uniformity interpretations are recorded explicitly here, and have not been silently inserted into a frozen Lean statement.

The probability in this lemma concerns only the fresh uniform permutation. Later, \(G\) is random: one conditions on its realization before applying this deterministic result. The translate \(H_q\) may be selected using \(G\), because the bound is uniform in \(G,H_q\) and the fresh permutation is independent of \(G\).

## Why this is what the lower bound needs

Put \(e=|E(H)|\), \(r=|E(G)\cap E(H)|\), and \(d=|\partial H|\). Each of the \(r\) internal graph edges is forced to be an ascent. Ordinary uniform comparisons have ascent probability \(1/2\). Sorting can also decrease ascent probabilities at component boundaries, so counting only forced ascents is insufficient.

The expectation comparison at lines 5064–5094 is

\[
\mathbb E_\pi X_{G,H}\ge e/2+r/6-O(d).
\]

For adjacent full components of sizes \(a,b\), the boundary ascent probability and its deficit satisfy

\[
p(a,b)=\binom{a+b}{a}^{-1},
\qquad
\frac12-p(a,b)\le\frac{(a-1)+(b-1)}6.
\]

Each component is charged at most twice. Clipped components require care: retain their internal ascents and discard only boundary comparisons incident to them. Discarding whole clipped intersections, as the source's prose suggests, need not cost \(O(d)\). With the edge-boundary convention above, the repaired counting argument gives the safe finite inequality

\[
\mathbb E_\pi X_{G,H}\ge e/2+r/6-d.
\]

If \(d\le D\sqrt M\) and \(r\ge M^{1/2+\delta}\), the expected excess eventually dominates both the boundary loss and the fluctuations of order \(\sqrt M\). The ascent count therefore exceeds the uniform baseline by \(M^{1/2+\delta/2}\) with probability tending to one.

The cold set has a random global location. The article tests all \(N+1\) translates \(H_q=(q+H_0)\cap[N]\). Under uniformity, each false-positive probability decays exponentially in a positive power of \(M\), so their union still has probability tending to zero when \(M\ge N^a\). Under the shuffle law, the many-cold-edges lemma supplies a successful translate with probability tending to one. This separation gives total variation distance tending to one.

Thus the local result converts **many collision edges** into **an observable excess of ascents**.

## Why the literal helper remains false

The coordinate condition in **lem:block-bd** fixes every other relevant value set. A Doob martingale step fixes only the sets already exposed. Changing the next exposed set changes the conditional distribution of later relevant sets, and the printed condition does not control this effect.

This failure persists with a nonempty reservoir. Take \(N=3\), with singleton \(V_1,V_2,V_0\). List their values in that order and define:

| Assignment | \(f\) |
|---|---:|
| \((1,2,3)\) | 0 |
| \((3,2,1)\) | 1 |
| \((1,3,2)\) | 1 |
| \((3,1,2)\) | 2 |
| \((2,3,1)\) | 2 |
| \((2,1,3)\) | 3 |

Every permissible change of one relevant block, keeping the other fixed and adjusting the reservoir, changes \(f\) by one. Thus \(L_1=L_2=1\) satisfies the hypothesis, but

\[
\mathbb Ef=3/2,\qquad
\mathbb P(|f-3/2|\ge3/2)=1/3>2e^{-9/4}.
\]

The strict exponential comparison follows from

\[
e^{9/4}\ge
1+\frac94+\frac{(9/4)^2}{2}+\frac{(9/4)^3}{6}
=\frac{983}{128}>6.
\]

No surrounding hypothesis eliminates this dependence problem. The specialized ascent function has additional structure that an arbitrary \(f\) lacks.

## Two distinct proof routes for the needed concentration

These are mathematical reconstruction routes, not Lean-tested proofs.

**Direct finite counting.** Order the graph components \(C_1,\ldots,C_q\) from left to right. Internal graph edges contribute deterministically. Each other relevant boundary contributes

\[
B_j=\mathbf 1\{\max\pi(C_j)<\min\pi(C_{j+1})\}.
\]

Split boundaries by the parity of the component index \(j\). Within one parity, the sets \(C_j\cup C_{j+1}\) are disjoint. Their induced relative orders are independent and uniform: for prescribed relative orders on disjoint position sets of sizes \(d_1,\ldots,d_s\), exactly \(N!/\prod_i d_i!\) permutations realize them. This is a finite counting statement, not independence of component value sets.

Apply Hoeffding separately to the two sums. There are at most \(M\) relevant boundaries, giving

\[
\mathbb P(|X-\mathbb EX|\ge t)
\le\min\{1,4e^{-t^2/(2M)}\}
\le2e^{-t^2/(4M)}.
\]

The parity here is the **component index**, unlike the position parity in the uniform-permutation scan test.

**Abstract independent-key representation.** Give each position an independent atomless uniform key. Ranking all keys produces a uniform permutation. Group keys by graph component; these vectors are independent. Ranking and sorting preserve the comparisons defining \(X\).

Only components incident to a relevant intercomponent comparison affect the random part of \(X\), and there are at most \(2M\). Replacing one component's key vector changes at most two indicators. Independent bounded differences yields the same bound with \(c=1/4\). Independence belongs to a proved alternative representation, not to the original disjoint value sets.

Both routes prove a stronger concentration helper without a boundary-size condition. The original target can retain its printed condition. Neither route requires a new shuffle-model assumption. Formalization must prove the finite-counting or rank-law dependency and apply trusted concentration results; neither dependency may be inserted as an axiom or placeholder.

## Meaning of the whole article's result

Write \(L(T)=\max\{\Lambda_0(T),\Lambda_1(T)\}\). Under the profile and local-good-shuffle hypotheses, the active statements aim to give, at \(K=\lfloor T\log N\rfloor\),

\[
L(T)\le-\eta\ \Longrightarrow\
d_{\rm TV}(P(n,K),\nu_{\rm Unif})\to0,
\]

\[
L(T)\ge\eta\ \Longrightarrow\
d_{\rm TV}(P(n,K),\nu_{\rm Unif})\to1
\qquad(\eta>0\text{ fixed}).
\]

Here \(\Lambda_0(T)=1-A(0,T)\) measures survival of a largest-prefix block. The optimized margin \(\Lambda_1\) detects the cold-collision mechanism. Auxiliary margins are dominated by \(\Lambda_0\). The displayed results do not settle the zero-margin case or behavior at the critical time.

The active random-pile-size upper bound is obtained by conditioning and averaging at lines 1999–2011. The random-pile-size lower bound needs one common test over typical pile sequences; merely averaging deterministic total variation lower bounds is invalid. The old overview at lines 2562–2785, including its random lower claim, is commented out. The intended union-test method appears in 2510.22783v1.pdf, Lemmas 6.5–6.6, page 53.

The exact failed dependency is the passage from reservoir-coordinate oscillation to a bound on Doob conditional ranges. The needed replacement is a valid proof of component-sorting ascent concentration. This clarification does not certify the rest of the article: the separate occupancy and upper-exploration issues recorded in REPORT.md remain.
