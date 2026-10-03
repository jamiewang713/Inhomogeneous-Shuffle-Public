"""Exact finite model checks. Supplemental adversarial evidence, not Lean proofs."""
from itertools import permutations, product
from collections import defaultdict, Counter
from fractions import Fraction as F
from math import comb, exp, log
import json
from pathlib import Path

def columns(counts):
    return sorted(set(permutations(tuple(a for a,c in enumerate(counts) for _ in range(c)))))
def choose(n,k):
    return comb(n,k) if 0 <= k <= n else 0

def check_case(name, counts, M, x, side, j, witness=None):
    n=sum(counts[0]); d=len(counts); R=set(range(M)); g=F(n-M,n)
    allcols=[columns(c) for c in counts]
    groups={}; count=good_count=larger_count=0
    p=lambda t,a: F(counts[t][a],n)
    prefix=lambda hi: prod(p(t,x[t]) for t in range(hi))
    ell=lambda t: M*prefix(t)*sum(p(t,a) for a in range(x[t]))
    right=lambda t: M*prefix(t)*sum(p(t,a) for a in range(x[t]+1,len(counts[t])))
    for omega in product(*allcols):
        count+=1
        rows=list(zip(*omega)); rowpref=lambda r:rows[r][:len(x)]
        internal=tuple((r,rows[r]) for r in sorted(R) if rowpref(r)==x)
        low=sum(rowpref(r)<x for r in R); size=len(internal)
        T={r for r in R if rows[r][:j]==x[:j]}
        other=tuple(omega[t] for t in range(d) if t!=j)
        if side=='equal':
            E={r for r in range(n) if omega[j][r]==x[j]}
            A=E; B=T-E; D=set(range(x[j])); key=(other,tuple(sorted(E)))
            C=set(range(n))-R-E
            muB=M*prefix(j)*(1-p(j,x[j])); muC=(n-M)*(1-p(j,x[j]))
            good=(F(len(B))>=muB/2 and F(len(C))>=muC/2)
            target=g*min(ell(j),right(j))/8
        else:
            pred=(lambda suffix:suffix<x[j+1:]) if side=='lower' else (lambda suffix:suffix>x[j+1:])
            B={r for r in T if pred(rows[r][j+1:len(x)])}; A=T-B
            D=set(range(x[j]+1)) if side=='lower' else set(range(x[j]))
            key=(other,tuple((r,omega[j][r]) for r in sorted(A)))
            strict=(lambda a:a<x[witness]) if side=='lower' else (lambda a:a>x[witness])
            B0={r for r in R if all(rows[r][t]==x[t] for t in range(witness) if t!=j) and strict(rows[r][witness])}
            assert B0<=B
            shortpred=(lambda suffix:suffix<x[j+1:witness+1]) if side=='lower' else (lambda suffix:suffix>x[j+1:witness+1])
            sourceB={r for r in T if shortpred(rows[r][j+1:witness+1])}
            assert sourceB<=B
            larger_count+=bool(sourceB<B)
            witnessmean=M*prod(p(t,x[t]) for t in range(witness) if t!=j)*sum(p(witness,a) for a in range(len(counts[witness])) if strict(a))
            marked=sum(omega[j][r] in D for r in range(n) if r not in A)
            markedp=sum(p(j,a) for a in D)
            good=(F(len(B0))>=witnessmean/2 and F(marked)>=F(n-len(A))*markedp/2 and F(n-len(A)-marked)>=F(n-len(A))*(1-markedp)/2)
            witnessside=ell(witness) if side=='lower' else right(witness)
            opposite=right(j) if side=='lower' else ell(j)
            assert witnessmean*p(j,x[j])==witnessside
            target=g*witnessside*opposite/(8*M)
        N=n-len(A); K=sum(omega[j][r] in D for r in range(n) if r not in A); draws=len(B)
        Y=sum(omega[j][r] in D for r in B)
        shift=low-Y
        state=(N,K,draws,shift,size,internal,good)
        if key not in groups: groups[key]=(state,Counter())
        assert groups[key][0]==state, (name,'reveal measurability',state,groups[key][0])
        groups[key][1][Y]+=1
        variance=F(draws*K*(N-K)*(N-draws),N*N*(N-1)) if N>=2 else F(0)
        if good:
            good_count+=1
            assert variance>=target,(name,variance,target)
        assert low==shift+Y and low+size==shift+Y+size
        assert all(rows[r][t]==x[t] for r,_ in internal for t in range(len(x)))
    for (N,K,draws,shift,size,internal,good),hist in groups.values():
        total=sum(hist.values())
        den=comb(N,draws)
        for y in range(draws+1):
            assert F(hist[y],total)==F(choose(K,y)*choose(N-K,draws-y),den),(name,N,K,draws,y,hist)
    if side=='equal':
        scale=min(ell(j),right(j)); mult=2
    else:
        scale=min(witnessside,opposite); mult=3
    failure=F(count-good_count,count)
    upper=mult*exp(-((1-log(2))/2)*float(g*scale))
    assert float(failure)<=upper+1e-14
    return dict(name=name,n=n,d=d,M=M,prefix=list(x),case=side,selected_column=j,
                witness_column=witness,arrays=count,positive_fine_fibers=len(groups),
                good_arrays=good_count,enlarged_full_suffix_arrays=larger_count,
                exact_law='PASS',history_refinement='PASS',actual_variance_on_good='PASS',
                failure_probability=str(failure),source_failure_bound=upper)

def prod(xs):
    out=F(1)
    for x in xs: out*=x
    return out

results=[
    check_case('coincident maximizers; immediate join',[(2,2,2),(2,2,2)],4,(1,1),'equal',0),
    check_case('left maximizer later; immediate join',[(1,3,2),(3,2,1)],4,(1,1),'lower',0,1),
    check_case('right maximizer later; immediate join',[(1,4,1),(1,1,4)],4,(1,1),'upper',0,1),
    check_case('full suffix after strict witness, lower',[(1,2,1)]*3,2,(1,1,1),'lower',0,1),
    check_case('full suffix after strict witness, upper',[(1,2,1)]*3,2,(1,1,1),'upper',0,1),
]
# Empty local prefix is the exposed-anchor counterexample: both endpoints are
# deterministic, and the separate Lean Degenerate module excludes it from genuine crossings.
for cols in product(columns((1,2,1)),repeat=2):
    rows=list(zip(*cols)); R=range(2)
    assert sum(row[:0]<() for row in rows[:2])==0
    assert sum(row[:0]==() for row in rows[:2])==2
out={'status':'PASS','purpose':'supplemental exact finite adversarial model checks; no substitute for kernel proofs',
     'total_arrays':sum(r['arrays'] for r in results),'cases':results,
     'fixed_anchor_endpoint':'both deterministic at empty prefix; separately excluded by Lean Degenerate proofs'}
Path(__file__).with_name('ADVERSARIAL_FINITE.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':'PASS','total_arrays':out['total_arrays'],'cases':len(results)}))
