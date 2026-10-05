#!/usr/bin/env python3
# Generates Metatheory/SigBelow.agda (the reference bound `below`, erasure
# agreement, monotonicity) from Spec/Annotated's constructors and erasure.
# Usage (from DirectedHoTT/): python3 tools/gen-sigbelow.py . tools/gen-sigbelow.tmpl > Metatheory/SigBelow.agda
import re,sys
root=sys.argv[1]
src=open(root+'/Spec/Annotated.agda').read()
def decls(name):
    blk=src[src.index(f'data {name} where'):]
    blk=blk[:blk.index('\n\n')]
    out=[]
    for l in blk.split('\n')[1:]:
        m=re.match(r'^  (\S+) : ∀ \{Γ\} → (.*)$',l)
        if m:
            args=[a.strip() for a in m.group(2).split('→')][:-1]
            out.append((m.group(1),args))
    return out
TY=decls('ATy'); TM=decls('ATm')
era={}
for l in src.split('\n'):
    m=re.match(r'^  ⌈ \(?(\S+)( [^⌉]*?)?\)? ⌉(ᵀ?) = (.*)$',l)
    if m: era[(m.group(1),m.group(3))]=m.group(4)
def kind(a):
    if a.startswith('ATy'): return 'T'
    if a.startswith('ATm'): return 'M'
    if a.startswith('Var'): return 'V'
    if a=='ℕ': return 'N'
    raise Exception(a)
bf={'T':'belowᵀ','M':'below'}
def conj(ps):
    r=ps[-1]
    for p in reversed(ps[:-1]): r=f"{p} ∧ ({r})"
    return r
def proj(ps,i,e):
    x=e
    for j in range(i):
        x=f"(∧-r ({ps[j]}) ({conj(ps[j+1:])}) {x})"
    if i<len(ps)-1:
        x=f"(∧-l ({ps[i]}) ({conj(ps[i+1:])}) {x})"
    return x
def info(c,args,var_n='n'):
    ks=[kind(a) for a in args]; xs=[f"x{i}" for i in range(len(args))]
    pat=c if not args else f"({c} {' '.join(xs)})"
    idx=[i for i,k in enumerate(ks) if k in 'TM']
    ps=[f"{bf[ks[i]]} {var_n} x{i}" for i in idx]
    return ks,xs,pat,idx,ps
BEL=[]
for fn,cons in (('belowᵀ',TY),('below',TM)):
    for c,args in cons:
        ks,xs,pat,idx,ps=info(c,args)
        rhs = "x0 < n" if c=='ref' else ("true" if not ps else conj(ps))
        BEL.append(f"{fn} n {pat} = {rhs}")
AG=[]
for fn,cons,sfx in (('era-agreeᵀ',TY,'ᵀ'),('era-agree',TM,'')):
    for c,args in cons:
        ks,xs,pat,idx,ps=info(c,args)
        if c=='ref': AG.append(f"  {fn} n h {pat} e = cong (R.ref x0) (h x0 e)"); continue
        r=era[(c,sfx)]
        kept=re.findall(r'⌈ (x\d+) ⌉(ᵀ?)',r)
        head=r.split(' ')[0]
        if not kept: AG.append(f"  {fn} n h {pat} e = refl"); continue
        prs=[]
        for x,t in kept:
            i=int(x[1:]); j=idx.index(i)
            f='era-agreeᵀ' if t=='ᵀ' else 'era-agree'
            prs.append(f"({f} n h {x} {proj(ps,j,'e')})")
        cg={1:'cong',2:'cong₂',3:'cong₃',4:'cong₄',5:'cong₅'}[len(kept)]
        AG.append(f"  {fn} n h {pat} e = {cg} R.{head} {' '.join(prs)}")
def pack(prs):
    r=prs[-1]
    for p in reversed(prs[:-1]): r=f"(∧-both {p} {r})"
    return r
MO=[]
for fn,cons in (('mono-belowᵀ',TY),('mono-below',TM)):
    for c,args in cons:
        ks,xs,pat,idx,ps=info(c,args)
        if c=='ref': MO.append(f"{fn} {{n = n}} {{m = m}} up {pat} e = up x0 e"); continue
        if not ps: MO.append(f"{fn} {{n = n}} {{m = m}} up {pat} e = refl"); continue
        prs=[]
        for j,i in enumerate(idx):
            f='mono-belowᵀ' if ks[i]=='T' else 'mono-below'
            prs.append(f"({f} {{n = n}} {{m = m}} up x{i} {proj(ps,j,'e')})")
        MO.append(f"{fn} {{n = n}} {{m = m}} up {pat} e = {pack(prs)}")
hdr=open(sys.argv[2]).read()
print(hdr.replace('@BELOW@','\n'.join(BEL)).replace('@AGREE@','\n'.join(AG)).replace('@MONO@','\n'.join(MO)))
