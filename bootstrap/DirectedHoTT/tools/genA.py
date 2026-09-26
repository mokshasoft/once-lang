#!/usr/bin/env python3
"""Generate Spec/Annotated.agda — the annotated kernel syntax and its erasure.

ONE field table (FORMERS below) drives every definition: the `ATy`/`ATm`
data types, renaming, substitution, erasure `⌈_⌉`, and the two commutation
lemmas.  A field is (kind, binders, annotation?):  kind ∈ ty|tm|nat|var.
Annotation fields are exactly what erasure drops; the NON-annotation fields,
in order, must be the `RTm`/`RTy` constructor's arguments (`--check` compares
the constructor lists against Spec/Syntax).

Usage:  tools/genA.py            (writes Spec/Annotated.agda)
        tools/genA.py --check    (constructor lists agree with Spec/Syntax)
"""
import re, sys, os

T, M, N, V = 'ty', 'tm', 'nat', 'var'
def f(kind, k=0, ann=False): return (kind, k, ann)
A = True

TYS = [
 ('base', []), ('U', []),
 ('Π', [f(T), f(T,1)]), ('Σ\'', [f(T), f(T,1)]),
 ('El', [f(M)]), ('Hom', [f(T), f(M), f(M)]),
 ('Unit', []), ('Nat', []), ('Id', [f(T), f(M), f(M)]),
 ('IMu', [f(M), f(M), f(M)]),                       # IMu I D i
 ('Desc', [f(M)]),                                  # Desc I
 ('DIh', [f(M,0,A), f(M), f(T,2), f(M), f(M,0,A), f(M)]),  # DIh [I] D M C [i] p
 ('Fin', [f(N)]),
]
TMS = [
 ('var', [f(V)]),
 ('lam', [f(T,0,A), f(M,1)]),                       # lam [A] t
 ('app', [f(M), f(M)]),
 ('pair', [f(T,1,A), f(M), f(M)]),                  # pair [B] a b
 ('absurd', [f(M), f(M)]),
 ('ordtr', [f(M)]*5),
 ('fst', [f(M)]), ('snd', [f(M)]),
 ('⌜base⌝', []),
 ('⌜Π⌝', [f(M), f(M,1)]), ('⌜Σ⌝', [f(M), f(M,1)]),
 ('⌜Hom⌝', [f(M)]*3),
 ('hrefl', [f(M), f(M)]),
 ('tr', [f(T,0,A), f(M,0,A), f(M,0,A), f(M,1), f(M), f(M)]),   # tr [A t u] d p e
 ('ap', [f(M,0,A), f(M,0,A), f(M,0,A), f(M), f(M,1), f(M)]),   # ap [cA t u] cB b p
 ('⌜Id⌝', [f(M)]*3),
 ('idrefl', [f(M), f(M)]),
 ('jsub', [f(T,0,A), f(M,0,A), f(M,0,A), f(M,1), f(M), f(M)]), # jsub [A t u] d p e
 ('unit', []), ('nzero', []), ('nsuc', [f(M)]),
 ('natrec', [f(T,1,A), f(M), f(M,2), f(M)]),        # natrec [M] z s n
 ('⌜Nat⌝', []), ('⌜Unit⌝', []),
 # ★ levitated inductive families (PLAN-LEVITATION)
 ('⌜IMu⌝', [f(M), f(M), f(M)]),                     # ⌜IMu⌝ I D i
 ('⌜Fin⌝', [f(N)]),
 ('con', [f(M,0,A), f(M,0,A), f(M,0,A), f(M)]),      # con [I D i] p
 ('ielim', [f(M,0,A), f(M), f(T,2,A), f(M), f(M), f(M)]),  # ielim [I] D [M] i e t
 ('dι', [f(M,0,A), f(M)]),                          # dι [I] j
 ('dσ', [f(M,0,A), f(M), f(M)]),                    # dσ [I] S f
 ('dρ', [f(M,0,A), f(M), f(M)]),                    # dρ [I] j C
 ('dpay', [f(M)]*4),                                # dpay I D C i
 ('dih', [f(M,0,A), f(M), f(T,2,A), f(M), f(M), f(M,0,A), f(M)]),  # dih [I] D [M] e C [i] p
 ('fzero', [f(N,0,A)]),                             # fzero [n]
 ('fsuc', [f(N,0,A), f(M)]),                        # fsuc [n] t
 ('fcase', [f(N,0,A), f(T,1,A), f(M), f(M), f(M,1)]),  # fcase [n P] t a b
 ('fcase0', [f(T,1,A), f(M)]),                      # fcase0 [P] t
 ('psplit', [f(T,0,A), f(T,1,A), f(T,1,A), f(M,2), f(M)]),  # psplit [A B P] b q
]

def ext(fn, k, base):
    x = base
    for _ in range(k): x = f'{fn} ({x})' if ' ' in x else f'{fn} {x}'
    return x

def lhs(c, fs):
    if not fs: return c
    return '(' + c + ' ' + ' '.join('x' if k == V else f'x{i}' for i, (k, _, _) in enumerate(fs)) + ')'

def sig(k): return 'Var Γ' if k == V else ('ℕ' if k == N else None)

def ctor_type(c, fs, res):
    parts = []
    for kind, b, _ in fs:
        if kind == V: parts.append('Var Γ')
        elif kind == N: parts.append('ℕ')
        else:
            g = 'Γ' + ''.join(' ∙' for _ in range(b))
            g = '(' + ('(' * (b - 1)) + 'Γ' + ' ∙)' * b if b else 'Γ'
            parts.append(('ATy ' if kind == T else 'ATm ') + g)
    return f'  {c} : ∀ {{Γ}} → ' + ' → '.join(parts + [res + ' Γ'])

def act(which, c, fs, ty):
    fn = {'ren': ('renTyᴬ', 'renTmᴬ', 'extR', 'ρ'), 'sub': ('subTyᴬ', 'subTmᴬ', 'extSᴬ', 'σ')}[which]
    L = lhs(c, fs)
    me = fn[0] if ty else fn[1]
    if fs and fs[0][0] == V:
        return f'{me} {fn[3]} {L} = ' + ('var (ρ x)' if which == 'ren' else 'σ x')
    rhs = [c]
    for i, (kind, b, _) in enumerate(fs):
        if kind == N: rhs.append(f'x{i}')
        else: rhs.append(f'({fn[0] if kind == T else fn[1]} {"(" + ext(fn[2], b, fn[3]) + ")" if b else fn[3]} x{i})')
    return f'{me} {fn[3]} {L} = ' + ' '.join(rhs)

def erase(c, fs, ty):
    me = '⌈ {} ⌉ᵀ' if ty else '⌈ {} ⌉'
    L = lhs(c, fs)
    if fs and fs[0][0] == V: return '⌈ (var x) ⌉ = var x'
    rhs = [c]
    for i, (kind, b, ann) in enumerate(fs):
        if ann: continue
        rhs.append(f'x{i}' if kind == N else (f'(⌈ x{i} ⌉ᵀ)' if kind == T else f'(⌈ x{i} ⌉)'))
    return me.format(L) + ' = ' + ' '.join(rhs)

def era(which, c, fs, ty):
    me = ('era-renTy' if ty else 'era-renTm') if which == 'ren' else ('era-subTy' if ty else 'era-subTm')
    pre = f'{me} ρ' if which == 'ren' else f'{me} σ τ h'
    L = lhs(c, fs)
    if fs and fs[0][0] == V: return f'{pre} {L} = ' + ('refl' if which == 'ren' else 'h x')
    body, proofs, n = [c], [], 0
    for i, (kind, b, ann) in enumerate(fs):
        if ann: continue
        if kind == N: body.append(f'x{i}'); continue
        body.append(f'a{n}'); n += 1
        lem = ('era-renTy' if kind == T else 'era-renTm') if which == 'ren' else ('era-subTy' if kind == T else 'era-subTm')
        if which == 'ren':
            proofs.append(f'({lem} {"(" + ext("extR", b, "ρ") + ")" if b else "ρ"} x{i})')
        else:
            if b: proofs.append(f'({lem} ({ext("extSᴬ", b, "σ")}) ({ext("extS", b, "τ")}) ({ext("era-ext", b, "h")}) x{i})')
            else: proofs.append(f'({lem} σ τ h x{i})')
    if n == 0: return f'{pre} {L} = refl'
    lam = 'λ ' + ' '.join(f'a{j}' for j in range(n)) + ' → ' + ' '.join(body)
    return f'{pre} {L} = cong{n} ({lam}) ' + ' '.join(proofs)

HEADER = open(os.path.join(os.path.dirname(__file__), 'genA.header')).read()

def generate():
    o = [HEADER.rstrip('\n'), '', 'data ATy : Cx → Set', 'data ATm : Cx → Set', '', 'data ATy where']
    o += [ctor_type(c, fs, 'ATy') for c, fs in TYS]
    o += ['', 'data ATm where'] + [ctor_type(c, fs, 'ATm') for c, fs in TMS]
    o += ['', 'renTyᴬ : {Γ Δ : Cx} → Ren Γ Δ → ATy Γ → ATy Δ',
          'renTmᴬ : {Γ Δ : Cx} → Ren Γ Δ → ATm Γ → ATm Δ']
    o += [act('ren', c, fs, True) for c, fs in TYS] + [act('ren', c, fs, False) for c, fs in TMS]
    o += ['', 'Subᴬ : Cx → Cx → Set', 'Subᴬ Γ Δ = Var Γ → ATm Δ', '',
          'extSᴬ : {Γ Δ : Cx} → Subᴬ Γ Δ → Subᴬ (Γ ∙) (Δ ∙)',
          'extSᴬ σ vz     = var vz', 'extSᴬ σ (vs x) = renTmᴬ vs (σ x)', '',
          'subTyᴬ : {Γ Δ : Cx} → Subᴬ Γ Δ → ATy Γ → ATy Δ',
          'subTmᴬ : {Γ Δ : Cx} → Subᴬ Γ Δ → ATm Γ → ATm Δ']
    o += [act('sub', c, fs, True) for c, fs in TYS] + [act('sub', c, fs, False) for c, fs in TMS]
    o += ['', '-- ★ ERASURE — drops exactly the annotation fields.',
          '⌈_⌉ᵀ : {Γ : Cx} → ATy Γ → RTy Γ', '⌈_⌉ : {Γ : Cx} → ATm Γ → RTm Γ']
    o += [erase(c, fs, True) for c, fs in TYS] + [erase(c, fs, False) for c, fs in TMS]
    o += ['', '-- ★ erasure commutes with renaming',
          'era-renTy : {Γ Δ : Cx} (ρ : Ren Γ Δ) (A : ATy Γ) → ⌈ renTyᴬ ρ A ⌉ᵀ ≡ renTy ρ ⌈ A ⌉ᵀ',
          'era-renTm : {Γ Δ : Cx} (ρ : Ren Γ Δ) (t : ATm Γ) → ⌈ renTmᴬ ρ t ⌉ ≡ renTm ρ ⌈ t ⌉']
    o += [era('ren', c, fs, True) for c, fs in TYS] + [era('ren', c, fs, False) for c, fs in TMS]
    o += ['', '-- extending a substitution commutes with erasure',
          'era-ext : {Γ Δ : Cx} {σ : Subᴬ Γ Δ} {τ : Sub Γ Δ} → (∀ x → ⌈ σ x ⌉ ≡ τ x) →',
          '          ∀ x → ⌈ extSᴬ σ x ⌉ ≡ extS τ x',
          'era-ext h vz     = refl',
          'era-ext {σ = σ} h (vs x) = trans (era-renTm vs (σ x)) (cong (renTm vs) (h x))', '',
          '-- ★ erasure commutes with substitution, against ANY pointwise-equal τ',
          'era-subTy : {Γ Δ : Cx} (σ : Subᴬ Γ Δ) (τ : Sub Γ Δ) → (∀ x → ⌈ σ x ⌉ ≡ τ x) →',
          '            (A : ATy Γ) → ⌈ subTyᴬ σ A ⌉ᵀ ≡ subTy τ ⌈ A ⌉ᵀ',
          'era-subTm : {Γ Δ : Cx} (σ : Subᴬ Γ Δ) (τ : Sub Γ Δ) → (∀ x → ⌈ σ x ⌉ ≡ τ x) →',
          '            (t : ATm Γ) → ⌈ subTmᴬ σ t ⌉ ≡ subTm τ ⌈ t ⌉']
    o += [era('sub', c, fs, True) for c, fs in TYS] + [era('sub', c, fs, False) for c, fs in TMS]
    return '\n'.join(o) + '\n'

def check():
    src = open(os.path.join(os.path.dirname(__file__), '..', 'Spec', 'Syntax.agda')).read()
    def ctors(dataname):
        m = re.search(r'^data ' + dataname + r' where\n(.*?)(?=\n\S)', src, re.S | re.M)
        return [l.split(':')[0].strip() for l in m.group(1).split('\n')
                if re.match(r'^  [^\s-]', l) and ':' in l]
    ok = True
    for name, table in (('RTy', TYS), ('RTm', TMS)):
        want, have = set(ctors(name)), {c for c, _ in table}
        if want != have:
            ok = False
            print(f'{name}: missing {sorted(want - have)}, extra {sorted(have - want)}')
    print('genA: constructor lists agree' if ok else 'genA: MISMATCH')
    return ok

if __name__ == '__main__':
    if '--check' in sys.argv: sys.exit(0 if check() else 1)
    if not check(): sys.exit(1)
    out = os.path.join(os.path.dirname(__file__), '..', 'Spec', 'Annotated.agda')
    open(out, 'w').write(generate())
    print('wrote', os.path.normpath(out))
