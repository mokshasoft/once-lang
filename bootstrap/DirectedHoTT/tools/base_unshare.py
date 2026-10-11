#!/usr/bin/env python3
"""PLAN-REF: the SIGNATURE-FREE vocabulary of `Spec/Base` (Ctx, ⌊_⌋, single,
nrs, wk-single, _∋_∷_, …) is imported from `Spec.Base` itself, never through
an instance of `Spec.Typing`/`Spec.Reduction`.
★ WHY.  A module application copies the module's WHOLE exported scope,
re-exports included: while `Spec.Reduction` re-exported `Spec.Base`, every
instance minted its own `single`, `⌊_⌋`, … (`Lib0.Inst.Spec-Typing.single`,
`Lib.ArithComm._.⌊_⌋`, …).  Two heads for one function defeat syntactic
equality, and Agda decides `subTm (single x) F ≡ subTm (single′ x) F` by
evaluating the substitution: Examples/Gcd/LeEq 4 s → 1057 s (profiled
2026-10-11: 55M unfoldings of extS/renTm/subTm in `Eq4.⊢transport`).
So `Spec.Reduction` no longer re-exports `Spec.Base`, and this rewrite —
run by `planref.convert_all` on generated modules, and as a CLI on
hand-written ones — strips the Base names from those `using` lists and
opens them ONCE, from `Spec.Base`, before the module header.  Idempotent.
  base_unshare.py FILE...     rewrite in place
"""
import re
import sys

BASE = {'⌊_⌋', 'DescF', 'fsucS', 'iinst', 'methS', 'MethTy', 'nrs', 'pairS', 'single', 'single2',
        'swp', 'wk2M', 'wk-single', 'Ctx', '◇', '_▹_', '_∋_∷_', 'here', 'there', '_×_', '_,,_', 'π₁', 'π₂'}
SPEC = r'DirectedHoTT\.Spec\.(?:Typing|Reduction)'


def statements(L):
    """(start, end) line spans of import/open statements (paren-balanced)."""
    i = 0
    while i < len(L):
        if re.match(r'^\s*(open import|open|import|module \S+ =)\s', L[i]) and not L[i].lstrip().startswith('--'):
            j, depth = i, 0
            while True:
                depth += L[j].count('(') - L[j].count(')')
                if depth <= 0 and not (j + 1 < len(L) and re.match(r'^\s+(using|hiding|renaming|;|\))', L[j + 1])):
                    break
                j += 1
            yield i, j
            i = j + 1
        else:
            i += 1


def convert_text(s):
    L = s.split('\n')
    aliases = {'Lib0.Spec-Typing', 'Lib0.Spec-Reduction'}
    for m in re.finditer(r'import ' + SPEC + r'[^\n]*? as (\S+)', s):
        aliases.add(m.group(1))
    for m in re.finditer(r'module (\S+) = ' + SPEC + r'\b', s):
        aliases.add(m.group(1))
    head = re.compile(r'^\s*(?:open import ' + SPEC + r'\b|open (?:' + '|'.join(map(re.escape, aliases)) + r')(?=\s|$))')
    used, hide, openall = set(), None, False
    edits = []
    for a, b in statements(L):
        txt = '\n'.join(L[a:b + 1])
        if not head.match(txt):
            continue
        u = re.search(r'\busing\s*\((.*?)\)', txt, re.S)
        if u:
            names = [x.strip() for x in u.group(1).split(';') if x.strip()]
            b_ = [n for n in names if n in BASE]
            if not b_:
                continue
            used.update(b_)
            keep = [n for n in names if n not in BASE]
            if not keep and not re.search(r'\b(renaming|public)\b', txt) and not txt.lstrip().startswith('import'):
                edits.append((a, b, None))
            else:
                ind = re.match(r'\s*', L[a]).group(0)
                new = txt[:u.start(1)] + ' ' + '\n'.join(_wrap(keep, ind)) + ' ' + txt[u.end(1):]
                edits.append((a, b, new))
        else:
            openall = True
            h = re.search(r'\bhiding\s*\((.*?)\)', txt, re.S)
            hn = {x.strip() for x in h.group(1).split(';')} & BASE if h else set()
            hide = hn if hide is None else hide & hn
            if hn:   # the instance no longer exports them: hiding them warns
                rest = [x.strip() for x in h.group(1).split(';') if x.strip() not in BASE]
                new = (txt[:h.start()] + 'hiding ( %s )' % '; '.join(rest) + txt[h.end():] if rest
                       else re.sub(r'\s*\bhiding\s*\(.*?\)', '', txt, count=1, flags=re.S))
                edits.append((a, b, new))
    if not used and not openall:
        return s
    for a, b, new in sorted(edits, reverse=True):
        L[a:b + 1] = [] if new is None else new.split('\n')
    hm = next(i for i, l in enumerate(L) if re.match(r'^module DirectedHoTT\.', l))
    ex = next((i for i in range(hm) if re.match(r'^open import DirectedHoTT\.Spec\.Base\b', L[i])), None)
    if ex is not None:
        u = re.search(r'using \( (.*) \)$', L[ex])
        if u and not openall:
            used |= set(u.group(1).split('; '))
        elif not u:
            return '\n'.join(L)          # already opens Spec.Base wholesale
        del L[ex]
        hm -= 1
    if openall:
        imp = 'open import DirectedHoTT.Spec.Base' + (' hiding ( %s )' % '; '.join(sorted(hide)) if hide else '')
    else:
        imp = 'open import DirectedHoTT.Spec.Base using ( %s )' % '; '.join(sorted(used))
    L.insert(hm, imp)
    return '\n'.join(L)

def _wrap(names, ind):
    """house style: `using ( a; b` then `        ; c; d` continuation lines"""
    out, cur = [], ''
    for n in names:
        piece = n if not cur else '; ' + n
        if cur and len(ind) + 10 + len(cur) + len(piece) > 78:
            out.append(cur)
            cur = n
        else:
            cur += piece
    out.append(cur)
    return [out[0]] + [ind + '        ; ' + x for x in out[1:]]


if __name__ == '__main__':
    for p in sys.argv[1:]:
        t = open(p).read()
        u = convert_text(t)
        if u != t:
            open(p, 'w').write(u)
            print('base_unshare:', p)
