#!/usr/bin/env python3
"""PLAN-REF (D082): parameterise a module by the ambient SIGNATURE.

The kernel, its metatheory and its libraries are parameterised by the
signature `𝒮 : Defs` (and, for typing, the bound `n` and the entries'
typing `ok`).  This tool brings a module that USES them into line, the way
the generators (`gen-knot.py`, `gen-judge.py`) must emit it:

  * the module's header becomes `(𝒮 : Defs) (wf : WfK 𝒮)` — one hypothesis,
    the signature's context formation — with the bound `𝓃 = size 𝒮`, the
    entries' typing `ok` and the references' reducibility `refs` derived in a
    private block (`Metatheory/Entries`);
  * every import of a parameterised module gets its arguments, read off that
    module's OWN header (so nothing here can drift from the tree);
  * each parameterised module is instantiated ONCE per file (`import M args
    as ᴵM` + `open ᴵM …`, local imports too): two applications of one module
    make its names ambiguous wherever they meet.

A module that imports nothing parameterised is left alone.

  planref.py FILE...        rewrite the files in place
  (library) convert_text(text) -> text
"""
import os
import re
import sys

ROOT = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))

# the arguments each kind of parameter list takes, inside a W module
ARGS = {'R': '𝒮', 'T': '𝒮 𝓃', 'O': '𝒮 𝓃 ok', 'F': '𝒮 𝓃 ok refs', 'W': '𝒮 wf'}
SPEC_ARGS = {'DirectedHoTT.Spec.Typing': '𝒮 𝓃', 'DirectedHoTT.Spec.Reduction': '𝒮'}
QUAL = r'(?=\s+(?:using|hiding|renaming|public|as)\b|\s*$)'
_cls = {}


def module_class(mod):
    """R/T/O/F/W from the module's own header; None if unparameterised (or not ours)."""
    if mod in _cls:
        return _cls[mod]
    c = None
    if mod.startswith('DirectedHoTT.'):
        p = os.path.join(ROOT, mod[len('DirectedHoTT.'):].replace('.', '/') + '.agda')
        if os.path.exists(p):
            s = open(p).read()
            m = re.search(r'^module ' + re.escape(mod) + r'\b(.*?)\bwhere', s, re.M | re.S)
            ps = m.group(1) if m else ''
            if '(wf : WfK' in ps:
                c = 'W'
            elif '(refs :' in ps:
                c = 'F'
            elif '(ok :' in ps:
                c = 'O'
            elif re.search(r'\((n|𝓃) : ℕ\)', ps):
                c = 'T'
            elif '(𝒮 : Defs)' in ps:
                c = 'R'
    _cls[mod] = c
    return c


def _imports_param(text):
    for m in re.finditer(r'(?:open import|import) (DirectedHoTT\.[A-Za-z.]+)', text):
        if m.group(1) in SPEC_ARGS or module_class(m.group(1)):
            return True
    return False


def _alias(mod):
    return 'ᴵ' + mod.split('.')[-1] + ('ᴿ' if mod.endswith('.Red') else '')


def convert_text(text):
    hm = re.search(r'^module (\S+) where$', text, re.M)
    if not hm or not _imports_param(text):
        return text
    me = hm.group(1)
    pre = ('open import DirectedHoTT.Spec.Syntax using ( Defs )\n'
           'open import DirectedHoTT.Spec.SigWf using ( WfK )\n'
           'import DirectedHoTT.Metatheory.Entries as Entries\n')
    post = ('\n\n-- ★ PLAN-REF: over a well-formed signature, at all its names\n'
            'private\n'
            '  𝓃 = Defs.size 𝒮\n'
            '  ok = Entries.sigOK 𝒮 𝓃 wf\n'
            '  refs = Entries.refsOK 𝒮 𝓃 (λ p → p) wf\n')
    head, body = text[:hm.start()], text[hm.end():]
    text = head + pre + f'module {me} (𝒮 : Defs) (wf : WfK 𝒮) where' + post + body
    hm = re.search(r'^module \S+ \(𝒮 : Defs\) \(wf : WfK 𝒮\) where$', text, re.M)
    head, body = text[:hm.end()], text[hm.end():]

    # arguments
    def args_of(mod):
        if mod in SPEC_ARGS:
            return SPEC_ARGS[mod]
        c = module_class(mod)
        return ARGS[c] if c else None

    def add_args(m):
        lead, kw, mod = m.group(1), m.group(2), m.group(3)
        a = args_of(mod)
        return f'{lead}{kw}{mod} {a}' if a else m.group(0)
    body = re.sub(r'^(\s*(?:where\s+)?|.*\bwhere\s+)((?:open )?import )(DirectedHoTT\.[A-Za-z.]+)' + QUAL,
                  add_args, body, flags=re.M)

    # one instance per (module, arguments): top level
    L = body.split('\n')
    top = {}
    for i, l in enumerate(L):
        m = re.match(r'^open import (DirectedHoTT\.[A-Za-z.]+) ((?:𝒮|𝓃|ok|refs|wf)(?: (?:𝒮|𝓃|ok|refs|wf))*)(.*)$', l)
        if m:
            top.setdefault((m.group(1), m.group(2)), []).append(i)
    aliases = {}
    for (mod, a), idx in top.items():
        if len(idx) < 2:
            continue
        al = _alias(mod)
        aliases[(mod, a)] = al
        for n, i in enumerate(idx):
            j = i + 1
            while j < len(L) and L[j].startswith(' ') and not L[j].strip().startswith('--') and not re.match(r'^\s+\S+\s*:', L[j]):
                j += 1
            qual = (L[i][len(f'open import {mod} {a}'):] + ' ' + ' '.join(x.strip() for x in L[i + 1:j])).strip()
            L[i] = (f'import {mod} {a} as {al}\n' if n == 0 else '') + f'open {al} {qual}'.rstrip()
            for k in range(i + 1, j):
                L[k] = None
    L = [l for l in L if l is not None]
    body = '\n'.join(L)

    # local imports open the file's one instance
    def local(m):
        lead, mod, a, rest = m.group(1), m.group(2), m.group(3), m.group(4) or ''
        al = aliases.get((mod, a))
        if al is None:
            al = _alias(mod)
            aliases[(mod, a)] = al
            need.append((mod, a, al))
        return f'{lead}open {al}{rest}'
    need = []
    body = re.sub(r'^(\s+(?:where\s+)?|\S.*\bwhere\s+)open import (DirectedHoTT\.[A-Za-z.]+) ((?:𝒮|𝓃|ok|refs|wf)(?: (?:𝒮|𝓃|ok|refs|wf))*)((?: (?:using|hiding|renaming)\b.*)?)$',
                  local, body, flags=re.M)
    if need:
        # a top-level open of the same instance becomes the alias, else add one
        L = body.split('\n')
        for mod, a, al in need:
            done = False
            for i, l in enumerate(L):
                if re.match(r'^open import ' + re.escape(mod) + ' ' + re.escape(a) + r'(\s|$)', l):
                    rest = l[len(f'open import {mod} {a}'):]
                    L[i] = f'import {mod} {a} as {al}\nopen {al}{rest}'
                    done = True
                    break
            if not done:
                j = 0
                while j < len(L) and (L[j].strip() == '' or L[j].startswith('--') or L[j].startswith('private')
                                       or re.match(r'^(open import|import|open ᴵ|  (𝓃|ok|refs) = )', L[j])
                                       or (L[j][:1].isspace() and not re.match(r'^\s+\S+\s*:', L[j]))):
                    j += 1
                L.insert(j, f'import {mod} {a} as {al}')
        body = '\n'.join(L)
    return head + body


def _modname(path):
    rel = os.path.relpath(os.path.abspath(path), ROOT)
    return 'DirectedHoTT.' + rel[:-5].replace('/', '.')


def convert_all(outs):
    """{path: text} -> {path: text}: the classes of the batch settled FIRST (a
    fixpoint: a module that imports a parameterised one, or one of the batch
    that will be, becomes `W`), then each text converted."""
    names = {p: _modname(p) for p in outs}
    w = set()
    changed = True
    while changed:
        changed = False
        for p, t in outs.items():
            n = names[p]
            if n in w or not re.search(r'^module \S+ where$', t, re.M):
                continue
            imps = re.findall(r'(?:open import|import) (DirectedHoTT\.[A-Za-z.]+)', t)
            if any(i in SPEC_ARGS or i in w or (i not in names.values() and module_class(i)) for i in imps):
                w.add(n)
                changed = True
    for n in w:
        _cls[n] = 'W'
    return {p: convert_text(t) for p, t in outs.items()}


if __name__ == '__main__':
    outs = {p: open(p).read() for p in sys.argv[1:]}
    for p, t in convert_all(outs).items():
        if t != outs[p]:
            open(p, 'w').write(t)
            print('planref:', os.path.relpath(p, ROOT))
