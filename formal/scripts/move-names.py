#!/usr/bin/env python3
# move-names.py — rewrite the importers of a module after some of its names
# moved to other modules (plan 0.114 phase C: definitions move into the Spec,
# and the implementation imports them from there; no re-export is left behind).
#
#   python3 formal/scripts/move-names.py SRC MAP [--skip FILE ...] [--dry-run]
#
# SRC is the module the names left (e.g. Once.Type). MAP is a file of lines
# `NewModule name name …` (names as written in a `using` list, `module R` for a
# record/module name). Every file under formal/Once that imports SRC is
# rewritten, by exact token edits only (memory: bulk scripts, no tidy):
#   * `open import SRC [as X] using (…) [renaming (…)]`: the list is split, one
#     statement per module that now defines the names;
#   * `open import SRC [as X] [hiding (…)] [renaming (…)]` (wholesale): one
#     wholesale open per module, with each hiding/renaming item sent to the
#     module that defines it;
#   * `import SRC as X`: an `import NewModule as X` is added for each new
#     module whose names the file uses as `X.name` (Agda resolves a name
#     through several modules imported under one alias);
#   * `import SRC` (unaliased): `SRC.name` becomes `NewModule.name`, and
#     `import NewModule` is added.
# A statement that keeps no name of SRC is dropped.
import os, re, sys

FORMAL = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
NAMECH = r'[^\s().;{}@"]'

def qual_key(n):
    """The token after `M.` in a qualified use: an operator's first name part."""
    if '_' in n and not n.startswith('module '):
        parts = [p for p in n.split('_') if p]
        if parts:
            return parts[0]
    return n

def load_map(path):
    where = {}
    for line in open(path):
        line = line.split('#')[0].split()
        if not line:
            continue
        mod, names = line[0], line[1:]
        for n in names:
            where[n.replace('module:', 'module ')] = mod
    return where

def split_items(body):
    body = re.sub(r'--[^\n]*', '', body)
    return [' '.join(i.split()) for i in body.split(';') if i.strip()]

def parse_stmt(text, src):
    """text: the whole statement. Returns dict or None."""
    m = re.match(r'(\s*)(open\s+)?import\s+' + re.escape(src) + r'(?=\s|$)(.*)$', text, re.S)
    if not m:
        return None
    ind, is_open, rest = m.group(1), bool(m.group(2)), m.group(3)
    rest_nc = re.sub(r'--[^\n]*', '', rest)
    st = {'indent': ind, 'open': is_open, 'alias': None, 'using': None,
          'hiding': None, 'renaming': None, 'public': False}
    a = re.match(r'\s*as\s+(' + NAMECH + r'+)', rest_nc)
    if a:
        st['alias'] = a.group(1)
        rest_nc = rest_nc[a.end():]
    for kw in ('using', 'hiding', 'renaming'):
        k = re.search(r'\b' + kw + r'\s*\(', rest_nc)
        if k:
            depth, i = 1, k.end()
            while depth:
                depth += {'(': 1, ')': -1}.get(rest_nc[i], 0)
                i += 1
            st[kw] = split_items(rest_nc[k.end():i - 1])
    st['public'] = bool(re.search(r'\bpublic\b', rest_nc))
    return st

def ren_from(item):
    return item.split(' to ')[0].strip()

def emit(st, mod, using, hiding, renaming):
    head = st['indent'] + ('open ' if st['open'] else '') + 'import ' + mod
    if st['alias']:
        head += ' as ' + st['alias']
    parts = []
    if using is not None:
        parts.append('using (' + '; '.join(using) + ')')
    if hiding:
        parts.append('hiding (' + '; '.join(hiding) + ')')
    if renaming:
        parts.append('renaming (' + '; '.join(renaming) + ')')
    if st['public']:
        parts.append('public')
    return ' '.join([head] + parts)

def rewrite_stmt(st, src, where, mods, used_qual):
    """Return the replacement lines for one statement."""
    out = []
    if st['open'] and st['using'] is not None:
        groups = {}
        for n in st['using']:
            groups.setdefault(where.get(n, src), []).append(n)
        rens = {}
        for r in st['renaming'] or []:
            rens.setdefault(where.get(ren_from(r), src), []).append(r)
        for mod in mods + [src]:
            if mod in groups or mod in rens:
                out.append(emit(st, mod, groups.get(mod, []), None, rens.get(mod)))
        return out
    if st['open']:   # wholesale open
        hid, ren = {}, {}
        for h in st['hiding'] or []:
            hid.setdefault(where.get(h, src), []).append(h)
        for r in st['renaming'] or []:
            ren.setdefault(where.get(ren_from(r), src), []).append(r)
        for mod in mods + [src]:
            out.append(emit(st, mod, None, hid.get(mod), ren.get(mod)))
        return out
    # qualified import
    for mod in mods:
        if mod in used_qual:
            out.append(emit(st, mod, None, None, None))
    if src in used_qual or not used_qual:
        out.append(emit(st, src, None, None, None))
    return out

def open_alias(stmt, prefix, src, where, mods):
    """`open X …` where X is SRC or an alias of it: one `open import` per module."""
    st = parse_stmt(re.sub(r'^(\s*)open\s+', r'\1open import ', stmt, count=1), prefix)
    st['alias'] = None
    return rewrite_stmt(st, src, where, mods, set())

def process(path, src, where, mods, dry):
    text = open(path).read()
    lines = text.split('\n')
    aliases = set(re.findall(r'^\s*(?:open\s+)?import\s+' + re.escape(src) + r'\s+as\s+(' + NAMECH + r'+)', text, re.M))
    prefixes = aliases | ({src} if re.search(r'^\s*import\s+' + re.escape(src) + r'\s*$', text, re.M) else set())
    openre = re.compile(r'\s*open\s+(' + '|'.join(re.escape(a) for a in prefixes) + r')(\s|$)') if prefixes else None
    i, new, changed = 0, [], False
    while i < len(lines):
        om = openre.match(lines[i]) if openre else None
        if om and not re.match(r'\s*open\s+import\b', lines[i]):
            ind = len(lines[i]) - len(lines[i].lstrip())
            j = i + 1
            while j < len(lines) and lines[j].strip() and \
                    len(lines[j]) - len(lines[j].lstrip()) > ind:
                j += 1
            new.extend(open_alias('\n'.join(lines[i:j]), om.group(1), src, where, mods))
            changed = True
            i = j
            continue
        if not re.match(r'\s*(open\s+)?import\s+' + re.escape(src) + r'(\s|$)', lines[i]):
            new.append(lines[i]); i += 1; continue
        ind = len(lines[i]) - len(lines[i].lstrip())
        j = i + 1
        while j < len(lines) and lines[j].strip() and \
                len(lines[j]) - len(lines[j].lstrip()) > ind:
            j += 1
        stmt = '\n'.join(lines[i:j])
        st = parse_stmt(stmt, src)
        prefix = st['alias'] if st['alias'] else src
        used_qual = set()
        for q in re.findall(r'(?<![\w.])' + re.escape(prefix) + r'\.(' + NAMECH + r'+)', text):
            used_qual.add(where.get(q, src))
        if not st['open'] and not st['alias']:
            # `import SRC`: rewrite SRC.name to its new home
            pass
        repl = rewrite_stmt(st, src, where, mods, used_qual)
        new.extend(repl)
        changed = True
        i = j
    out = '\n'.join(new)
    qwhere = {}
    for n, m in where.items():
        qwhere.setdefault(qual_key(n), m)
        qwhere[n] = m
    nc = lambda t: re.sub(r'--[^\n]*', '', t)
    # unaliased qualified uses: SRC.x -> NewModule.x
    def fix(m):
        n = m.group(1)
        return qwhere[n] + '.' + n if n in qwhere else m.group(0)
    body = re.sub(r'(?<![\w.])' + re.escape(src) + r'\.(' + NAMECH + r'+?)(?=[\s()])', fix, out)
    # nested module paths: SRC.R.x where `module R` moved
    for n, m in where.items():
        if n.startswith('module '):
            r = n.split()[1]
            body = re.sub(r'(?<![\w.])' + re.escape(src + '.' + r + '.'), m + '.' + r + '.', body)
    # every module used qualified, unaliased, is imported
    for mod in mods + [src]:
        used = re.search(r'(?<![\w.])' + re.escape(mod) + r'\.(?![A-Z][\w]*\.)' + NAMECH, nc(body))
        if used and not re.search(r'^\s*(open\s+)?import\s+' + re.escape(mod) + r'(\s|$)', body, re.M):
            first = re.search(r'^(open\s+)?import\s', body, re.M)
            body = body[:first.start()] + 'import ' + mod + '\n' + body[first.start():]
    # every module an alias of SRC is used for is imported under that alias
    for a in aliases:
        need = set()
        for m in re.finditer(r'(?<![\w.])' + re.escape(a) + r'\.(' + NAMECH + r'+?)(?=[\s()])', nc(body)):
            need.add(qwhere.get(m.group(1), src))
        for mod in sorted(need):
            if not re.search(r'^\s*(open\s+)?import\s+' + re.escape(mod) + r'\s+as\s+' + re.escape(a) + r'(\s|$)', body, re.M):
                first = re.search(r'^(\s*)(open\s+)?import\s', body, re.M)
                body = body[:first.start()] + first.group(1) + 'import ' + mod + ' as ' + a + '\n' + body[first.start():]
    if body != out:
        changed = True
    if changed and body != text:
        if dry:
            print('would rewrite', path)
        else:
            open(path, 'w').write(body)
        return True
    return False

def main():
    args = sys.argv[1:]
    dry = '--dry-run' in args
    skip = set()
    if '--skip' in args:
        k = args.index('--skip')
        skip = {os.path.normpath(a) for a in args[k + 1:] if not a.startswith('--')}
    src, mapfile = args[0], args[1]
    where = load_map(mapfile)
    mods = []
    for m in where.values():
        if m not in mods:
            mods.append(m)
    os.chdir(FORMAL)
    n = 0
    for root, _, fs in os.walk('Once'):
        for f in sorted(fs):
            p = os.path.normpath(os.path.join(root, f))
            if not f.endswith('.agda') or p in skip:
                continue
            if process(p, src, where, mods, dry):
                n += 1
    print(f'move-names: {n} files {"would be " if dry else ""}rewritten')

main()
