import os, re, sys, json
ROOT = sys.argv[1]

def strip_block_comments(lines):
    """Return lines with {- -} regions blanked (handles nesting, crudely but safely)."""
    out, depth = [], 0
    for ln in lines:
        res, i = [], 0
        while i < len(ln):
            if ln.startswith('{-', i) and not ln.startswith('{-#', i):
                depth += 1; i += 2; continue
            if ln.startswith('-}', i) and depth > 0:
                depth -= 1; i += 2; continue
            res.append(' ' if depth else ln[i]); i += 1
        out.append(''.join(res))
    return out

def strip_line_comment(ln):
    # remove -- comments (not inside a string; good enough for Agda decls)
    m = re.search(r'(?<![\w:!#$%&*+./<=>?@\\^|~-])--(\s|$|[^\w])', ln)
    return ln[:m.start()] if m else ln

def indent(ln): return len(ln) - len(ln.lstrip())

results = {}
for dirpath, _, files in os.walk(ROOT):
    for fn in sorted(files):
        if not fn.endswith('.agda'): continue
        path = os.path.join(dirpath, fn)
        rel = os.path.relpath(path, ROOT)
        raw = open(path, encoding='utf-8').read().split('\n')
        lines = [strip_line_comment(l) for l in strip_block_comments(raw)]
        names, blocks = [], 0
        i = 0
        while i < len(lines):
            ln = lines[i]
            m = re.match(r'^(\s*)postulate(\s|$)', ln)
            if not m:
                i += 1; continue
            blocks += 1
            base = len(m.group(1))
            # trailing content on the same line counts as the first item
            rest = ln[m.end():].strip()
            body = []
            if rest: body.append((base + 99, rest))
            j = i + 1
            item_indent = None
            while j < len(lines):
                l2 = lines[j]
                if not l2.strip(): j += 1; continue
                ind = indent(l2)
                if ind <= base: break
                if item_indent is None: item_indent = ind
                body.append((ind, l2.strip()))
                j += 1
            # an ITEM begins at item_indent; deeper lines continue it
            cur = None
            items = []
            for ind, txt in body:
                if item_indent is not None and ind == item_indent:
                    if cur is not None: items.append(cur)
                    cur = txt
                else:
                    if cur is None: cur = txt
                    else: cur += ' ' + txt
            if cur is not None: items.append(cur)
            for it in items:
                # "a b c : T"  -> 3 names ; split on the FIRST top-level colon
                mm = re.match(r'^([^:]+?)\s*:(?!:)', it)
                if mm:
                    for nm in mm.group(1).split():
                        if nm not in ('{', '}'): names.append(nm)
            i = j
        if blocks or names:
            results[rel] = {'blocks': blocks, 'names': names}

tot_n = sum(len(v['names']) for v in results.values())
tot_b = sum(v['blocks'] for v in results.values())
print(f"TOTAL: {tot_n} postulated names in {tot_b} blocks across {len(results)} files")
json.dump(results, open(sys.argv[2], 'w'), indent=1, ensure_ascii=False)
