# SPDX-License-Identifier: AGPL-3.0-or-later
# Copyright (C) 2025-2026 Jonas Claesson
"""tools/notation.py — the Knot's object-term NOTATION, applied to generated text.

A de Bruijn variable is written `v₃` (not `var (vs (vs (vs vz)))`) and a payload
`e0 ,ₚ e1 ,ₚ unit` (not `pair e0 (pair e1 unit)`).  Both are PATTERN SYNONYMS
(Lib/Sugar), so the checker sees exactly the old terms — measured on
RedXiConGen: 64.8/67.2 s → 59.3/60.4 s CPU.  `notate` rewrites a module's text
and adds the names it uses to its Lib/Sugar import.
"""
import re

SUB = str.maketrans("01234567", "₀₁₂₃₄₅₆₇")
NAMES = ["v₀", "v₁", "v₂", "v₃", "v₄", "v₅", "v₆", "v₇", "_,ₚ_"]
VAR = re.compile(r"var ((?:\(vs )*)vz")


def vars_(s):
    """`(var (vs … vz))` / `var (vs … vz)` → `vₖ` (k ≤ 7)."""
    out, i = [], 0
    while True:
        m = VAR.search(s, i)
        if not m:
            out.append(s[i:])
            break
        d = m.group(1).count("(vs ")
        j = m.end()
        if d > 7 or s[j:j + d] != ")" * d:
            out.append(s[i:j]); i = j
            continue
        start, end = m.start(), j + d
        name = "v" + str(d).translate(SUB)
        if start > 0 and s[start - 1] == "(" and s[end:end + 1] == ")":
            out.append(s[i:start - 1]); out.append(name); i = end + 1
        else:
            out.append(s[i:start]); out.append(name); i = end
    return "".join(out)


def _close(s, i, o="(", c=")"):
    d = 0
    for j in range(i, len(s)):
        if s[j] == o: d += 1
        elif s[j] == c:
            d -= 1
            if d == 0: return j + 1
    raise ValueError("unbalanced: " + s[i:i + 60])


def _args(body):
    res, i, n = [], 0, len(body)
    while i < n:
        if body[i] in " \n":
            i += 1
        elif body[i] == "(":
            j = _close(body, i); res.append(body[i:j]); i = j
        elif body[i] == "{":
            j = _close(body, i, "{", "}"); res.append(body[i:j]); i = j
        else:
            j = i
            while j < n and body[j] not in " \n()": j += 1
            res.append(body[i:j]); i = j
    return res


def _flat(group):
    """`(pair A B)` → [A, …] with a nested `(pair …)` in B flattened."""
    a = _args(group[1:-1])
    if len(a) != 3 or a[0] != "pair": return None
    A, B = a[1], a[2]
    rest = _flat(B) if B.startswith("(pair ") else None
    return [pairs(A)] + (rest if rest else [pairs(B)])


def pairs(s):
    """parenthesised `(pair A (pair B C))` → `(A ,ₚ B ,ₚ C)`; the result stays
    parenthesised, so `,ₚ` never re-associates with a neighbouring operator."""
    out, i = [], 0
    while i < len(s):
        if s.startswith("(pair ", i):
            j = _close(s, i); comps = _flat(s[i:j])
            if comps:
                out.append("(" + " ,ₚ ".join(comps) + ")"); i = j
                continue
            out.append(s[i]); i += 1
            continue
        if s[i] == "(":
            j = _close(s, i); out.append("(" + pairs(s[i + 1:j - 1]) + ")"); i = j
            continue
        out.append(s[i]); i += 1
    return "".join(out)


def ensure_imports(text):
    used = [n for n in NAMES if (",ₚ" in text if n == "_,ₚ_" else re.search(re.escape(n) + r"(?![₀-₉])", text))]
    if not used: return text
    L = text.split("\n")
    for i, l in enumerate(L):
        m = re.match(r"^open import DirectedHoTT\.Lib\.Sugar( using \( (.*) \))?\s*$", l)
        if m:
            if not m.group(1): return text          # the whole module is open
            have = [x.strip() for x in m.group(2).split(";")]
            L[i] = "open import DirectedHoTT.Lib.Sugar using ( %s )" % "; ".join(have + [n for n in used if n not in have])
            return "\n".join(L)
    last = max(i for i, l in enumerate(L) if l.startswith("open import"))
    L.insert(last + 1, "open import DirectedHoTT.Lib.Sugar using ( %s )" % "; ".join(used))
    return "\n".join(L)


def _rewrite(chunk):
    try:
        return pairs(vars_(chunk))
    except ValueError:
        return None


def notate(text):
    """rewrite declaration by declaration (a line at column 0 and its indented
    continuation lines), so an expression spanning lines is seen whole; a
    chunk that does not parse falls back to its lines, then is left as is"""
    L = text.split("\n")
    out, i = [], 0
    def plain(l):
        return l.lstrip().startswith("--") or l.startswith(("open import", "module", "import"))
    while i < len(L):
        if plain(L[i]) or not L[i].strip():
            out.append(L[i]); i += 1
            continue
        j = i + 1
        while j < len(L) and L[j].startswith((" ", "\t")) and not L[j].lstrip().startswith("--"): j += 1
        chunk = "\n".join(L[i:j])
        r = _rewrite(chunk)
        if r is None:
            r = "\n".join(x if plain(x) else (_rewrite(x) or x) for x in L[i:j])
        out.append(r); i = j
    return ensure_imports("\n".join(out))
