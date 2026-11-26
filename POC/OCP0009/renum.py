"""OCP-0009 — de Bruijn tower renumbering for the lexrec example stack.

WHY THIS EXISTS.  The branch derivations are 12-deep `vs`/`there` towers on
single 400-character lines.  Every time Γ₅ changes shape, every tower moves.
Hand-editing them is how the μ₁/μ₂ measure bug got in (see FINDINGS); this
does it by position instead.  It was used for the whole 2026-08-07 refactor
(stp-out-of-Γ₅) and is what option C's remaining work needs.

WHAT IT DOES.  Parses the prefix-application syntax, tracks BINDER DEPTH
through the forms that bind (`lam`, `natrec`'s step, `⊢lam`, `⊢natrec`'s
motive and step, `Π`, `ty-Π`), and rewrites each `var (vs^k vz)` /
`there^k here` according to where index k sits relative to Γ₅'s slots.

TWO MODES.

  OPTION_C[0] = False   (the 2026-08-07 stp refactor)
      index >  d-SLOTS  ->  index-1        (the slot below stp went away)
      index == d-SLOTS  ->  stp_repl(...)  (stp itself: now an argument)
      index <  d-SLOTS  ->  untouched      (local binders)

  OPTION_C[0] = True    (option C: NO Γ₅ at all)
      the four slots at d-4/d-3/d-2/d-1 become μ₂/μ₁/cP/cA, each as
      `w^(d-SLOTS) <term>` or `⊢wk^(d-SLOTS) <derivation>`;
      local binders untouched.

  CARRIER_BINDER[0] = True also rewrites `⊢lam ty-Nat` (the CARRIER binder
      at the ℕ carrier) into `⊢lam (ty-El (⊢var A))`.  ⚠ Set it FALSE for
      LexAsm, whose `⊢lam ty-Nat`s are genuine `Nat` binders.

  SLOTS[0] is how far from the top of the local context Γ₅'s topmost slot
      sits — 4 when reading the ℕ-carrier sources, 5 for the 5-slot Γ₅.

USAGE.  `transform(src, base_depth, stp_repl)` where base_depth is the OLD
depth of the definition's AMBIENT context (Γ₅'s slots included).  Get those
by counting the Ctx: e.g. ΓZZ = Γ₅(4) + n₂ + x + le + lt = 8.

⚠ IT DOES NOT HANDLE COMMENTS.  Strip trailing `--` comments from a
definition before transforming, or they will be flattened onto one line and
swallow the rest of the file.  (This bit once already — lexAuxMot.)

⚠ AND IT DOES NOT BALANCE PARENS for you when you hand-edit the output;
check `l.count("(") == l.count(")")` per line afterwards.
"""
"""Drop the `stp` slot from Gamma5 and renumber de Bruijn towers.

Old Gamma5 (5 slots, deepest first): A, cP, mu1, mu2, stp.
At a context of old depth d the Gamma5 slots sit at indices
d-5 (stp), d-4 (mu2), d-3 (mu1), d-2 (cP), d-1 (A).

Rule:  i <  d-5  -> unchanged (local binders)
       i == d-5  -> `stp`, replaced by STP(d-5) weakenings of stpTm
       i >  d-5  -> i-1
"""
import re, sys

# arg positions that live under extra binders: name -> {argindex: +binders}
BINDERS = {
    'lam':     {0: 1},
    'natrec':  {1: 2},
    '⊢lam':    {1: 1},
    '⊢natrec': {0: 1, 2: 2},
    'ty-Π':    {1: 1},
    'Π':       {1: 1},
    'Σ':       {1: 1},
}

TOK = re.compile(r'\(|\)|[^\s()]+')

def parse(s):
    toks = TOK.findall(s)
    pos = [0]
    def node():
        t = toks[pos[0]]
        if t == '(':
            pos[0] += 1
            items = []
            while toks[pos[0]] != ')':
                items.append(node())
            pos[0] += 1
            return items
        pos[0] += 1
        return t
    out = []
    while pos[0] < len(toks):
        out.append(node())
    return out

def unparse(n):
    if isinstance(n, str):
        return n
    return '(' + ' '.join(unparse(x) for x in n) + ')'

def tower(n):
    """`var (vs (vs ... vz))` / `there (... here)` -> index, else None."""
    if isinstance(n, list) and len(n) == 2 and n[0] in ('var',):
        return depth_of(n[1], 'vz', 'vs')
    return None

def depth_of(n, zero, succ):
    k = 0
    while True:
        if isinstance(n, str):
            return k if n == zero else None
        if isinstance(n, list) and len(n) == 2 and n[0] == succ:
            k += 1; n = n[1]; continue
        if isinstance(n, list) and len(n) == 1:
            n = n[0]; continue
        return None

def mk(kind, k):
    zero, succ = ('vz', 'vs') if kind == 'var' else ('here', 'there')
    inner = zero
    for _ in range(k):
        inner = '(%s %s)' % (succ, inner)
    return '(%s %s)' % ('var', inner) if kind == 'var' else inner

def walk(n, d, stp_repl):
    """d = current OLD context depth."""
    if isinstance(n, str):
        return n
    # a `var (vs^k vz)` tower
    k = depth_of(n[1], 'vz', 'vs') if (len(n) == 2 and n[0] == 'var') else None
    if k is not None:
        return remap(k, d, stp_repl, 'var')
    # a bare `there^k here` tower (a ∋ proof used as ⊢var's argument)
    k = depth_of(n, 'here', 'there')
    if k is not None:
        return remap(k, d, stp_repl, 'there')
    if len(n) == 2 and n[0] == '⊢var':
        k = depth_of(n[1], 'here', 'there')
        if k is not None:
            r = remap(k, d, stp_repl, 'there')
            param = (d - k <= SLOTS[0]) if OPTION_C[0] else (k == d - SLOTS[0])
            return r if param else ['⊢var', r]
    if CARRIER_BINDER[0] and n[0] == '⊢lam' and n[1] == 'ty-Nat':
        n = ['⊢lam', ['ty-El', ['⊢var', mk('there', d - 1)]], n[2]]
    head = n[0] if isinstance(n[0], str) else None
    bmap = BINDERS.get(head, {})
    out = [walk(n[0], d, stp_repl)] if not isinstance(n[0], str) else [n[0]]
    for i, a in enumerate(n[1:]):
        out.append(walk(a, d + bmap.get(i, 0), stp_repl))
    return out

CARRIER_BINDER = [True]   # rewrite `⊢lam ty-Nat` -> `⊢lam (ty-El (⊢var A))`?
SLOTS = [5]          # how far from the top Gamma5's stp sat

OPTION_C = [False]
PARAM = {4: ('μ₁2', 'dμ₂'), 3: ('μ₁1', 'dμ₁'), 2: ('cP', 'dcP'), 1: ('cA', 'dcA')}

def remap_c(k, d, kind):
    off = d - k                      # 1..4 for the four Γ₅ slots
    if off > SLOTS[0]:
        return mk(kind, k)           # a local binder — untouched
    tm, drv = PARAM[off]
    tm = tm.replace('μ₁2', 'μ₂').replace('μ₁1', 'μ₁')
    n = d - SLOTS[0]                 # one weakening per local binder
    if kind == 'var':
        return '(' + 'w (' * n + tm + ')' * n + ')'
    return '(' + '⊢wk (' * n + drv + ')' * n + ')'

def remap(k, d, stp_repl, kind):
    if OPTION_C[0]:
        return remap_c(k, d, kind)
    stp = d - SLOTS[0]
    if k < stp:
        return mk(kind, k) if kind == 'var' else mk(kind, k)
    if k == stp:
        return stp_repl(stp, kind)
    return mk(kind, k - 1)

def transform(src, base_depth, stp_repl):
    """src: one Agda expression; base_depth: OLD depth of its ambient ctx."""
    tree = parse(src)
    node = tree[0] if len(tree) == 1 else tree   # top level IS one application
    out = unparse(walk(node, base_depth, stp_repl))
    if len(tree) > 1 and out.startswith('(') and out.endswith(')'):
        out = out[1:-1]                          # strip the wrapper we added
    return out

if __name__ == '__main__':
    expr = sys.stdin.read()
    d = int(sys.argv[1])
    def repl(k, kind):
        if kind == 'var':
            return '(' + 'renTm vs (' * k + 'stpTm' + ')' * k + ')'
        return '(' + '⊢wk (' * k + 'dstp' + ')' * k + ')'
    print(transform(expr, d, repl))
