#!/usr/bin/env python3
# ============================================================================
# profile-report.py — rank what the patched Agda's counters report measured.
#
#   tools/profile-report.py REPORT.json [REPORT.json …]   (agda-profile.sh output)
#   TOP=60 tools/profile-report.py ~/.cache/once-lang5-profile/reports/survey/*.json
#
# Reads the `--counters-file` JSON (perf-intro.md in the patched Agda) and
# prints, across all reports given:
#   1. per MODULE: own CPU time and bytes summed over its sites — the survey's
#      answer to "which modules make the cold build slow";
#   2. per KIND of after-block check (`[positivity]`, `[termination]`, …) —
#      memory `agda-perf-is-mutual-block-size` measured these at 84 %;
#   3. the top SITES by own time and by own bytes (a `where` definition is
#      its own site; its parent's own share excludes it);
#   4. what the costliest sites keep UNFOLDING (`unfoldingsByCause`).
# An incomplete report (a stop, a heap exhaustion, a snapshot) is flagged:
# its numbers are a lower bound.
# ============================================================================
import json, os, sys
from collections import defaultdict

TOP = int(os.environ.get("TOP", "40"))

def load(p):
    with open(p, encoding="utf-8") as f:
        return json.load(f)

def fmt_t(us):  return "%9.1fs" % (us / 1e6)
def fmt_b(b):   return "%9.2fG" % (b / 2**30)

def where(r):
    src = r.get("source") or "?"
    src = src.split("DirectedHoTT/")[-1]
    rng = r.get("range") or ""
    pos = rng.rsplit(":", 1)[-1] if ":" in rng else ""
    return "%s:%s" % (src, pos.split("-")[0]) if pos else src

def main(paths):
    if not paths:
        sys.exit("usage: profile-report.py REPORT.json …")
    sites, causes = [], []
    for p in paths:
        d = load(p)
        tag = os.path.basename(p)
        state = "complete" if d.get("complete") else (
            "SNAPSHOT at %ss" % d["snapshotAtSeconds"] if "snapshotAtSeconds" in d
            else "INCOMPLETE: %s" % d.get("stoppedBy", "?"))
        print("%-28s %-40s %4d module(s)" % (tag, state, len(d.get("countedModules", []))))
        if not d.get("complete"):
            for s in d.get("checkingWhenStopped", [])[:3]:
                print("    was checking: %s  %s" % (s.get("name"), where(s)))
        c = d.get("counters", {})
        sites += c.get("sites", [])
        causes += c.get("unfoldingsByCause", [])
    has_t = any("timeMicros" in s for s in sites)
    has_b = any("bytes" in s for s in sites)
    key_t = lambda s: s.get("timeMicros", 0)
    key_b = lambda s: s.get("bytes", 0)
    tot_t = sum(map(key_t, sites)); tot_b = sum(map(key_b, sites))

    # 1. per module
    mods = defaultdict(lambda: [0, 0, 0])
    for s in sites:
        m = (s.get("source") or "?").split("DirectedHoTT/")[-1]
        mods[m][0] += key_t(s); mods[m][1] += key_b(s); mods[m][2] += 1
    print("\n== MODULES by own CPU time (%d modules, total %s, %s allocated)" % (
        len(mods), fmt_t(tot_t).strip(), fmt_b(tot_b).strip()))
    acc = 0
    for m, (t, b, n) in sorted(mods.items(), key=lambda kv: -kv[1][0])[:TOP]:
        acc += t
        print("  %s %5.1f%% %5.1f%%cum %s %6d sites  %s" % (
            fmt_t(t), 100 * t / max(tot_t, 1), 100 * acc / max(tot_t, 1), fmt_b(b), n, m))

    # 2. per kind of after-block check
    kinds = defaultdict(lambda: [0, 0, 0])
    for s in sites:
        n = s.get("name", "")
        k = n.split("]")[0] + "]" if n.startswith("[") else "(definitions)"
        kinds[k][0] += key_t(s); kinds[k][1] += key_b(s); kinds[k][2] += 1
    print("\n== BY KIND of site")
    for k, (t, b, n) in sorted(kinds.items(), key=lambda kv: -kv[1][0]):
        print("  %s %5.1f%% %s %7d  %s" % (fmt_t(t), 100 * t / max(tot_t, 1), fmt_b(b), n, k))

    # 3. top sites
    if has_t:
        print("\n== TOP %d SITES by own CPU time" % TOP)
        for s in sorted(sites, key=key_t, reverse=True)[:TOP]:
            print("  %s (+nested %s) %s  %s  %s" % (fmt_t(key_t(s)), fmt_t(s.get("timeMicrosWithNested", 0)).strip(),
                                                   fmt_b(key_b(s)), s.get("name"), where(s)))
    if has_b:
        print("\n== TOP %d SITES by own bytes allocated" % TOP)
        for s in sorted(sites, key=key_b, reverse=True)[:TOP]:
            print("  %s %s  %s  %s" % (fmt_b(key_b(s)), fmt_t(key_t(s)), s.get("name"), where(s)))

    # 4. what the costliest causes unfold
    if causes:
        print("\n== TOP %d UNFOLDING CAUSES (site → what it unfolds most)" % min(TOP, 15))
        for c in sorted(causes, key=lambda c: -c.get("count", 0))[:min(TOP, 15)]:
            most = ", ".join("%s×%d" % (u["name"], u["count"]) for u in c.get("unfoldedMost", [])[:5])
            print("  %12d  %s  %s\n                %s" % (c.get("count", 0), c.get("name"), where(c), most))

if __name__ == "__main__":
    main(sys.argv[1:])
