import os,re,collections
os.chdir('formal')
mods={}
for root,d,fs in os.walk('Once'):
    for f in fs:
        if f.endswith('.agda'):
            p=os.path.join(root,f); mods[p[:-5].replace('/','.')]=p
pub=collections.defaultdict(set)
for m,p in mods.items():
    for line in open(p,errors='replace'):
        mm=re.match(r'\s*open\s+import\s+([A-Za-z0-9_.]+)(.*)$', line)
        if mm and re.search(r'\bpublic\b', mm.group(2)) and mm.group(1) in mods:
            pub[m].add(mm.group(1))
# Roots: every module under Once/Spec (plan 0.114: the Spec is that directory;
# re-exports out of it, while any remain, pull their targets in).
seen=set(); fr=[m for m in mods if m=='Once.Spec' or m.startswith('Once.Spec.')]
while fr:
    m=fr.pop()
    if m in seen: continue
    seen.add(m); fr.extend(pub[m])
for m in sorted(seen): print('formal/'+m.replace('.','/')+'.agda')
