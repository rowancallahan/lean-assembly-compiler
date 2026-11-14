import json,collections,csv
J=list(csv.DictReader(open('/home/user/lean-assembly-compiler/Testing/notes/book_survey.csv')))
F=[j for j in J if j['verdict'] in 'ABCD']
print('functions (excl. X type/proof/meta, K constants):',len(F), collections.Counter(j['verdict'] for j in J))
ch=collections.defaultdict(collections.Counter)
for j in J: ch[j['chapter']][j['verdict']]+=1
for c in sorted(ch): print(c,dict(ch[c]))
feat=collections.Counter()
for j in F:
    if j['verdict']=='C':
        for n in j['needs'].split('; '):
            if n: feat[n]+=1
print(feat.most_common(14))
# unlock count: C functions whose needs are only this feature
only=collections.Counter()
for j in F:
    if j['verdict']=='C':
        n=[x for x in j['needs'].split('; ') if x]
        if len(n)==1: only[n[0]]+=1
print('single-gap',only.most_common())
# closest: C with exactly 1 need, small, pure
cl=[j for j in F if j['verdict']=='C' and len([x for x in j['needs'].split('; ') if x])==1]
import re
cl.sort(key=lambda j:len(j['signature']))
for j in cl[:60]: print(j['chapter'][:3],j['name'][-28:],'|',j['signature'][4:70],'|',j['needs'])
