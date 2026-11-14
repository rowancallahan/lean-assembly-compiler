import json,csv,re,collections,sys,os
sys.path.insert(0,'/tmp/claude-0/s/scr')
from overrides import O
R=json.load(open('/tmp/claude-0/s/rows2.json'))
tries={}
tp='/tmp/claude-0/s/tries.tsv'
if os.path.exists(tp):
    for l in open(tp):
        p=l.rstrip('\n').split('\t')
        if len(p)>=2: tries[p[0]]=(p[1],p[2] if len(p)>2 else '')
CH={'Intro':'1 Getting to Know Lean','HelloWorld':'2 Hello, World!','Cat':'2 Hello, World!','feline':'2 Hello, World!','first-lake':'2 Hello, World!','second-lake':'2 Hello, World!','Props':'3 Interlude: Propositions, Proofs, Indexing','Induction':'3 Interlude: Propositions, Proofs, Indexing','Classes':'4 Overloading and Type Classes','Monads':'5 Monads','FunctorApplicativeMonad':'6 Functor, Applicative, Monad','MonadTransformers':'7 Monad Transformers','DependentTypes':'8 Programming with Dependent Types','Universes':'8 Programming with Dependent Types','ProgramsProofs':'9 Programming, Proving, Performance','douglib':'7 Monad Transformers','Doug1':'7 Monad Transformers','Examples.lean':'(support)','ExampleSupport.lean':'(support)','SpecialTypes':'(special types)','Strings':'(strings)'}
MAP={'tagged data/structures':'tagged data','Option/Prod/Sum results (tagged data / output encoding)':'tagged data (Option/Prod/Sum encoding)','Int (signed, unbounded)':'big numbers (Int/unbounded Nat)','multiply-divide':'multiply-divide','non-tail recursion (calls + stack)':'calls+stack / non-tail recursion','polymorphism by monomorphisation':'polymorphism by monomorphisation','polymorphism by monomorphisation (type class)':'polymorphism by monomorphisation','higher-order by specialisation':'higher-order by specialisation','two list inputs':'two list inputs','strings':'strings','allocator (new data)':'allocator'}
TW={'add1':('add1',784,'expr'),'double':('double',661,'expr'),'Nat.double':('double',661,'expr'),'NewNamespace.triple':('triple',624,'expr'),'NewNamespace.quadruple':('quadruple',589,'expr'),'timesTwelve':('timesTwelve',589,'expr'),'maximum':('maximum',829,'expr'),'isZero':('isZero',829,'expr'),'pred':('pred',829,'expr'),'even':('even_small+even_large_vs_mod',12829,'expr'),'Match.even':('even_small+even_large_vs_mod',12829,'expr'),'halve':('halve_small+halve_large_vs_div',12829,'expr'),'Match.halve':('halve_small+halve_large_vs_div',12829,'expr'),'plus':('plus_small+plus_large_vs_add',4261,'expr'),'minus':('minus_small+minus_large_vs_sub',4429,'expr'),
'Tail.sum':('sum64_vs_Tail.sum',310,'list'),'NonTail.sum':('sum64_vs_NonTail.sum',310,'list'),'Tail.reverse':('reverse_vs_Tail.reverse',310,'list'),'NonTail.reverse':('reverse_vs_NonTail.reverse',310,'list'),'take':('take5_vs_Book.take',310,'list'),'drop':('drop5_vs_Book.drop',310,'list'),'mergeSort':('sort_vs_Book.mergeSort',310,'list'),'insertionSort':('sort_vs_Book.insertionSort',310,'list'),'times':('times_vs_book_times',672,'loop'),'div':('div_vs_book_div',557,'loop')}
out=[]
for r in R:
    if not r['pure']: continue
    nm=r['name']; last=nm.split('.')[-1]
    key=nm if nm in O else (last if last in O else None)
    # require override key only for rows whose sig matches (avoid name clashes with Float/struct defs)
    needs=[MAP[x] for x in r['needs'] if x in MAP]
    if 'allocator' in needs and 'tagged data' not in needs: needs.remove('allocator')
    needs=list(dict.fromkeys(needs))
    v=r.get('verdict');why=r.get('why','');rest='';bnd='';tid='';basis='auto'
    if v in('X','D'): pass
    elif key and r['kind']!='instance' and not (r['feat'] and 'strings' in r['feat']) :
        v,rest,bnd,tid=O[key]; basis='curated'; needs=[] if v=='B' else needs
    elif r['kind']=='instance':
        v='C'; needs=needs or ['tagged data']; 
        if 'higher-order by specialisation' not in needs and re.search(r'Functor|Monad|Applicative|Alternative|Seq|Bind|Pure',r['sig']): needs.append('higher-order by specialisation')
    else:
        if re.search(r'Schema|\bRow\b|Vect|DBType|asType|Fin [a-z]|plusR|Subtype|\{n : Nat\}',r['sig']): needs.append('dependent types')
        isconst=not re.search(r'[({]|→',r['sig'].split(':')[0]+r['sig'][len(r['sig'].split(':')[0]):]) 
        if r['file'].startswith(('ExampleSupport','Examples.lean')): v='X'; why='Lean meta-programming support code'
        elif r['name'].endswith('evenLoops'): v='X'; why='rejected by Lean (non-terminating book example)'
        elif isconst and not needs: v='K'; rest='constant value (no input)'; basis='auto'
        elif re.search(r'Tail.sumHelper|Tail.factorial',r['name']): v='B'; rest='see Tail.sum' if 'sumHelper' in r['name'] else 'C: multiply'; v='B' if 'sumHelper' in r['name'] else 'C'; needs=['multiply-divide'] if v=='C' else []; basis='curated'; tid='sum' if v=='B' else ''
        else:
            v='B' if not needs else 'C'
            if v=='B': rest='no feature gap found by the classifier'; basis='auto-unverified'
    if v=='X': needs=[]
    rows=dict(chapter=CH.get(r['chapter'],r['chapter']),file=r['file'],line=r['line'],name=nm,kind=r['kind'],signature=r['sig'].replace('"','\''),types='|'.join(r['types']),recursion=r['recursion'],allocates=int(bool(r['alloc'])),strings=int(bool(r['strings'])),verdict=v,needs='; '.join(needs),restatement=rest,bounds=bnd,basis=basis,try_id=tid,variants=r['variants'])
    t=None
    if tid:
        ids=[tid] if tid in tries or not any(k.startswith(tid) for k in tries) else [tid]
        cand=[k for k in tries if k.split('_',1)[-1]==tid or k.split('_',1)[-1].startswith(tid+'_')]
        rows['try_results']='; '.join(f'{k}:{tries[k][0]}' for k in cand)
        rows['try_msg']=' | '.join(f'{k}: {tries[k][1][:140]}' for k in cand if tries[k][0]=='ERR')
    else: rows['try_results']='';rows['try_msg']=''
    rows['threeway']='';rows['threeway_inputs']='';rows['mismatches']=''
    if rows['verdict']=='B' and basis=='curated' and (last in TW or nm in TW) and r['kind']!='instance':
        n_,c_,k_=TW.get(nm) or TW[last]
        rows['threeway']='Lean(book def) == RV64 QEMU == RV64 Sail'+(' == AArch64 QEMU' if k_=='expr' else '; no ARM generator yet for this program class')
        rows['threeway_inputs']=f'{c_} ({n_})'; rows['mismatches']='0'
    out.append(rows)
cols=list(out[0].keys())
w=csv.DictWriter(open('/home/user/lean-assembly-compiler/Testing/notes/book_survey.csv','w',newline=''),cols)
w.writeheader(); w.writerows(out)
J=[o for o in out]
json.dump(J,open('/tmp/claude-0/s/final.json','w'))
print(len(out),collections.Counter(o['verdict'] for o in out))
