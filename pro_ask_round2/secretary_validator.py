import sys, random
sys.setrecursionlimit(100000)
Z=('Z',); O=('O',)
def C(x):return('C',x)
def SEQ(a,b):return('SEQ',a,b)
def ALT(ts):return('ALT',tuple(ts))
def STAR(a):return('STAR',a)
def rsize(r):
    t=r[0]
    if t in('Z','O','C'):return 1
    if t=='SEQ':return 1+rsize(r[1])+rsize(r[2])
    if t=='ALT':return 1+sum(rsize(q) for q in r[1])
    return 1+rsize(r[1])
def sigma4(r1,r2):
    t=r1[0]
    if t=='Z':return Z
    if t=='O':return r2
    if t=='SEQ':return sigma4(r1[1],sigma4(r1[2],r2))
    if r2==Z:return Z
    if r2==O:return r1
    return('SEQ',r1,r2)
def sigma7(r1,r2):
    if r1[0]=='STAR' and r2[0]=='STAR':return STAR(r1[1]) if r1[1]==r2[1] else sigma4(r1,r2)
    if r1[0]=='STAR' and r2[0]=='SEQ' and r2[1][0]=='STAR':
        return SEQ(STAR(r1[1]),r2[2]) if r1[1]==r2[1][1] else sigma4(r1,r2)
    return sigma4(r1,r2)
def rflts(lst):
    o=[]
    for r in lst:
        if r[0]=='Z':continue
        if r[0]=='ALT':o.extend(r[1])
        else:o.append(r)
    return o
def rdistinct(xs,acc):
    acc=set(acc);o=[]
    for x in xs:
        if x in acc:continue
        o.append(x);acc.add(x)
    return o
def rsimp_ALTs(rs):
    rs=list(rs)
    if not rs:return Z
    if len(rs)==1:return rs[0]
    return ALT(rs)
def rprune(cov,rs):
    cs=set(cov);return[r for r in rs if r not in cs]
def prune_pair(e,l):
    if e[0]=='SEQ' and e[1][0]=='ALT' and l[0]=='SEQ' and l[1][0]=='ALT' and e[2]==l[2]:
        return sigma7(rsimp_ALTs(rprune(list(e[1][1]),list(l[1][1]))),l[2])
    return l
def prune_against(seen,r):
    for x in seen:r=prune_pair(x,r)
    return r
def prune_rows(rs):
    seen=[];o=[]
    for r in rs:
        rp=prune_against(seen,r);o.append(rp);seen=[rp]+seen
    return o
def strongALTs(rs):return rsimp_ALTs(rdistinct(rflts(prune_rows(rs)),set()))
def S(r):
    t=r[0]
    if t in('Z','O','C'):return r
    if t=='SEQ':return sigma7(S(r[1]),S(r[2]))
    if t=='ALT':return strongALTs(rflts([S(q) for q in r[1]]))
    sr=S(r[1])
    if sr[0] in('Z','O'):return O
    if sr[0]=='STAR':return sr
    return STAR(sr)
def rfrontier(r):
    if r[0]=='Z':return set()
    if r[0]=='ALT':
        o=set()
        for q in r[1]:o|=rfrontier(q)
        return o
    return {r}
def row_dlforms(r):
    if r[0]=='Z':return set()
    if r[0]=='ALT':
        o=set()
        for q in r[1]:o|=row_dlforms(q)
        return o
    if r[0]=='SEQ' and r[1][0]=='ALT':
        o=set()
        for p in r[1][1]:o|=row_dlforms(sigma7(p,r[2]))
        return o
    return rfrontier(r)
def dlclosure(US):
    o=set()
    for p in US:o|=row_dlforms(S(p))
    return o
def apder_terms(r):
    t=r[0]
    if t in('Z','O'):return set()
    if t=='C':return {O}
    if t=='ALT':
        o=set()
        for q in r[1]:o|=apder_terms(q)
        return o
    if t=='SEQ':return {sigma4(p,r[2]) for p in apder_terms(r[1])}|apder_terms(r[2])
    return {sigma4(p,r) for p in apder_terms(r[1])}
def apder_frontier(r):
    o=rfrontier(r)
    for q in apder_terms(r):o|=rfrontier(q)
    return o
def apder_rows(r):return {r}|apder_frontier(r)
def atf(r,k):
    t=r[0]
    if t in('Z','O'):return set()
    if t=='C':return rfrontier(k)
    if t=='ALT':
        o=set()
        for q in r[1]:o|=atf(q,k)
        return o
    if t=='SEQ':return atf(r[1],sigma4(r[2],k))|atf(r[2],k)
    return atf(r[1],sigma4(r,k))
def SAA(r,k):return dlclosure(rfrontier(sigma4(r,k))|atf(r,k))
def U(r):return dlclosure(apder_rows(r))
def nonalt(r):return r[0]!='ALT'
def rnonseq(r):return r[0]!='SEQ'
def apder_nf(r):
    t=r[0]
    if t in('Z','O','C'):return True
    if t=='ALT':return all(apder_nf(q) and nonalt(q) and q!=Z for q in r[1])
    if t=='SEQ':
        r1,r2=r[1],r[2]
        return apder_nf(r1) and apder_nf(r2) and rnonseq(r1) and r1 not in(Z,O) and r2 not in(Z,O)
    return apder_nf(r[1])
def D(r,k):return len(SAA(r,k)-SAA(O,k))
def pp(r):
    t=r[0]
    if t=='Z':return '0'
    if t=='O':return '1'
    if t=='C':return r[1]
    if t=='SEQ':return '('+pp(r[1])+'.'+pp(r[2])+')'
    if t=='ALT':return '('+'+'.join(pp(q) for q in r[1])+')'
    return pp(r[1])+'*'

def P1(q,k):  return D(ALT([q]),k) <= rsize(q)              # singleton-size
def P2(rs,k):                                                # cover
    cov=set()
    for q in set(rs): cov|=SAA(ALT([q]),k)
    return SAA(ALT(tuple(rs)),k) <= cov
def P3(r):    return D(r,O) <= rsize(r)                      # global D
def P4(r):    return len(U(r)) <= rsize(r)+1                 # U bound

a,b,c=C('a'),C('b'),C('c')
print("=== NAMED ===")
ok=True
def chk(name,cond,det=""):
    global ok
    print("  "+name.ljust(36)+("OK" if cond else "VIOLATION")+"  "+det)
    if not cond: ok=False
qn=SEQ(ALT([O,STAR(a)]),STAR(b)); kn=STAR(b)
chk("Pro-new q=(1+a*).b* k=b* P1", P1(qn,kn), "D(ALT[q],k)="+str(D(ALT([qn]),kn))+" rsize q="+str(rsize(qn))+" D(q,k)="+str(D(qn,kn)))
qb=SEQ(STAR(b),STAR(a)); qc=SEQ(STAR(c),STAR(a)); k=STAR(a)
chk("+1CE [b*a*,c*a*] k=a* P2", P2([qb,qc],k), "SAA="+str(len(SAA(ALT([qb,qc]),k))))
chk("+1CE size-step", D(ALT([qb,qc]),k)<=rsize(qb)+rsize(qc), "D="+str(D(ALT([qb,qc]),k))+" sumsize="+str(rsize(qb)+rsize(qc)))

random.seed(12345)
alpha=[a,b,c]
def gen(d):
    if d<=0: return random.choice(alpha)
    r=random.random()
    if r<0.30: return STAR(gen(d-1))
    if r<0.62:
        r1=gen(d-1)
        tries=0
        while (r1[0]=='SEQ' or r1 in (Z,O)) and tries<8: r1=gen(d-1); tries+=1
        if r1[0]=='SEQ' or r1 in (Z,O): r1=random.choice(alpha)
        r2= STAR(random.choice(alpha)) if random.random()<0.5 else gen(d-1)
        if r2 in (Z,O): r2=STAR(random.choice(alpha))
        return SEQ(r1,r2)
    if r<0.9:
        n=random.randint(1,3); bs=[]
        for _ in range(n):
            q=gen(d-1); t=0
            while (q[0]=='ALT' or q==Z) and t<8: q=gen(d-1); t+=1
            if q[0]=='ALT' or q==Z: q=random.choice(alpha)
            if q not in bs: bs.append(q)
        return ALT(bs) if bs else random.choice(alpha)
    return random.choice(alpha)

print("=== ADVERSARIAL witness-biased sweep ===")
pr=set(); pq=set(); pk=set()
for _ in range(8000):
    r=gen(random.randint(2,5))
    if apder_nf(r) and rsize(r)<=20:
        pr.add(r)
        if nonalt(r) and r!=Z: pq.add(r)
        pk.add(r)
for x in alpha: pk|={STAR(x),SEQ(STAR(x),STAR(a)),O}
pr=list(pr); pq=[q for q in pq if apder_nf(q)]; pk=[k for k in pk if apder_nf(k)]
print("  pool_r="+str(len(pr))+" pool_q="+str(len(pq))+" pool_k="+str(len(pk)))
v1=v2=v3=v4=n1=n2=n3=n4=0; worst=None
for r in pr:
    n3+=1
    if not P3(r): v3+=1; worst=worst or ("P3",pp(r),D(r,O),rsize(r))
    n4+=1
    if not P4(r): v4+=1; worst=worst or ("P4",pp(r),len(U(r)),rsize(r))
for q in pq[:500]:
    for k in pk[:150]:
        n1+=1
        if not P1(q,k):
            v1+=1; worst=worst or ("P1",pp(q),pp(k),D(ALT([q]),k),rsize(q))
for _ in range(5000):
    m=random.randint(2,4); bs=[]
    for _2 in range(m):
        q=random.choice(pq)
        if q not in bs: bs.append(q)
    if len(bs)<2: continue
    k=random.choice(pk); n2+=1
    if not P2(bs,k): v2+=1; worst=worst or ("P2",[pp(x) for x in bs],pp(k))
print("  P1 singleton-size  : "+str(n1)+" tested, "+str(v1)+" VIOL")
print("  P2 cover           : "+str(n2)+" tested, "+str(v2)+" VIOL")
print("  P3 D(r,1)<=rsize   : "+str(n3)+" tested, "+str(v3)+" VIOL")
print("  P4 |U|<=rsize+1    : "+str(n4)+" tested, "+str(v4)+" VIOL")
if worst: print("  WORST:",worst)
print("NAMED ok:",ok)
