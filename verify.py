from __future__ import annotations
import hashlib, os, platform, shutil, struct, subprocess, sys, tempfile, time
from concurrent.futures import ProcessPoolExecutor, ThreadPoolExecutor
from dataclasses import dataclass
from fractions import Fraction as Q
from pathlib import Path

ROOT=Path(__file__).resolve().parent
CERT=ROOT/'cert'
SRC=ROOT/'src'
H={
'near_residual.bin':'ffd6807e6a2a4a43c383e30a684de375a1e4d9ff288e0825d306d650bb665fc4',
'middle_19_999.rle':'37aeb66a4a13a93ff50d17dd41e8bd1577324cf157bce89407e78c7d796960af',
'tail_R1000.bin':'bd859ab0ef2604cee2ccf059ca6b00ba04164507bb6c8c887780faf2bf4f4c55',
}

def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1<<20),b''):h.update(b)
    return h.hexdigest()

def integrity():
    for n,w in H.items():
        p=CERT/n
        if not p.is_file():raise SystemExit(f'FAIL missing {n}')
        if sha(p)!=w:raise SystemExit(f'FAIL hash {n}')
    m=ROOT/'MANIFEST.sha256'
    if not m.is_file():raise SystemExit('FAIL missing MANIFEST.sha256')
    listed={}
    for line in m.read_text().splitlines():
        if line.strip():
            d,r=line.split('  ',1);listed[r]=d
    actual={str(p.relative_to(ROOT)).replace(os.sep,'/') for p in ROOT.rglob('*') if p.is_file() and p.name!='MANIFEST.sha256' and '__pycache__' not in p.parts}
    if set(listed)!=actual:raise SystemExit('FAIL manifest inventory')
    for r,d in listed.items():
        if sha(ROOT/r)!=d:raise SystemExit(f'FAIL manifest {r}')
    print(f'PASS integrity ({len(actual)} files)')

def cxx():
    if os.environ.get('CXX'):
        x=os.environ['CXX']
        if shutil.which(x) or Path(x).is_file():return x
        raise SystemExit(f'CXX not executable: {x}')
    for x in ('g++','clang++'):
        if shutil.which(x):return x
    raise SystemExit('C++17 compiler required: g++ or clang++')

def cid(x):
    try:return subprocess.check_output([x,'--version'],text=True,stderr=subprocess.STDOUT).splitlines()[0]
    except:return x

def build(name,x,xid):
    s=SRC/f'{name}.cpp'
    key=hashlib.sha256(s.read_bytes()+xid.encode()).hexdigest()[:16]
    out=Path(tempfile.gettempdir())/f'albertson-{name}-{key}{".exe" if os.name=="nt" else ""}'
    if out.exists():return out
    last=''
    for flags in (['-O3','-DNDEBUG','-std=c++17','-fopenmp'],['-O3','-DNDEBUG','-std=c++17']):
        p=subprocess.run([x,*flags,str(s),'-o',str(out)],text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        if p.returncode==0:return out
        last=p.stdout
        try:out.unlink()
        except FileNotFoundError:pass
    raise SystemExit(f'FAIL compile {name}\n{last}')

def run(cmd,env=None):
    p=subprocess.run([str(x) for x in cmd],cwd=ROOT,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    if p.returncode:
        print(p.stdout.rstrip());raise SystemExit(p.returncode)
    return p.stdout.rstrip()

TARGET=Q(1,64)
BP_A=Q(34627,4000)
R=0
XMAX=Q(0)

@dataclass(frozen=True)
class I:
    lo:Q
    hi:Q
    def __init__(self,a,b=None):
        a=Q(a);b=a if b is None else Q(b)
        if b<a:raise ValueError
        object.__setattr__(self,'lo',a);object.__setattr__(self,'hi',b)
    def __add__(self,o):o=ii(o);return I(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self):return I(-self.hi,-self.lo)
    def __sub__(self,o):return self+(-ii(o))
    def __rsub__(self,o):return ii(o)-self
    def __mul__(self,o):
        o=ii(o);z=(self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi);return I(min(z),max(z))
    __rmul__=__mul__
    def inv(self):
        if self.lo<=0<=self.hi:raise ValueError
        a=1/self.lo;b=1/self.hi;return I(min(a,b),max(a,b))
    def __truediv__(self,o):return self*ii(o).inv()
    def __rtruediv__(self,o):return ii(o)/self

def ii(x):return x if isinstance(x,I) else I(x)
def sq(x):return I(0,max(x.lo*x.lo,x.hi*x.hi)) if x.lo<=0<=x.hi else I(min(x.lo*x.lo,x.hi*x.hi),max(x.lo*x.lo,x.hi*x.hi))
def fall(n,k):
    z=1
    for i in range(k):z*=n-i
    return z

def BF(b,j):return I(b,b+XMAX) if j==0 else I(b-Q(j)*XMAX,b)
def GF(A,b,j):return I(A.lo-b-Q(j+1)*XMAX,A.hi-b)
def bpn(b):
    p=BF(b,0)*BF(b,1)*BF(b,2)*BF(b,3);num=I(BP_A*b-(Q(13)*BP_A+18)*XMAX,BP_A*b);den=BF(b,14)
    if not(num.lo>0 and den.lo>0):raise ValueError
    return p*num/(Q(624)*den)
def pr(A,b,u,v,j,k):
    den=fall(u,k)*fall(v,4-k);num=fall(u,j)*fall(v,4-j)
    if num==0:return I(0)
    z=I(Q(num,den))
    if k>j:
        for t in range(j,k):z=z*GF(A,b,t)
    elif j>k:
        for t in range(k,j):z=z/GF(A,b,t)
    qk=4-k;qj=4-j
    if qk>qj:
        for t in range(qj,qk):z=z*BF(b,t)
    elif qj>qk:
        for t in range(qk,qj):z=z/BF(b,t)
    return z
def ip(A,b,u,v,k):
    z=I(1)
    for t in range(k):z=z*GF(A,b,t)
    for t in range(4-k):z=z*BF(b,t)
    return z/Q(fall(u,k)*fall(v,4-k))
def m0(A):
    X=I(0,XMAX)
    return (-sq(A)+4*A-2-A*X-2*sq(X))/2 if A.hi<=2-XMAX else A*(1-X)/2
def mt(A,b):
    X=I(0,XMAX);d=3-A;tr=3-b
    if d.hi>2*b-2*XMAX or not d.lo*R>=7:raise ValueError
    if A.lo>=tr:return (3-b*d)/2-6*X
    if A.hi<=tr:return (3-sq(d)+2*b*d-2*b*b)/2-6*X
    raise ValueError
def rs(row):
    if row==0:return Q(5)
    if row==5:return Q(37,9)
    raise ValueError
def ri(row):
    if row==0:return Q(203,9)
    if row==5:return Q(155,9)
    raise ValueError
def vc(A,b,M,c):
    _,u,v,row,k=c
    if not 0<=k<=4 or fall(u,k)*fall(v,4-k)<=0:raise ValueError
    G=GF(A,b,0);B=BF(b,0)
    if not(G.lo>0 and BF(b,14).lo>0):raise ValueError
    ah=Q(u*(u-1))/(GF(A,b,0)*GF(A,b,1));bh=Q(u*v)/(B*G)
    if (ah-bh).lo<0 or (2*bh-ah).lo<0:raise ValueError
    rr=[]
    for j in range(5):
        z=pr(A,b,u,v,j,k)
        if z.hi>1:raise ValueError
        rr.append(z)
    C=ri(row)*(u+v-2)
    if row==0:C=Q((203*(u+v-2))//9)
    X=I(0,XMAX);E=Q(v*(v-1),2)+(ah-bh)*G*(1-X)+(2*bh-ah)*(M-BF(b,0)*BF(b,1)/2)
    if not ((rs(row)*E-C)*ip(A,b,u,v,k)+bpn(b)*(1-rr[0])-TARGET).lo>0:raise ValueError
def ve(A,M,s,row):
    X=I(0,XMAX);d2=A*(A-X);d4=d2*(A-2*X)*(A-3*X);C=ri(row)*(s-2)
    if row==0:C=Q((203*(s-2))//9)
    if not (rs(row)*Q(fall(s,2))/d2*M-C-Q(fall(s,4))/d4/64).lo>0:raise ValueError

@dataclass
class Box:
    lo:Q;hi:Q;caps:list;s:int;row:int

def loadtail(p):
    d=p.read_bytes();o=0
    if len(d)<16 or not d[:8].startswith(b'ALBTL01'):raise ValueError
    o=8;r,n=struct.unpack_from('<II',d,o);o+=8;bs=[]
    for _ in range(n):
        ln,ld,hn,hd=struct.unpack_from('<qqqq',d,o);o+=32;m=d[o];o+=1;cs=[]
        for _ in range(m):cs.append(tuple(d[o:o+5]));o+=5
        s=d[o];row=d[o+1];o+=2;bs.append(Box(Q(ln,ld),Q(hn,hd),cs,s,row))
    if o!=len(d):raise ValueError
    return r,bs

def wi(r):
    global R,XMAX
    R=r;XMAX=Q(1,r)
def wb(x):
    j,b=x
    try:
        A=I(b.lo,b.hi);M=m0(A)
        for c in b.caps:
            vc(A,Q(c[0],100),M,c);M=mt(A,Q(c[0],100))
        ve(A,M,b.s,b.row);return j,''
    except Exception as e:return j,str(e)
def tail(threads):
    global R,XMAX
    t=time.perf_counter();R,bs=loadtail(CERT/'tail_R1000.bin');XMAX=Q(1,R);x=Q(221,125);caps=0;mx=0
    for b in bs:
        if b.lo!=x or not b.hi>b.lo:raise SystemExit('FAIL tail coverage')
        x=b.hi;caps+=len(b.caps);mx=max(mx,len(b.caps))
    if x!=Q(141,50):raise SystemExit('FAIL tail endpoint')
    if threads<=1:it=map(wb,enumerate(bs))
    else:
        ex=ProcessPoolExecutor(max_workers=min(4,threads),initializer=wi,initargs=(R,));it=ex.map(wb,enumerate(bs),chunksize=16)
    try:
        for j,e in it:
            if e:raise SystemExit(f'FAIL tail box {j}: {e}')
    finally:
        if threads>1:ex.shutdown()
    return f'PASS uniform middle tail r>=1000 boxes={len(bs)} caps={caps} maxcaps={mx} sec={time.perf_counter()-t:.3f}'

def main():
    threads=max(1,int(os.environ.get('ALBERTSON_THREADS',os.cpu_count() or 1)))
    t=time.perf_counter();print('Albertson certificate verification');print('  finite obligations: 19 <= r <= 999');print('  uniform middle tail: r >= 1000');print()
    integrity();x=cxx();xid=cid(x);print(f'PASS compiler {xid}')
    with ThreadPoolExecutor(max_workers=2) as e:
        a=e.submit(build,'near',x,xid);b=e.submit(build,'middle',x,xid);near=a.result();middle=b.result()
    env=os.environ.copy();env['OMP_NUM_THREADS']=str(threads);env.setdefault('OMP_DYNAMIC','FALSE')
    with ThreadPoolExecutor(max_workers=3) as e:
        f1=e.submit(run,[near,CERT/'near_residual.bin'],env)
        f2=e.submit(run,[middle,CERT/'middle_19_999.rle'],env)
        f3=e.submit(tail,min(4,threads))
        out=[f1.result(),f2.result(),f3.result()]
    for s in out:print(s)
    print(f'ALL CERTIFICATES VERIFIED ({time.perf_counter()-t:.2f}s)')

if __name__=='__main__':main()
