#include <algorithm>
#include <atomic>
#include <chrono>
#include <climits>
#include <cstdint>
#include <cstring>
#include <fstream>
#include <iostream>
#include <vector>
#ifdef _OPENMP
#include <omp.h>
#endif
using namespace std; using i128=__int128_t;

static inline i128 ab128(i128 x){return x<0?-x:x;}
static inline i128 gcd128(i128 a,i128 b){a=ab128(a);b=ab128(b);while(b){i128 t=a%b;a=b;b=t;}return a;}
static inline i128 mul_checked(i128 a,i128 b){i128 z;if(__builtin_mul_overflow(a,b,&z)){cerr<<"INT128 OVERFLOW\n";abort();}return z;}
static inline i128 add_checked(i128 a,i128 b){i128 z;if(__builtin_add_overflow(a,b,&z)){cerr<<"INT128 OVERFLOW\n";abort();}return z;}
static inline long long fall64(long long x,int k){long long z=1;for(int i=0;i<k;i++)z*=x-i;return z;}
static inline long long Z(int r){return 1LL*(r/2)*((r-1)/2)*((r-2)/2)*((r-3)/2)/4;}
static inline long long ceil_div(long long a,long long b){return a>=0?(a+b-1)/b:a/b;}
static inline long long floor_div(long long a,long long b){return a>=0?a/b:-((-a+b-1)/b);}
static long long ceil128(i128 n,i128 d){return n>=0?(long long)((n+d-1)/d):(long long)(n/d);}
static vector<long long> CLB;
static void init_complete(int N){CLB.assign(N+1,0);for(int q=0;q<=min(N,12);q++)CLB[q]=Z(q);if(N>=13)CLB[13]=219;for(int q=14;q<=N;q++){long long val=ceil_div(1LL*q*CLB[q-1],q-4);int t=q-13;if(t>=2){i128 num=((i128)34627*t*t-(i128)72000*t)*q*(q-1)*(q-2)*(q-3);i128 den=(i128)4000*4*13*12*t*(t-1);val=max(val,ceil128(num,den));}CLB[q]=val;}}
static long long base_edges(int r,int n){long long b=0;i128 num=(i128)(r+1)*(r-2)*n-(i128)r*(r-3);b=max(b,ceil128(num,2LL*(r-1)));if(n<=2*r-1)b=max(b,ceil_div((r-1)*n+(n-r)*(2*r-n)-2,2));if(n!=2*r-1)b=max(b,ceil_div((r-1)*n+2*(r-3),2));return b;}
static long long term_edges(int r,int n,int w){long long D=3LL*r-n;if(D<7||D>2LL*w)return LLONG_MIN/4;long long num=D<=w?3LL*r*r-1LL*w*D-12LL*r:3LL*r*r-D*D+2LL*w*D-2LL*w*w-12LL*r;return ceil_div(num,2);}
static inline long long Jexact(int k,int E){if(E<=k-2)return 1LL*E*(2LL*k-E-5)/2;if(E==k-1)return 1LL*(k-2)*(k-2)/2;return ceil_div(1LL*k*(E-3),2);} 
static long long exact_terminal(int r,int n,int w){long long D=3LL*r-n;if(D<7)return LLONG_MIN/4;long long best=LLONG_MAX/4;int k0=max(3,(int)((D+1)/2));for(int k=k0;k<=r;k++){int c=min(w,k);int tlo=max(1,(int)D-k),thi=min(k,c);for(int t=tlo;t<=thi;t++){int E=k+t-(int)D;if(E<0)continue;long long a=2LL*k-t;long long eh=a*(a-1)/2-1LL*(k-t)*(c-t+1)-c/2;long long base=3LL*(r*(r-1LL)-1LL*k*(k-1))/2;long long val=base+Jexact(k,E)+eh;if(val<best)best=val;}}return best;}
static inline bool edge_exact(int r,int n,long long M,int s,int row){long long N2=1LL*s*(s-1),D2=1LL*n*(n-1),N4=fall64(s,4),D4=fall64(n,4),targ=Z(r)-1;i128 v;if(row==0){long long C=203LL*(s-2)/9;v=(i128)5*N2*M*D4-(i128)C*D2*D4-(i128)N4*targ*D2;}else if(row==1){v=(i128)37*N2*M*D4-(i128)155*(s-2)*D2*D4-(i128)9*N4*targ*D2;}else return false;return v>0;}
static inline bool cap_exact(int r,int n,int q,long long M,int u,int v){int t=n-q;if(q<15||t<4||u>t||v>q)return false;long long Na=1LL*u*(u-1),Da=1LL*t*(t-1),Nb=1LL*u*v,Db=1LL*q*t;if((i128)Na*Db<(i128)Nb*Da)return false;if((i128)2*Nb*Da<(i128)Na*Db)return false;long long N[5],D[5];int k=0;for(int j=0;j<5;j++){if(j>u||4-j>v){N[j]=0;D[j]=1;}else{N[j]=fall64(u,j)*fall64(v,4-j);D[j]=fall64(t,j)*fall64(q,4-j);}if(j&&(i128)N[j]*D[k]>(i128)N[k]*D[j])k=j;}if(N[k]==0)return false;for(int j=0;j<5;j++)if((i128)N[j]*D[k]>(i128)N[k]*D[j])return false;long long T2=M-1LL*q*(q-1)/2,X=1LL*t*(r-1)-T2,Y=-1LL*t*(r-1)+2*T2,SD=1LL*q*t*(t-1);i128 EN=(i128)(1LL*v*(v-1)/2)*SD+(i128)Na*X*q+(i128)Nb*Y*(t-1);long long C=203LL*(u+v-2)/9;i128 SN=(i128)5*EN-(i128)C*SD;long long targ=Z(r)-1,clb=CLB[q];i128 g1=gcd128(SD,D[k]);
    i128 aD=SD/g1, bD=D[k]/g1;
    i128 L=mul_checked(aD,D[k]);
    i128 term1=mul_checked(SN,bD);
    i128 term2=mul_checked(mul_checked((i128)N[k],(i128)(clb-targ)),aD);
    i128 n12=add_checked(term1,term2);
    i128 g2=gcd128(L,D[0]);
    i128 m12=D[0]/g2, m0=L/g2;
    i128 left=mul_checked(n12,m12);
    i128 right=mul_checked(mul_checked((i128)N[0],(i128)clb),m0);
    i128 total=add_checked(left,-right);
    return total>0;}
struct Cap{uint8_t p,u,v;};struct Rec{vector<Cap>caps;uint8_t s,row;};struct Run{uint16_t len;Rec rec;};struct RRow{int r,lo,hi;vector<Run>runs;};
int main(int ac,char**av){const char*path=ac>1?av[1]:"cert/middle_19_999.rle";ifstream f(path,ios::binary);char magic[8];f.read(magic,8);if(memcmp(magic,"ALBMR01",7)){cerr<<"bad magic\n";return 3;}int32_t a,b;uint64_t count;f.read((char*)&a,4);f.read((char*)&b,4);f.read((char*)&count,8);vector<RRow> rows;rows.reserve(b-a+1);uint64_t encoded=0;for(int r=a;r<=b;r++){uint16_t ncnt,rcnt;f.read((char*)&ncnt,2);f.read((char*)&rcnt,2);RRow rr{r,(221*r+124)/125,(141*r)/50,{}};if(ncnt!=rr.hi-rr.lo+1){cerr<<"bad row count\n";return 3;}rr.runs.reserve(rcnt);int sum=0;for(int j=0;j<rcnt;j++){Run run;uint8_t m;f.read((char*)&run.len,2);f.read((char*)&m,1);run.rec.caps.resize(m);for(auto&c:run.rec.caps){f.read((char*)&c.p,1);f.read((char*)&c.u,1);f.read((char*)&c.v,1);}f.read((char*)&run.rec.s,1);f.read((char*)&run.rec.row,1);sum+=run.len;rr.runs.push_back(move(run));}if(sum!=ncnt){cerr<<"bad RLE sum\n";return 3;}encoded+=ncnt;rows.push_back(move(rr));}char tail;if(f.read(&tail,1)||encoded!=count){cerr<<"trailing/count\n";return 3;}init_complete(max(1200,b+10));atomic<int> fail{0};atomic<long long> caps{0};auto st=chrono::steady_clock::now();
#pragma omp parallel for schedule(dynamic,1)
for(int ri=0;ri<(int)rows.size();ri++){if(fail.load(memory_order_relaxed))continue;auto const&rr=rows[ri];int n=rr.lo;long long localcaps=0;for(auto const&run:rr.runs){for(int z=0;z<run.len;z++,n++){long long M=max(base_edges(rr.r,n),term_edges(rr.r,n,rr.r-1));if(rr.r<98)M=max(M,exact_terminal(rr.r,n,rr.r-1));int w=rr.r-1;for(auto const&c:run.rec.caps){int q=((int)c.p*rr.r+99)/100;if(q>w||q>=rr.r||!cap_exact(rr.r,n,q,M,c.u,c.v)){fail.store(1);break;}w=q-1;M=max(M,term_edges(rr.r,n,w));if(rr.r<98)M=max(M,exact_terminal(rr.r,n,w));localcaps++;}if(fail.load())break;if(!edge_exact(rr.r,n,M,run.rec.s,run.rec.row)){fail.store(1);break;}}if(fail.load())break;}if(n!=rr.hi+1)fail.store(1);caps+=localcaps;}
if(fail){cerr<<"FAIL finite middle certificate\n";return 2;}double sec=chrono::duration<double>(chrono::steady_clock::now()-st).count();cout<<"PASS finite middle exact r="<<a<<".."<<b<<" cases="<<count<<" caps="<<caps.load()<<" sec="<<sec<<"\n";}
