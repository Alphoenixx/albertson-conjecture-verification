#include <array>
#include <cassert>
#include <chrono>
#include <cstdint>
#include <cstring>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>
using namespace std;
using i128=__int128_t;

static inline i128 ab128(i128 x){return x<0?-x:x;}
static inline i128 gcd128(i128 a,i128 b){a=ab128(a);b=ab128(b);while(b){i128 t=a%b;a=b;b=t;}return a;}
static inline i128 cmul(i128 a,i128 b){i128 z;if(__builtin_mul_overflow(a,b,&z)){cerr<<"INT128 OVERFLOW\n";abort();}return z;}
static inline i128 cadd(i128 a,i128 b){i128 z;if(__builtin_add_overflow(a,b,&z)){cerr<<"INT128 OVERFLOW\n";abort();}return z;}
struct Q{
    i128 n,d;
    Q(long long x=0):n(x),d(1){}
    Q(i128 a,i128 b):n(a),d(b){norm();}
    void norm(){if(d==0)throw runtime_error("zero rational denominator");if(d<0){d=-d;n=-n;}if(n==0){d=1;return;}i128 g=gcd128(n,d);n/=g;d/=g;}
};
static inline Q operator+(const Q&a,const Q&b){i128 g=gcd128(a.d,b.d),ad=a.d/g,bd=b.d/g;return Q(cadd(cmul(a.n,bd),cmul(b.n,ad)),cmul(ad,b.d));}
static inline Q operator-(const Q&a){return Q(-a.n,a.d);} static inline Q operator-(const Q&a,const Q&b){return a+(-b);}
static inline Q operator*(const Q&a,const Q&b){i128 g1=gcd128(a.n,b.d),g2=gcd128(b.n,a.d);return Q(cmul(a.n/g1,b.n/g2),cmul(a.d/g2,b.d/g1));}
static inline Q operator/(const Q&a,const Q&b){return a*Q(b.d,b.n);} 
static inline bool operator<(const Q&a,const Q&b){i128 g=gcd128(a.d,b.d);return cmul(a.n,b.d/g)<cmul(b.n,a.d/g);} 
static inline bool operator>(const Q&a,const Q&b){return b<a;} static inline bool operator<=(const Q&a,const Q&b){return !(b<a);} static inline bool operator>=(const Q&a,const Q&b){return !(a<b);} static inline bool operator==(const Q&a,const Q&b){return a.n==b.n&&a.d==b.d;}
static inline Q& operator+=(Q&a,const Q&b){a=a+b;return a;}


static inline long long comb2(long long n){return n*(n-1)/2;}
static inline long long comb3(long long n){return n*(n-1)*(n-2)/6;}
static inline long long comb4(long long n){return n*(n-1)*(n-2)*(n-3)/24;}
static inline long long C(long long n,int k){if(k<0||k>n)return 0;if(k==0)return 1;if(k==1)return n;if(k==2)return comb2(n);if(k==3)return comb3(n);if(k==4)return comb4(n); long long z=1;for(int i=1;i<=k;i++)z=z*(n-k+i)/i;return z;}
static inline long long hill(int r){return 1LL*(r/2)*((r-1)/2)*((r-2)/2)*((r-3)/2)/4;}
static inline long long ceildiv(long long a,long long b){assert(b>0);return a>=0?(a+b-1)/b:a/b;}
static inline long long ceil128(i128 a,i128 b){assert(b>0);return a>=0?(long long)((a+b-1)/b):(long long)(a/b);}
static const long long INF=(1LL<<62);
static long long base_edges(int k,int n){
    if(n<k||n==k+1)return INF;if(k<=2)return n==k?comb2(k):INF;if(k==3)return (n>=3&&n%2)?n:INF;if(n==k)return comb2(k);
    long long v=ceil128((i128)(k+1)*(k-2)*n-(i128)k*(k-3),2LL*(k-1));
    if(n<=2*k-1)v=max(v,ceildiv(1LL*(k-1)*n+1LL*(n-k)*(2*k-n)-2,2));
    v=max(v,ceildiv(1LL*(k-1)*n+2LL*(k-3),2));
    return v;
}
static long long upper_edges(int n,long long target){
    long long best=comb2(n),Cn4=comb4(n),Cn2=comb2(n),T=target-1;
    for(int s=4;s<=n;s++){
        long long cf=203LL*(s-2)/9;
        i128 num=((i128)T*comb4(s)+(i128)cf*Cn4)*Cn2;
        i128 den=(i128)Cn4*5*C(s,2);
        long long v=(long long)(num/den); if(v<best)best=v;
    }
    return best;
}
static vector<long long> compLB;
static void init_bounds(int N=1000){
    compLB.assign(N+1,0);
    for(int q=0;q<=12;q++)compLB[q]=hill(q);
    compLB[13]=219;
    for(int q=14;q<=N;q++){
        long long v=ceildiv(1LL*q*compLB[q-1],q-4);int t=q-13;
        if(t>=2){i128 num=((i128)34627*t*t-(i128)72000*t)*q*(q-1)*(q-2)*(q-3);i128 den=(i128)4000*4*13*12*t*(t-1);v=max(v,ceil128(num,den));}
        compLB[q]=v;
    }
}
static inline bool completion_ok(int r,int c){
    long long T=1LL*c*c+1,n=r+c; i128 cost=(i128)T*comb2(n)-(i128)T*(T+1)/2;
    return (i128)(comb4(n)-comb4(r))*compLB[r] >= cost*comb4(r);
}
static inline bool routing_ok(int r,int c){
    int b=r-(c+1)-(3*(c+1)/2); if(b<2)return false; long long z=1LL*(b/2)*((b-1)/2);
    if(c>=6 && (i128)8*(c-1)*z >= (i128)5*(r+c)*(3*r+c))return true;
    if(c>=13){i128 num=(i128)34627*b*b-(i128)72000*b;if(num>0 && (i128)8*(c-1)*num >= (i128)13*12*4000*(r+c)*(3*r+c))return true;}
    return false;
}
static long long join_lower(int a,int b){
    if(min(a,b)<3)return 0; long long bn=0,bd=1;
    for(auto [side,other]:{pair<int,int>{a,b},pair<int,int>{b,a}}){
        for(int s=3;s<=min(side,6);s++){
            long long z=1LL*(s/2)*((s-1)/2)*(other/2)*((other-1)/2),num=z*C(side,2),den=C(s,2);
            if((i128)num*bd>(i128)bn*den){bn=num;bd=den;}
        }
    }
    return ceildiv(bn,bd);
}
static inline Q qrat(long long n,long long d=1){return Q(n)/d;}
static inline Q prob(int chosen,int total,int count){if(count>chosen)return Q(0);return qrat(C(chosen,count),C(total,count));}
struct Cfg{int s,h,degree;long long total_low,total_high;array<pair<long long,long long>,3> eb;};
static Cfg config(int r,int c){int n=r+c,k=3*c/2,s=r-k,h=n-s;return {s,h,r-1,base_edges(r,n),upper_edges(n,hill(r)),{{{comb2(s),comb2(s)},{1LL*s*h,1LL*s*h},{base_edges(k,h),comb2(h)}}}};}
struct W{uint8_t typ;uint16_t a,b;long long num,den;};
struct Cert{int r,c;vector<W>w;};
static pair<array<Q,8>,Q> row_for(const Cfg&cfg,const W&w){
    array<Q,8>a{}; for(auto &x:a)x=Q(0); int s=cfg.s,h=cfg.h;
    if(w.typ==0||w.typ==1){int u=w.a,v=w.b;for(int j=0;j<5;j++)a[j]=prob(u,s,j)*prob(v,h,4-j);Q slope=w.typ==0?Q(4):Q(1);a[5]=-slope*prob(u,s,2);a[6]=-slope*qrat(1LL*u*v,1LL*s*h);a[7]=-slope*prob(v,h,2);long long cf=w.typ==0?50LL*(u+v-2)/3:3LL*(u+v-2);return {a,Q(-cf)};}
    if(w.typ==2){int j=w.a;a[5+j]=1;return {a,Q(cfg.eb[j].first)};}
    if(w.typ==3){int j=w.a;a[j]=-1;if(j<5){static int k0[5]={0,1,2,3,4},k1[5]={4,3,2,1,0};long long mx=3*C(s,k0[j])*C(h,k1[j]);return {a,Q(-mx)};}return {a,Q(-cfg.eb[j-5].second)};}
    if(w.typ==4){int ss=w.a,u=s;for(int cnt=2;cnt<=4;cnt++){int idx=cnt; 
            Q jp;if(cnt==2)jp=qrat(1LL*ss*(ss-1),1LL*u*(u-1));else if(cnt==3)jp=qrat(2LL*ss*(ss-1)*(u-ss),1LL*u*(u-1)*(u-2));else jp=qrat(4LL*ss*(ss-1)*(u-ss)*(u-ss-1),1LL*u*(u-1)*(u-2)*(u-3));a[idx]=jp;}
        return {a,Q(join_lower(ss,s+h-ss))};}
    throw runtime_error("bad row type");
}
static bool valid_witness(const Cfg&cfg,const W&w){
    if(w.den<=0)return false;
    if(w.typ==0||w.typ==1){
        int u=w.a,v=w.b;
        if(u<0||u>cfg.s||v<0||v>cfg.h||u+v<=2)return false;
        return true;
    }
    if(w.typ==2)return w.a<3&&w.b==0;
    if(w.typ==3)return w.a<8&&w.b==0;
    if(w.typ==4)return w.a>=1&&w.a<cfg.s&&w.b==0;
    return false;
}
static bool check_cert(const Cfg&cfg,const Cert&z){
    array<Q,8>coef{};for(auto&x:coef)x=Q(0);Q val=0;
    try{
        for(auto const&w:z.w){
            if(!valid_witness(cfg,w))return false;
            Q wt=qrat(w.num,w.den);if(wt<0)return false;
            auto [a,b]=row_for(cfg,w);
            for(int i=0;i<8;i++)coef[i]+=wt*a[i];
            val+=wt*b;
        }
    }catch(const exception&){return false;}
    for(int i=0;i<8;i++)if(coef[i]>(i<5?Q(1):Q(0)))return false;
    return val>=hill(z.r);
}
int main(int ac,char**av){
    const char*path=ac>1?av[1]:"cert/near_residual.bin";
    init_bounds();
    ifstream f(path,ios::binary);if(!f){cerr<<"open\n";return 3;}
    char magic[8];f.read(magic,8);if(!f||memcmp(magic,"ALBNR01\0",8)){cerr<<"magic\n";return 3;}
    uint32_t N;f.read((char*)&N,4);if(!f){cerr<<"header\n";return 3;}
    unordered_map<int,Cert> mp;mp.reserve(N*2);
    for(uint32_t i=0;i<N;i++){
        uint16_t r,c;uint8_t m;
        f.read((char*)&r,2);f.read((char*)&c,2);f.read((char*)&m,1);
        if(!f){cerr<<"truncated record\n";return 3;}
        Cert z{r,c,{}};z.w.resize(m);
        for(auto&x:z.w){
            f.read((char*)&x.typ,1);f.read((char*)&x.a,2);f.read((char*)&x.b,2);f.read((char*)&x.num,8);f.read((char*)&x.den,8);
            if(!f){cerr<<"truncated witness\n";return 3;}
        }
        int key=r*1000+c;
        if(!mp.emplace(key,move(z)).second){cerr<<"duplicate certificate key\n";return 3;}
    }
    char tail;if(f.read(&tail,1)){cerr<<"trailing\n";return 3;}
    long long small=0,completion=0,routing=0,direct=0,lp=0;unordered_set<int>used;auto st=chrono::steady_clock::now();
    for(int r=19;r<=999;r++){
        int cm=(57*r-1)/250;
        for(int c=0;c<=cm;c++){
            if(c<=5){small++;continue;}
            if(completion_ok(r,c)){completion++;continue;}
            if(routing_ok(r,c)){routing++;continue;}
            Cfg cfg=config(r,c);if(cfg.total_low>cfg.total_high){direct++;continue;}
            int key=r*1000+c;auto it=mp.find(key);
            if(it==mp.end()||it->second.r!=r||it->second.c!=c||r>204||!check_cert(cfg,it->second)){
                cerr<<"FAIL r="<<r<<" c="<<c<<"\n";return 2;
            }
            if(!used.insert(key).second){cerr<<"certificate reused\n";return 2;}
            lp++;
        }
    }
    if(used.size()!=mp.size()){cerr<<"unused certs "<<mp.size()-used.size()<<"\n";return 2;}
    double sec=chrono::duration<double>(chrono::steady_clock::now()-st).count();
    cout<<"PASS near finite exact counts small="<<small<<" completion="<<completion<<" routing="<<routing<<" direct="<<direct<<" lp="<<lp<<" sec="<<sec<<"\n";
}
