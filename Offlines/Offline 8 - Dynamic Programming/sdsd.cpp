/*#pragma GCC optimize("Ofast")
#pragma GCC optimize ("unroll-loops")
#pragma GCC target("sse,sse2,sse3,ssse3,sse4,popcnt,abm,mmx,avx,tune=native")*/

#include <bits/stdc++.h>
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
using namespace std;
using namespace __gnu_pbds;

#define max3(a,b,c) max(max(a,b),c)
#define max4(a,b,c,d) max(max(a,b),max(c,d))
#define min3(a,b,c) min(min(a,b),c)
#define min4(a,b,c,d) min(min(a,b),min(c,d))
#define printCase cout<<"Case "<<tc<<": "
#define pb push_back
#define ff first
#define ss second
#define all(a) (a).begin(), (a).end()
#define rall(a) (a).rbegin(), (a).rend()
#define fo(i, n) for(int i=0;i<n;i++)
#define ofo(i, n) for(int i=1;i<=n;i++)
#define rfo(i,n) for(int i=n-1;i>=0;i--)
#define int long long int
#define gap " "
#define br "\n"
#define ins insert
#define PI 2 * acos(0.0)
#define isSet(n, i) bool(n & (1LL << i))
#define setBit(n, i) (n | (1LL << i))
#define unsetBit(n, i) (n & !(1LL << i))
#define print(x) cout<< #x <<" = "<< x<<endl;
#define double long double
#define allzero(x) memset(x,0,sizeof(x))
#define mem(a,b) memset(a,b,sizeof(a))
#define even(x) !(x&1)
#define odd(x) x&1
#define sz(x) (int) (x).size()
#define ll long long int
#define found(x,y) x.find(y)!=x.end()
#define notfound(x,y) x.find(y)==x.end()
#define vi vector<int>
#define rep(i,a,b) for(int i=a;i<(b);++i)
#define MAX(a) *max_element(all(a))

template <typename T> using ordered_set = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update>;
typedef pair<int, int> pii;

const int inf = LLONG_MAX - 1;
int MAXN = 2e5 + 5;
int mod = 1e9+7;
const double pi = atan2(0, -1);
const double eps = 1e-9;

mt19937 rng(chrono::steady_clock::now().time_since_epoch().count());
int random(int l,int r) {
	return uniform_int_distribution<int>(l, r)(rng);
}

struct chash { /// use most bits rather than just the lowest ones
	const uint64_t C = (int)(2e18*acos((double)-1))+71; // large odd number
	const int RANDOM = rng();
	int operator()(int x) const {
		return __builtin_bswap64((x^RANDOM)*C); }
};

template<class K,class V> using HT = gp_hash_table<K,V,chash>;

/*** Redefined Mathematical Functions ****/

int emm(int a, int b, int m){
    return (a%m * b%m)%m;
}
int epm(int a, int b, int m){
    return ((((a%m) + (b%m) )%m)+m)%m;
}
int esm(int a, int b, int m){
    return (((a+m-b)%m)+m)%m;
}

int em(int a, int b){
    return (a%mod * b%mod)%mod;
}
int ep(int a, int b){
    return ((((a%mod) + (b%mod) )%mod)+mod)%mod;
}
int es(int a, int b){
    return (((a+mod-b)%mod)+mod)%mod;
}

int gcd(int a, int b)
{
    return __gcd(a,b);
}

int ceil2(int a, int b) {
    return (a + b - 1) / b;
}

int floor2(int a, int b) {
    return floor((double)a/(double)b);
}

int is_power_of_two(int x)
{
    if(!(x&(x-1)))
        return 1;
    return 0;
}

int Log(int n, int r)    // returns r base log n
{
    return (n > r - 1) ? 1 +
       Log(n / r, r) : 0;
}

int power(int a,int b)  //log(b)
{
    int res=1;
    while(b>0)
    {
        if(b&1)
            res = res*a;
        a = a*a;
        b >>= 1;
    }
    return res;
}

int powmod(int a,int b,int m)   //log(b)
{
    a%=m;
    int res=1;
    while(b>0)
    {
        if(b&1)
            res = res*a % m;
        a = a*a % m;
        b >>= 1;
    }
    return res;
}

int modmul(int a, int b, int M) {
    int ret = a * b - M * (int)(1.L / M * a * b);
    return ret + M * (ret < 0) - M * (ret >= (int)M);
}

int modpow(int b, int e, int mod) {
    int ans = 1;
    for (; e; b = modmul(b, b, mod), e /= 2)
    if (e & 1) ans = modmul(ans, b, mod);
    return ans;
}

int modLog(int a, int b, int m) {    // O(sqrt(m))

    int n = (int) sqrt(m) + 1, e = 1, f = 1, j = 1;

    unordered_map<int, int> A;

    while (j <= n && (e = f = e * a % m) != b % m)
    {
        A[e * b % m] = j++;
    }

    if (e == b % m) return j;

    if (__gcd(m, e) == __gcd(m, b))
    {
        for(int i=2;i<n+2;++i)
        {
            if (A.count(e = e * f % m))
                return n * i - A[e];
        }
    }

    return -1;
}


bool isPrime(int n) {
    if (n < 2 || n % 6 % 4 != 1) return (n | 1) == 3;
    int A[] = {2, 325, 9375, 28178, 450775, 9780504, 1795265022},
    s = __builtin_ctzll(n-1), d = n >> s;
    for (int a : A) { // ^ count t ra i l in g zeroes
        int p = modpow(a%n, d, n), i = s;
        while (p != 1 && p != n - 1 && a % n && i--)
            p = modmul(p, p, n);
        if (p != n-1 && i != s) return 0;
    }
    return 1;
}

int extended_euclidean(int a, int b, int& x, int& y) {
    if (b == 0) {
        x = 1;
        y = 0;
        return a;
    }
    int x1, y1;
    int d = extended_euclidean(b, a % b, x1, y1);
    x = y1;
    y = x1 - y1 * (a / b);
    return d;
}

int modinv(int a, int m)
{
    int x, y;
    int g = extended_euclidean(a, m, x, y);
    if (g != 1) {
        return -1;
    }
    else {
        x = (x % m + m) % m;
        return x;
    }
}

bool dGreater(double a, double b)
{
    return (a - b) > ( (fabs(a) < fabs(b) ? fabs(b) : fabs(a)) * eps);
}

bool dLess(double a, double b)
{
    return (b - a) > ( (fabs(a) < fabs(b) ? fabs(b) : fabs(a)) * eps);
}
bool dEqual(double a, double b)
{
    return fabs(a-b)<=eps;
}
double dMax(double a, double b)
{
    if(dGreater(a,b))
        return a;
    else
        return b;
}
double dMin(double a, double b)
{
    if(dLess(a,b))
        return a;
    else
        return b;
}

/****************** End ******************/

/************ Matrix Structure *************/

template<class T, int N> struct Matrix {

    // Usage - Matrix<int,4>M;  M.d[0] = {a,0,b,c};

    typedef Matrix M;
    array<array<T, N>, N> d{};
    M operator*(const M& m) const {

        M a;

        fo(i,N)
        {
            fo(j,N)
            {
                fo(k,N)
                {
                    a.d[i][j] += d[i][k]*m.d[k][j];
                    a.d[i][j] %= mod;
                }
            }
        }

        return a;
    }

    vector<T> operator*(const vector<T>& vec) const {

        vector<T> ret(N);

        fo(i,N)
        {
            fo(j,N)
            {
                ret[i] += d[i][j] * vec[j];
                ret[i] %= mod;
            }
        }

        return ret;
    }

    M operator^(int p) const {

        assert(p >= 0);
        M a, b(*this);

        fo(i,N)
        {
            a.d[i][i] = 1;
        }

        while (p) {
            if (p&1) a = a*b;
            b = b*b;
            p >>= 1;
        }
        return a;
    }
};

/****************** End ******************/

/************* Fraction structure ************/

struct frac{
    int x,y;
    frac(int a=0, int b=1)
    {
        x = a;
        y = b;
    }
    void simplify()
    {
        int g = __gcd(x,y);
        x /= g;
        y /= g;
    }
    frac operator+(frac p)
    {
        int g = __gcd(y,p.y);
        int a = x*(p.y/g)+(y/g)*p.x;
        int b = (y/g)*p.y;
        frac r(a,b);
        r.simplify();
        return r;
    }
    frac operator*(frac p)
    {
        int a = x*p.x;
        int b = y*p.y;
        frac r(a,b);
        r.simplify();
        return r;
    }
};

/****************** End ******************/


/************* 3D point structure ************/

struct point{
    int x,y,z;
    point operator-(point p)
    {
        point t;
        t.x = x - p.x;
        t.y = y - p.y;
        t.z = z - p.z;
        return t;
    }
    point operator+(point p)
    {
        point t;
        t.x = x + p.x;
        t.y = y + p.y;
        t.z = z + p.z;
        return t;
    }
    int sq()
    {
        return x*x + y*y + z*z;
    }
    bool operator==(point p)
    {
        return x==p.x && y==p.y && z==p.z;
    }
};
bool operator < (point a, point b)
{
    if(a.x != b.x)
        return a.x < b.x;
    if(a.y != b.y)
        return a.y < b.y;
    return a.z < b.z;
}
bool operator > (point a, point b)
{
    if(a.x != b.x)
        return a.x > b.x;
    if(a.y != b.y)
        return a.y > b.y;
    return a.z > b.z;
}
double dist(point a, point b)
{
    int dx = a.x - b.x;
    int dy = a.y - b.y;
    int dz = a.z - b.z;
    double ans = sqrt( dx*dx + dy*dy + dz*dz );
    return ans;
}

int dot(point a, point b)  // 0 = right angle, >0 = acute, <0 = obtuse
{
    return a.x * b.x + a.y * b.y + a.z * b.z ;
}

point cross(point a, point b)  // cross product of two vectors
{
    point p;
    p.x = a.y * b.z - a.z * b.y;
    p.y = a.z * b.x - a.x * b.z;
    p.z = a.x * b.y - a.y * b.x;
    return p;
}

double area(point a, point b, point c) // area of a triangle
{
    point r = cross(b-a,c-a);
    double ans = 0.5*sqrt(r.sq());
    return ans;
}

/****************** End ******************/


/*** pt structure, alternative of pair<int,int> ****/

struct pt{

    int x,y;

    pt(int a=0, int b=0)
    {
        x = a;
        y = b;
    }

    pt operator + (pt b)
    {
        pt c;
        c.x = x + b.x;
        c.y = y + b.y;
        return c;
    }

    pt operator - (pt b)
    {
        pt c;
        c.x = x - b.x;
        c.y = y - b.y;
        return c;
    }
    bool operator ==(pt b)
    {
        return (x==b.x && y==b.y);
    }
    bool operator !=(pt b)
    {
        return (!(x==b.x && y==b.y));
    }

    void show()
    {
        cout<<"x = "<<x<<" y = "<<y<<br;
    }
};

bool operator<(const pt a, const pt b)
{
    if(a.x==b.x)
        return (a.y<b.y);
    return (a.x<b.x);
}
bool operator>(const pt a, const pt b)
{
    if(a.x==b.x)
        return (a.y>b.y);
    return (a.x>b.x);
}
double val(pt a)
{
    double ans = sqrt(a.x*a.x + a.y*a.y);
    return ans;
}
double dist(pt a, pt b)
{
    int dx = a.x - b.x;
    int dy = a.y - b.y;
    double ans = sqrt( dx*dx + dy*dy );
    return ans;
}

int dot(pt a, pt b)  // 0 = right angle, >0 = acute, <0 = obtuse
{
    return a.x * b.x + a.y * b.y ;
}

double area(pt a, pt b, pt c) // area of a triangle
{
    int ans = a.x*b.y - a.y*b.x + b.x*c.y - b.y*c.x + c.x*a.y - c.y*a.x;
    return 0.5*abs(ans);
}
double angle(pt a, pt b)
{
    double ans;
    double kk = dot(a,b)/(val(a)*val(b));
    if(dEqual(kk,1.0))
    {
        ans = 0.0;
    }
    else if(dEqual(kk,-1.0))
    {
        ans = PI;
    }
    else
        ans = acos(kk);
    return ans;
}

/****************** End ******************/

/********** Debugging Functions **********/

void show(vector<pt>&v)
{
    cout<<"[";
    for(pt p: v)
    {
        int x = p.x;
        int y = p.y;
        cout<<" ("<<x<<","<<y<<") ";
    }
    cout<<"]";
    cout<<endl;
}

void show(vector<int>&v)
{
    for(int p: v)
        cout<<p<<gap;
    cout<<endl;
}

void show(pt a)
{
    cout<<"("<<a.x<<","<<a.y<<")"<<endl;
}

void debug(int n)
{
    cout<<"Okay "<<n<<endl;
}

/****************** End ******************/


/************* Combinatorics **************/

// Calculate factorials

vector<int>fact;
vector<int>invfac;

void factorials(int N){
    N = N+1;

    fact.resize(N+1);
    invfac.resize(N+1);

    invfac[0]=1;
    invfac[1] = 1;
    fact[0]=1;
    fact[1] = 1;
    for(int i=2; i<N; i++) invfac[i] = (mod - (mod/i)*invfac[mod%i]%mod)%mod;
    for(int i=1; i<N; i++){
        fact[i]=i*fact[i-1];
        invfac[i]*=invfac[i-1];
        fact[i]%=mod;
        invfac[i]%=mod;
    }
}

int ncr(int n, int r){
    if(n<0 || r<0 || n<r) return 0;
    int k=fact[n];
    k*=invfac[r]; k%=mod;
    k*=invfac[n-r]; k%=mod;
    return k;
}

/****************** End ******************/



/************* Number theory ************/

// Calculate Modular inverses

vector<int>inv;

void calcinverse(int N)
{
    N = N+1;
    inv.resize(N+1);
    inv[1] = 1;
    for(int i=2;i<N;i++)
    {
        inv[i] = mod - (mod / i) * inv[mod % i] % mod;
    }
}

vector<int>primes;

void sieve(int n)
{
    bool mark[n+10];  // Use bitset in memory issue
    ofo(i,n)
    {
        mark[i] = 1;
    }
    int i,j,limit = sqrt(n*1.0) + 2;
    mark[1] = 0;
    for(int i=4;i<=n;i+=2)
    {
        mark[i] = 0;
    }
    primes.pb(2);

    for(int i=3;i<=n;i+=2)
    {
        if(mark[i])
        {
            primes.pb(i);
            if(i<=limit)
            {
                for(int j=i*i; j<=n;j+=i*2)
                {
                    mark[j] = 0;
                }
            }
        }
    }

}

const int LIM = 10;  // Change here upto 1e8+123
bitset<LIM>markPrime;
vector<int> fastSieve() {

    const int S = (int)round(sqrt(LIM)), R = LIM / 2;

    vector<int> pr = {2}, sieve(S+1); pr.reserve((int)(LIM/log(LIM)*1.1));
    vector<pii> cp;
    for (int i = 3; i <= S; i += 2) if (!sieve[i]) {
    cp.push_back({i, i * i / 2});
    for (int j = i * i; j <= S; j += 2 * i) sieve[j] = 1;
    }
    for (int L = 1; L <= R; L += S) {
    array<bool, S> block{};
    for (auto &[p, idx] : cp)
    for (int i=idx; i < S+L; idx = (i+=p)) block[i-L] = 1;
    rep(i,0,min(S, R - L))
    if (!block[i]) pr.push_back((L + i) * 2 + 1);
    }
    for (int i : pr) markPrime[i] = 1;
    return pr;
}

vector<int>spf;
void spfSieve(int n)
{
    primes.clear();
    spf.resize(n+1);
    ofo(i,n)
    {
        spf[i] = i;
    }
    bool mark[n+10];
    ofo(i,n)
    {
        mark[i] = 1;
    }
    for(int i=2;i<=n;i++)
    {
        if(mark[i])
        {
            spf[i] = i;
            primes.pb(i);
            for(int j=2*i;j<=n;j+=i)
            {
                mark[j] = 0;
                spf[j] = min(spf[j],i);
            }
        }
    }
}

int pollard(int n) {
    auto f = [n](int x) { return modmul(x, x, n) + 1; };
    int x = 0, y = 0, t = 30, prd = 2, i = 1, q;
    while (t++ % 40 || __gcd(prd, n) == 1) {
        if (x == y) x = ++i, y = f(x);
        if ((q = modmul(prd, max(x,y) - min(x,y), n))) prd = q;
        x = f(x), y = f(f(y));
    }
    return __gcd(prd, n);
}

// This gives prime factors in random order
// One prime factor may appear twice in the vector
vector<int> factor(int n) {     // auto pf = factor(n)  // gives vector of prime factors
    if (n == 1) return {};
    if (isPrime(n)) return {n};
    int x = pollard(n);
    auto l = factor(x), r = factor(n / x);
    l.insert(l.end(), all(r));
    return l;
}

// Gives distinct prime factors in ascending order  n^(1/4)

vector<int>primeFactors(int n)
{
    auto ff = factor(n);
    set<int>s;
    for(int x: ff)
    {
        s.insert(x);
    }
    vector<int>ret;
    for(int y: s)
    {
        ret.pb(y);
    }
    return ret;
}

// Gives primes and powers

vector<pt>factorize(int n)
{
    auto a = primeFactors(n);
    vector<pt>ret;
    for(int x: a)
    {
        int k = 0;
        int p = n;
        while(p%x == 0)
        {
            p/=x;
            k++;
        }
        ret.pb({x,k});
    }
    return ret;
}

// Gives primes and powers from precalculated spf from spfSieve

vector<pt>factorizeFromSpf(int p)  // log(p) time
{
    vector<pt>res;
    while(p>1)
    {
        int q = spf[p];
        int cnt = 0;
        while(p%q == 0)
        {
            p/=q;
            cnt++;
        }
        res.pb({q,cnt});
    }
    return res;
}

vector<int>phi;

void calcphi(int n) {
    phi.resize(n+1);
    for (int i = 0; i <= n; i++)
    {
        phi[i] = i;
    }

    for (int i = 2; i <= n; i++) {
        if (phi[i] == i)
        {
            for (int j = i; j <= n; j += i)
            {
                phi[j] -= phi[j] / i;
            }
        }
    }
}

int nod(int n)
{
    auto a = factorize(n);
    int ans = 1;
    for(pt p: a)
    {
        ans = ans*(1+p.y);
    }
    return ans;
}

int getphi(int n)   // n^(1/4)
{
    auto pp = primeFactors(n);
    int ans = n;
    for(int p: pp)
    {
        ans -= ans/p;
    }
    return ans;
}

/****************** End ******************/


/************* General Helpers ************/

pt gridMoves[4] = {pt(1,0),pt(-1,0),pt(0,1),pt(0,-1)};

bool boundCheck(pt p, int n, int m) // zero indexing
{
    if(p.x>=0 && p.y>=0 && p.x<n && p.y<m)
    {
        return 1;
    }
    else
    {
        return 0;
    }
}

/****************** End ******************/


//


/*************** Data Structures **************/

struct segtree{

    // Usage: segtree tree(n); then set indices

    typedef int T;  // change type here
    static constexpr T unit = INT_MIN; // change this according to f
    T f(T a, T b)
    {
        return max(a,b); // changeable
    }
    vector<T>s;
    int n;
    segtree(int n=0, T def = unit)
    {
        this->n = n;
        s.resize(4*n,def);
    }
    void update(int pos, T val)
    {
        for(s[pos+=n] += val;pos/=2;)
        {
            s[pos] = f(s[pos*2],s[pos*2+1]);
        }
    }
    void set(int pos, T val)
    {
        for(s[pos+=n] = val;pos/=2;)
        {
            s[pos] = f(s[pos*2],s[pos*2+1]);
        }
    }
    void inc(int pos, T val)
    {
        for(s[pos+=n] += val;pos/=2;)
        {
            s[pos] = f(s[pos*2],s[pos*2+1]);
        }
    }
    T query(int b, int e) // query [b,e)
    {
        T ra = unit, rb = unit;
        for(b+=n, e+=n; b<e; b/=2, e/=2)
        {
            if(b%2)
            {
                ra = f(ra,s[b++]);
            }
            if(e%2)
            {
                rb = f(s[--e],rb);
            }
        }

        return f(ra,rb);
    }
};

// Lazy Segment Tree
struct Node {

    // query(L,R) means starting from index L before index R
    // same for other functions

    // Usage : Node*tr = new Node(a,0,sz(a)); // where a is a vector<int>

    int DEFAULT = 0;  // identity wrt combine function f

    Node *l = 0, *r = 0;
    int lo,hi,mset=inf,madd=0,val=DEFAULT;

    // returns new value if previous value = prev and a is added to all values
    int rangeaddf(int prev, int lo, int hi, int a)
    {
        return prev + (hi-lo)*a;
    }

    // return new value if all elements are set to a
    int rangef(int lo, int hi, int a)
    {
        return (hi-lo)*a;
    }

    // combines a and b
    int f(int a, int b)
    {
        return a+b;
    }

    Node(int lo, int hi):lo(lo),hi(hi) { }
    Node(vi&v, int lo, int hi):lo(lo),hi(hi){
        if(lo+1 < hi)
        {
            int mid = lo + (hi-lo)/2;
            l = new Node(v,lo,mid); r = new Node(v,mid,hi);
            val = f(l->val,r->val);
        }
        else
        {
            val = v[lo];
        }
    }
    int query(int L, int R)
    {
        if(R<=lo || hi<=L) return DEFAULT;
        if(L<=lo && hi<=R) return val;
        push();
        return f(l->query(L,R),r->query(L,R));
    }
    void set(int L, int R, int x)
    {
        if(R<=lo || hi<=L) return;
        if(L<=lo && hi<=R) mset=x, madd=0, val=rangef(lo,hi,x);
        else
        {
            push();
            l->set(L,R,x);
            r->set(L,R,x);
            val = f(l->val,r->val);
        }
    }
    void add(int L, int R, int x)
    {
        if(R<=lo || hi<=L) return;
        if(L<=lo && hi<=R) {
            if(mset != inf) mset+=x;
            else madd += x;
            val = rangeaddf(val,lo,hi,x);
        }
        else
        {
            push();
            l->add(L,R,x);
            r->add(L,R,x);
            val = f(l->val,r->val);
        }
    }
    // Lazy propagation
    void push()
    {
        if(!l)
        {
            int mid = lo + (hi-lo)/2;
            l = new Node(lo,mid); r = new Node(mid,hi);
        }
        if(mset != inf)
        {
            l->set(lo,hi,mset);
            r->set(lo,hi,mset);
            mset = inf;
        }
        else if(madd)
        {
            l->add(lo,hi,madd);
            r->add(lo,hi,madd);
            madd = 0;
        }
    }
};

/* Mo's Algorithm

const int N = 2e5 + 5;

int block_size = sqrt(N);

int a[N], b[N], freq[N], cnt;

struct Query{
    int index, L, R;
    bool operator<(Query other) const
    {
        return make_pair(L / block_size, R) <
               make_pair(other.L / block_size, other.R);
    }

};

void add(int index)
{
    if(freq[a[index]]==0)
        cnt++;
    freq[a[index]]++;
}

void remove(int index)
{
    freq[a[index]]--;
    if(freq[a[index]]==0)
        cnt--;
}

int get_answer()
{
    return cnt;
}

vector<int> mo_algo(vector<Query> queries) {

    vector<int> answers(queries.size());

    sort(queries.begin(), queries.end());

    int L = 0;
    int R = -1;

    for (Query q : queries) {

        while(R < q.R) add(++R);
        while(L < q.L) remove(L++);
        while(R > q.R) remove(R--);
        while(L > q.L) add(--L);

        answers[q.index] = get_answer();

    }

    return answers;
}

*/

// Disjoint Set Union Find

/*

vector<int>parent,csize;  // csize = component size

void initUF(int n)
{
    parent.resize(n+5);
    csize.resize(n+5);
}

void make_set(int v) {
    parent[v] = v;
    csize[v] = 1;
}

int find(int v) {
    if (v == parent[v])
        return v;
    return parent[v] = find(parent[v]);
}

void unite(int a, int b) {
    a = find(a);
    b = find(b);
    if (a != b)
    {
        if(csize[a] < csize[b])
            swap(a,b);
        csize[a] += csize[b];
        parent[b] = a;
    }
}

bool isUnited(int a, int b)
{
    return find(a)==find(b);
}

*/

/****************** End **********************/


/***************** Graph Theory ****************/

/*

    int ans = -inf;
    const int N = 30100;
    vector<pt>adj[N];
    vector<bool>vis(N,0);

*/

/*

    cin>>n>>m;

    vector<int>d(n+5,inf);
    vector<int>parent(n+5,-1);
    vector<bool>vis(n+5,0);
    vector<int>adj[n+5];

    fo(i,m)
    {
        cin>>u>>v;
        adj[u].pb(v);
        adj[v].pb(u);
    }

*/

/* Dijkstra

node u;
    fo(i,n)
    {
        d[i] = inf;
    }
    priority_queue<node>pq;
    pq.push({s,0});
    d[s] = 0;

    while(!pq.empty())
    {
        u = pq.top();
        pq.pop();
        if(u.cost > d[u.x])
        {
            continue;
        }
        for(pt p: adj[u.x])
        {
            int v = p.x;
            if( d[u.x] + p.y < d[v])
            {
                d[v] = d[u.x] + p.y ;
                pq.push({v,d[v]});
            }
        }
    }

*/

/* Floyd Warshall

    void printPath(int i, int j)
    {
        if(i!=j)
        {
            printPath(i,p[i][j]);
            cout<<gap<<j;
        }
        else
        {
            cout<<j;
        }

    }

    ofo(i,n)
    {
        ofo(j,n)
        {
            d[i][j] = inf;
        }
        d[i][i] = 0;
    }

    fo(i,m)
    {
        cin>>u>>v>>w;
        d[u][v] = min(d[u][v],w);
        d[v][u] = min(d[v][u],w);
        adj[u].pb({v,w});
        adj[v].pb({u,w});
    }

    ofo(i,n)
    {
        ofo(j,n)
        {
            p[i][j] = i;
        }
    }

    ofo(k,n)
    {
        ofo(i,n)
        {
            ofo(j,n)
            {
                if(d[i][k]<inf && d[k][j]<inf)
                {
                    if(d[i][k] + d[k][j] < d[i][j])
                    {
                        d[i][j] = d[i][k] + d[k][j];
                        p[i][j] = p[k][j];
                    }
                }
            }
        }
    }

*/

/* BFS

const int N = 31000;
int n,m;

vector<int>d(N+5,inf);
vector<int>parent(N+5,-1);
vector<bool>vis(N+5,0);
vector<pt>adj[N+5];

void BFS(int src)
{
    fo(i,N)
    {
        d[i] = inf;
        vis[i] = 0;
    }

    int u,v;
    queue<int>Q;

    u = src;
    Q.push(u);
    d[u] = 0;

    while(!Q.empty())
    {
        u = Q.front();
        Q.pop();
        vis[u] = 1;

        for(pt e: adj[u])
        {
            v = e.x;
            if(!vis[v])
            {
                vis[v] = 1;
                d[v] = d[u] + e.y;
                Q.push(v);
            }
        }
    }
}

*/

/* Grid BFS

const int N = 100;
const int M = 100;

int n,m;
char a[N+5][M+5];
bool vis[N+5][M+5];
int d[N+5][M+5];

void gridBFS(pt src)
{

    pt u,v;

    fo(j,n)
    {
        fo(k,m)
        {
            vis[j][k] = 0;
            d[j][k] = inf;
        }
    }

    queue<pt>Q;
    u = src;
    Q.push(u);
    d[u.x][u.y] = 0;

    while(!Q.empty())
    {
        u = Q.front();
        Q.pop();
        vis[u.x][u.y] = 1;

        for(pt k: gridMoves)
        {
            v = u+k;
            if( boundCheck(v,n,m) && !vis[v.x][v.y] && a[v.x][v.y]!='#' && a[v.x][v.y]!='m')
            {
                vis[v.x][v.y] = 1;
                Q.push(v);
                d[v.x][v.y] = d[u.x][u.y] + 1;
            }
        }
    }

}

*/

/****************** End ******************/

/******************* String ********************/

int smallPrimes[] = {29,31,37,43,47,53,59,61,67,71};
int bigPrimes[] = {999999929,999999937,1000000007,1000000009,1000000021,1000000033,1000000087,1000000103};

int hP1 = 43;
int hM1 = 1e9 + 7;

int hP2 = 37;
int hM2 = 999999929;

vector<int>hPw1;
vector<int>hPw2;

vector<int>invPw1;
vector<int>invPw2;

void calcHashPowers(int n)   // precalc powers and inverse powers
{
    hPw1.clear();
    hPw1.resize(n+5);
    hPw1[0] = 1;
    ofo(i,n)
    {
        hPw1[i] = emm(hPw1[i-1],hP1,hM1);
    }

    hPw2.clear();
    hPw2.resize(n+5);
    hPw2[0] = 1;
    ofo(i,n)
    {
        hPw2[i] = emm(hPw2[i-1],hP2,hM2);
    }

    int iP1, iP2;

    iP1 = powmod(hP1, hM1-2, hM1);
    iP2 = powmod(hP2, hM2-2, hM2);

    invPw1.clear();
    invPw1.resize(n+5);
    invPw1[0] = 1;
    ofo(i,n)
    {
        invPw1[i] = emm(invPw1[i-1],iP1,hM1);
    }

    invPw2.clear();
    invPw2.resize(n+5);
    invPw2[0] = 1;
    ofo(i,n)
    {
        invPw2[i] = emm(invPw2[i-1],iP2,hM2);
    }
}

pt get_hash(string s)
{
    int n = s.length();
    int hs1 = 0, hs2 = 0;;
    fo(i,n)
    {
        int val = s[i]-'a'+1;
        hs1 = epm(hs1, emm(val,hPw1[i],hM1) ,hM1);
        hs2 = epm(hs2, emm(val,hPw2[i],hM2) ,hM2);
    }
    pt res = pt(hs1,hs2);
    return res;
}

vector<pt>prefHashes;

void calcPrefHashes(string s)
{
    int n = s.length();
    int hs1 = 0, hs2 = 0;
    fo(i,n)
    {
        int val = s[i]-'a'+1;
        hs1 = epm(hs1, emm(val,hPw1[i],hM1) ,hM1);
        hs2 = epm(hs2, emm(val,hPw2[i],hM2) ,hM2);
        prefHashes.pb({hs1,hs2});
    }
}

// prefHash required
pt get_sub_hash(int i, int j)
{
    if(j>prefHashes.size())
        return pt(-1,-1);
    if(i==0)
        return prefHashes[j];

    int h1 = esm(prefHashes[j].x ,prefHashes[i-1].x ,hM1);
    int h2 = esm(prefHashes[j].y ,prefHashes[i-1].y ,hM2);
    h1 = emm(h1, invPw1[i], hM1);
    h2 = emm(h2, invPw2[i], hM2);
    return pt(h1,h2);
}

/****************** End ********************/

/************** Syntax Help **************/

/* Rotate 2D array by 90 degrees ccw

fo(i,n)
{
    fo(j,n)
    {
        B[n-1-j][i] = A[i][j];
    }
}

*/

// priority_queue< int , vector<int>, greater<int> > PQ;  // Min-Heap

// *max_element(all(a))   // maximum of a vector

// multi_set.erase(multi_set.find(p)) // erase single occurrence

// a.clear(); a.resize(n+5, vector<bool>(m+5,0)); // resize a 2D vector

/*

    cout<<fixed<<setprecision(6)<<value;

*/

// Replace map with HT or unordered_map for tight constraint
// Replace set or multiset with frequency array if possible

/****************** End ******************/

/*

    vector<int>a;

    a.clear();

    cin>>n;

    fo(i,n)
    {
        int p;
        cin>>p;
        a.pb(p);
    }

*/

/*

    cout << (ans ? "YES" : "NO") << "\n";

*/

/*
    cout<<"Case "<<tc<<": "<<ans<<br;
*/

void solve(int tc)
{
    //global initializations like "vector clear", "sum = 0"
    int m,n,p,q,maxm,minm,u,v,w,ans=0,choice;

    vector<int>vv;
    vv.pb(0);
    vv.pb(1);
    cout<<lower_bound(all(vv),2) - vv.begin();

}

void pre()
{
    //MAXN = 2e5 + 5;
    //factorials(MAXN);
    //calcinverse(MAXN);
    //sieve(MAXN);
    //calcphi(MAXN);
    //spfSieve(MAXN);
    //calcHashPowers(MAXN);
    //primes = fastSieve();  // must set LIM = 1e8+123
    //initUF(MAXN);
}

int32_t main() {

    //freopen("input.txt", "r", stdin);
    //freopen("output.txt", "w", stdout);
    ios_base::sync_with_stdio(0), cin.tie(0), cout.tie(0);
    bool multi = false;
    multi = true;
    pre();
    int t,tc=1;
    if(multi)
    {
        cin>>t;
        while(t--)
        {
            solve(tc);
            tc++;
        }
    }
    else
    {
        solve(tc);
    }
}


