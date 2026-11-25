// Exact two-edit search around the 28-gate Fano final-AND circuit.
// Compile with c++ -O2 -std=c++17. No solver or downloaded data is needed.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <vector>

using Word = std::uint64_t;
constexpr int inputs = 14, total = 42, output = 41;
struct Gate { bool isOr; int a, b; };
using Net = std::array<Gate, total>;
using Values = std::array<Word, total>;
using Order = std::vector<int>;
Word target, tests, pins;
Values initial{};

bool incident(int p, int l) { return p == l || p == (l+1)%7 || p == (l+3)%7; }
bool edge(int x) {
    for (int p=0;p<7;++p) for (int l=0;l<7;++l)
        if (incident(p,l) && (x>>p&1) && (x>>(7+l)&1)) return true;
    return false;
}
void boundary() {
    std::vector<int> rows;
    for (int p=0;p<7;++p) for (int l=0;l<7;++l)
        if (incident(p,l)) rows.push_back((1<<p)|(1<<(7+l)));
    target=(Word(1)<<rows.size())-1;
    for (int x=0;x<(1<<14);++x) if (!edge(x)) {
        bool maximal=true;
        for (int i=0;i<14;++i) if (!(x>>i&1) && !edge(x|(1<<i))) maximal=false;
        if (maximal) rows.push_back(x);
    }
    if (rows.size()!=58) std::abort();
    rows.push_back(1); rows.push_back(1<<7);
    tests=(Word(1)<<rows.size())-1;
    pins=Word(3)<<58;
    for (unsigned i=0;i<rows.size();++i) for (int j=0;j<inputs;++j)
        if (rows[i]>>j&1) initial[j] |= Word(1)<<i;
}
Net seed() {
    Net n{};
    std::vector<Gate> gates = {{true,7,13},{true,14,11},{false,0,15},{true,8,7},{true,17,12},{false,1,18},{true,10,9},{true,20,7},{false,3,21},{true,11,10},{true,23,8},{false,4,24},{true,12,11},{true,26,9},{false,5,27},{true,13,12},{true,29,10},{false,6,30},{true,28,31},{true,25,32},{true,22,33},{true,19,34},{true,16,35},{true,9,8},{true,37,13},{true,36,2},{true,36,38},{false,39,40}};
    std::copy(gates.begin(),gates.end(),n.begin()+inputs); return n;
}
// Re-schedule independent gates. The deleted label is never an operand.
Order schedule(const Net& n,int deleted) {
    Order order; std::array<bool,total> known{};
    std::fill_n(known.begin(),inputs,true);
    for (int pass=0;pass<total;++pass) {
        auto before=order.size();
        for (int i=inputs;i<total;++i)
            if (i!=deleted && !known[i] && known[n[i].a] && known[n[i].b]) {
                known[i]=true; order.push_back(i);
            }
        if (before==order.size()) break;
    }
    return order;
}
Word value(bool isOr,Word a,Word b) { return isOr ? a|b : a&b; }
Values run(const Net& n,const Order& order,int fixed=-1,Word forced=0) {
    Values w=initial;
    for (int i:order) w[i]=i==fixed ? forced : value(n[i].isOr,w[n[i].a],w[n[i].b]);
    return w;
}
bool legal(const Net& n,const Order& order) {
    return !n[output].isOr && std::all_of(order.begin(),order.end(),[&](int i){return n[i].a!=n[i].b;});
}
bool passes(const Net& n,const Values& w) {
    return w[output]==target && !((w[n[output].a]|w[n[output].b])&pins);
}

// A candidate for a final-AND operand must pass all 21 flags and reject both pins.
bool factor(Word x) { return (x&target)==target && !(x&pins); }
struct Signal { Word bits; int a=-1,b=-1; bool isOr=false; };
using Pool = std::vector<Signal>;
bool printWitness=true;
bool found(const Pool& pool,int a,int b) {
    if (a==b || !factor(pool[a].bits) || !factor(pool[b].bits) ||
        (pool[a].bits&pool[b].bits)!=target) return false;
    if (!printWitness) return true;
    std::cout<<"tail witness\n";
    for (unsigned i=0;i<pool.size();++i)
        if (pool[i].a>=0) std::cout<<i<<" "<<pool[i].isOr<<" "<<pool[i].a<<" "<<pool[i].b<<"\n";
    std::cout<<"AND "<<a<<" "<<b<<"\n";
    return true;
}
template<class F> bool eachNew(const Pool& pool,F test) {
    for (int a=0;a<int(pool.size());++a) for (int b=a+1;b<int(pool.size());++b)
        for (bool op:{false,true})
            if (test(Signal{value(op,pool[a].bits,pool[b].bits),a,b,op})) return true;
    return false;
}
// With two gates available before the root, the gates are independent or the
// second reads the first. The list stores wire identities even for equal values.
bool lastTwo(Pool& pool,int budget) {
    std::vector<int> old;
    for (int i=0;i<int(pool.size());++i) if (factor(pool[i].bits)) {
        for (int j:old) if (found(pool,i,j)) return true;
        old.push_back(i);
    }
    if (!budget) return false;
    std::vector<Signal> fresh;
    eachNew(pool,[&](Signal w){if (factor(w.bits)) fresh.push_back(w);return false;});
    int idx=int(pool.size());
    for (Signal w:fresh) {
        pool.push_back(w);
        for (int j:old) if (found(pool,idx,j)) return true;
        if (budget==2) for (Signal z:fresh) if ((w.bits&z.bits)==target) {
            pool.push_back(z);if (found(pool,idx,idx+1)) return true;pool.pop_back();
        }
        pool.pop_back();
    }
    if (budget<2) return false;
    return eachNew(pool,[&](Signal w){
        if (old.empty() && !factor(w.bits)) return false;
        pool.push_back(w);
        for (int i=0;i<idx;++i) for (bool op:{false,true}) {
            Signal z{value(op,w.bits,pool[i].bits),idx,i,op};
            if (!factor(z.bits)) continue;
            pool.push_back(z);
            for (int j:old) if (found(pool,idx+1,j)) return true;
            if (factor(w.bits) && found(pool,idx+1,idx)) return true;
            pool.pop_back();
        }
        pool.pop_back();return false;
    });
}
bool tailSearch(Pool& pool,int budget) {
    if (budget<=2) return lastTwo(pool,budget);
    if (lastTwo(pool,2)) return true;
    return eachNew(pool,[&](Signal w){
        pool.push_back(w);
        if (tailSearch(pool,budget-1)) return true;
        pool.pop_back();return false;
    });
}
int tails(const Net& n) {
    using Mask = std::uint64_t;
    std::vector<Mask> cuts{Word(1)<<output};
    const auto orig=run(n,schedule(n,-1));
    Pool positive;
    for (int i=0;i<39;++i) positive.push_back({orig[i]});
    printWitness=false;
    if (!tailSearch(positive,2)) return 2;
    printWitness=true;
    std::cout<<"restored a legal three-gate ending in the 28-gate positive control\n";
    for (int size=2;size<=6;++size) {
        std::vector<Mask> next;
        for (auto mask:cuts) for (int k=inputs;k<output;++k) if (!(mask>>k&1)) {
            bool closed=true;
            for (int j=k+1;j<total;++j) if (!(mask>>j&1) && (n[j].a==k||n[j].b==k)) closed=false;
            if (closed) next.push_back(mask|(Word(1)<<k));
        }
        std::sort(next.begin(),next.end());
        next.erase(std::unique(next.begin(),next.end()),next.end());
        cuts=next;
        int checked=0;
        for (Mask mask:cuts) if ((mask>>39&1) && (mask>>40&1)) {
            Pool pool;
            std::array<int,total> indices{};
            for (int k=0;k<total;++k) if (!(mask>>k&1)) {
                indices[k]=int(pool.size());
                if (k<inputs) pool.push_back({orig[k]});
                else pool.push_back({orig[k],indices[n[k].a],indices[n[k].b],n[k].isOr});
            }
            ++checked;
            if (tailSearch(pool,size-2)) return 1;
        }
        std::cout<<"terminal gates removed "<<size<<", closed cuts containing both operands "<<checked<<", no witness\n";
    }
    return 0;
}


// A four-vertex induced path obstructs simultaneous read-once factors.
void paths() {
    std::vector<int> induced;
    for (int mask=0;mask<(1<<inputs);++mask) if (__builtin_popcount(unsigned(mask))==4) {
        std::array<int,inputs> degree{};
        for (int p=0;p<7;++p) for (int l=0;l<7;++l)
            if ((mask>>p&1) && (mask>>(7+l)&1) && incident(p,l)) {
                ++degree[p]; ++degree[7+l];
            }
        if (std::count(degree.begin(),degree.end(),1)==2 &&
            std::count(degree.begin(),degree.end(),2)==2) induced.push_back(mask);
    }
    std::array<int,inputs+1> hits{};
    for (int x=0;x<(1<<inputs);++x)
        if (std::all_of(induced.begin(),induced.end(),[&](int p){return x&p;}))
            ++hits[__builtin_popcount(unsigned(x))];
    int k=0;while (!hits[k]) ++k;
    std::cout<<induced.size()<<" induced four-paths; minimum hitting set "<<k<<"; "<<hits[k]<<" minimizers\n";
    if (induced.size()!=84 || k!=5 || hits[k]!=14) std::abort();
}

int main() {
    boundary();
    paths();
    const Net original=seed();
    if (!passes(original,run(original,schedule(original,-1)))) return 2;
    std::uint64_t count=0, intermediates=0, surviving=0;
    for (int d=inputs;d<output;++d) for (int alias=0;alias<total;++alias) if (d!=alias) {
        Net n=original;
        for (int i=inputs;i<total;++i) if (i!=d) {
            if (n[i].a==d) n[i].a=alias;
            if (n[i].b==d) n[i].b=alias;
        }
        auto order=schedule(n,d);
        if (order.size()!=27) continue;
        ++intermediates;
        auto base=run(n,order);
        for (int k:order) {
            bool otherLegal=std::all_of(order.begin(),order.end(),[&](int i){return i==k||n[i].a!=n[i].b;});
            if (!otherLegal) continue;
            std::array<bool,total> descendant{};
            for (int i:order) descendant[i]=i==k || descendant[n[i].a] || descendant[n[i].b];
            auto lo=run(n,order,k,0), hi=run(n,order,k,tests);
            for (int a=0;a<total;++a) if (a!=d && !descendant[a])
            for (int b=a+1;b<total;++b) if (b!=d && !descendant[b])
            for (int op=0;op<=(k!=output);++op) {
                ++count;
                Word y=value(op,base[a],base[b]);
                auto select=[&](int i){return (lo[i]&~y)|(hi[i]&y);};
                if (select(output)!=target) continue;
                Word rootInputs=k==output ? base[a]|base[b] : select(n[output].a)|select(n[output].b);
                if (rootInputs&pins) continue;
                auto candidate=n;candidate[k]={bool(op),a,b};
                auto newOrder=schedule(candidate,d);
                if (newOrder.size()!=27 || !legal(candidate,newOrder) || !passes(candidate,run(candidate,newOrder))) return 3;
                ++surviving;
                std::cout<<"candidate: delete "<<d<<" alias "<<alias<<" change "<<k<<" "<<op<<" "<<a<<" "<<b<<"\n";
            }
        }
    }
    std::cout<<intermediates<<" acyclic bypasses; "<<count<<" legal replacements; "<<surviving<<" witnesses\n";
    return tails(original);
}
