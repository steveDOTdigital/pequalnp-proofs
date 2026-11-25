// Two-gate prefix exclusions for the 44-flag graph of case 9792.
#define main mcgee_main
#include "cubic-pair-restrictions.cpp"
#undef main
#include <iostream>

using Gate = std::array<int, 3>; // raw left, raw right, operation (zero AND, one OR)

struct PrefixBounds {
    Bounder &lower;
    Mask s;
    int budget;
    std::array<int,24> lo{}, hi{};
    std::vector<Gate> first;

    PrefixBounds(Bounder &b, Mask mask, int size) : lower(b), s(mask), budget(size) {
        for (Mask k=s;k;k&=k-1) {
            int v=::first(k);
            auto a=b.pin(s,v,v,0), c=b.pin(s,v,v,1);
            lo[v]=a.nonconstant ? size-a.lower : size;
            hi[v]=c.nonconstant ? size-c.lower : size;
        }
    }

    // On a partially fixed cube is c essential? A neighboring true singleton
    // already suffices. Otherwise a still-free neighbor that touches no
    // fixed true vertex can be selected without creating an earlier edge.
    bool sensitive(int c, Mask fixed, Mask ones) const {
        Mask forbidden=0;
        for (Mask k=ones;k;k&=k-1) forbidden |= lower.near[::first(k)];
        if (forbidden & ones) return false;
        return (lower.near[c] & (ones | (s & ~fixed & ~forbidden))) != 0;
    }

    struct Reads {
        std::array<int,24> times{}, ands{}, ors{};
        Mask used=0;
        void read(int v, int op) {
            used |= 1u<<v;
            (op ? ors[v] : ands[v])++;
            times[v]=std::max(times[v],ors[v]+ands[v]);
        }
    };

    void addRaw(Reads &r, Gate g) const {
        auto [a,b,op]=g; r.read(a,op); r.read(b,op);
        for (auto [v,w] : {std::pair<int,int>{a,b},{b,a}})
            if (sensitive(v,1u<<w,op ? 1u<<w : 0))
                r.times[v]=std::max(2,r.times[v]);
    }

    bool possible(const Reads &r) const {
        std::array<int,24> minReads{};
        for (Mask k=r.used;k;k&=k-1) {
            int v=::first(k);
            for(int total=r.times[v];total<=std::min(lo[v],hi[v]) && !minReads[v];++total)
                for(int a=r.ands[v];a<=total-r.ors[v];++a)
                    if(total+std::min(2,a)<=lo[v] && total+std::min(2,total-a)<=hi[v]) {
                        minReads[v]=total; break;
                    }
            if (!minReads[v]) return false;
        }
        int used=count(s & ~r.used);
        for (Mask k=r.used;k;k&=k-1) used+=minReads[::first(k)];
        if (used > budget+1) return false;
        for (Mask gone=r.used;gone;gone=(gone-1)&r.used) {
            Mask retained=lower.active(s & ~gone);
            if(!retained) continue;
            int payment=lower.solve(retained);
            for (Mask k=gone;k;k&=k-1) payment+=minReads[::first(k)];
            if(payment>budget) return false;
        }
        return true;
    }

    bool survives() {
        for(Mask k=s;k;k&=k-1) for(Mask j=k&(k-1);j;j&=j-1)
            for(int op=0;op<2;++op) {
                int a=::first(k), b=::first(j);
                if(!op && !(lower.near[a]&(1u<<b)))continue;
                Gate g{a,b,op}; Reads r; addRaw(r,g);
                if(possible(r)) first.push_back(g);
            }
        for(Gate g:first) {
            auto [a,b,op]=g; Reads r; addRaw(r,g);
            for(Gate h:first) if(h!=g) {
                Reads t=r;addRaw(t,h);
                if(possible(t))return true;
            }
            Mask pair=(1u<<a)|(1u<<b);
            for(Mask j=s & ~pair;j;j&=j-1) for(int y=0;y<2;++y) {
                int c=::first(j);Reads t=r;t.read(c,y);
                for(int x=0;x<4;++x) {
                    bool out=op ? x!=0 : x==3;
                    if(out!=bool(y))continue;
                    Mask ones=((x&1)?1u<<a:0)|((x&2)?1u<<b:0);
                    if(sensitive(c,pair,ones))t.times[c]=2;
                }
                if(possible(t))return true;
            }
        }
        return false;
    }
};

int main(int argc,char **argv){
    int depth=argc>1 ? std::stoi(argv[1]) : 2;
    if(depth<0 || depth>4)return 2;
    std::vector<Mask> graph(24);
    for(auto [a,b]:std::vector<std::pair<int,int>>{{0,15},{0,21},{0,23},{1,16},{1,22},{2,13},{2,17},{2,23},{3,13},{3,14},{3,18},{4,14},{4,15},{4,19},{5,13},{5,15},{5,16},{5,20},{6,14},{6,16},{6,17},{6,21},{7,15},{7,17},{7,18},{7,22},{8,16},{8,18},{8,19},{8,23},{9,17},{9,19},{9,20},{10,18},{10,20},{10,21},{11,13},{11,19},{11,21},{11,22},{12,14},{12,20},{12,22},{12,23}}){
        graph[a]|=1u<<b;graph[b]|=1u<<a;
    }
    Bounder signedBase(graph,true,-1),mono(graph,true,0,nullptr,&signedBase);
    Mask all=(1u<<24)-1;
    std::cout<<"Initial signed "<<signedBase.solve(all)<<" and monotone "<<mono.solve(all)<<std::endl;
    for(int n=24-depth;n<=24;++n){
        int checked=0, improved=0;
        for(Mask s=all;;s=(s-1)&all){
            if(count(s)==n && mono.active(s)==s){
                int initial=mono.solve(s), value=initial;
                while(value<mono.upper(s) && !PrefixBounds(mono,s,value).survives())++value;
                mono.memo[s]=value; ++checked;
                if(value>initial)++improved;
            }
            if(!s)break;
        }
        std::cout<<"Order "<<n<<" checked "<<checked<<" strengthened "<<improved<<std::endl;
    }
    std::cout<<"Full monotone lower "<<mono.solve(all)<<" upper "<<mono.upper(all)<<std::endl;
}
