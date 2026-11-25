// Gate elimination on vertex restrictions of the McGee graph, with all
// wire inversions free. No truth table on 24 variables is allocated.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <limits>
#include <vector>
using Mask=std::uint32_t;
int count(Mask m){return __builtin_popcount(m);}
int first(Mask m){return __builtin_ctz(m);}
struct Bounder{
    int n;
    std::vector<Mask> near;
    std::vector<std::int8_t> memo,alphaMemo;
    std::uint64_t calls=0,cores=0,pairs=0;
    bool pairRule;
    int mode;
    Bounder *previous,*freeModel;
    explicit Bounder(std::vector<Mask> g,bool usePair,int type=-2,Bounder* prev=nullptr,Bounder* base=nullptr):
        n(g.size()),near(g),memo(1u<<n,-1),alphaMemo(base?0:(1u<<n),-1),pairRule(usePair),
        mode(type),previous(prev),freeModel(base){if(!base)alphaMemo[0]=0;memo[0]=0;}
    int independent(Mask s){
        if(alphaMemo.empty())return freeModel->independent(s);
        if(alphaMemo[s]>=0)return alphaMemo[s];
        int v=first(s);Mask rest=s & ~(1u<<v);
        return alphaMemo[s]=std::max(independent(rest),1+independent(rest&~near[v]));
    }
    Mask active(Mask s)const{
        Mask a=0;
        for(Mask t=s;t;t&=t-1){int v=first(t);if(near[v]&s)a|=1u<<v;}
        return a;
    }
    int edges(Mask s)const{
        int e=0;for(Mask t=s;t;t&=t-1)e+=count(near[first(t)]&s);return e/2;
    }
    int upper(Mask s){return edges(s)+count(s)-independent(s)-1;}
    Mask component(Mask s,int v)const{
        Mask seen=1u<<v,front=seen;
        while(front){int w=first(front);front&=front-1;Mask add=(s&near[w])&~seen;seen|=add;front|=add;}
        return seen;
    }
    struct Pin{int lower,remaining;bool nonconstant;};
    Pin pin(Mask s,int v,int w,int high){
        Mask fixed=(1u<<v)|(1u<<w),alarms=0;
        if(high&1)alarms|=near[v];
        if(high&2)alarms|=near[w];
        if(high==3 && (near[v]&(1u<<w)))return {0,0,false};
        alarms &=s&~fixed;
        Mask core=active(s&~(fixed|alarms));
        int r=count(alarms);
        return {core?solve(core)+r:std::max(0,r-1),r+count(core),bool(r||core)};
    }
    int solve(Mask s){
        if(memo[s]>=0)return memo[s];
        ++calls;
        Mask a=active(s);if(a!=s)return memo[s]=solve(a);
        int num=count(s),goal=upper(s);
        bool pseudoforest=true;
        for(Mask left=s;left;){

            Mask comp=component(s,first(left));left&=~comp;
            int m=edges(comp);
            if(m>count(comp))pseudoforest=false;
            if(m==count(comp)-1){
                // An induced tree disjunct adds its edge and cover counts
                // to a nonconstant disjunct on disjoint inputs.
                return memo[s]=comp==s?goal:upper(comp)+1+solve(s&~comp);
            }
        }
        if(mode==0 && pseudoforest)return memo[s]=goal;
        std::array<int,24> degree{}, low{},high{};
        // Cheapest leaf peel first. These two pin budgets follow by direct
        // reader elimination; they need no lower bound for the rest yet.
        for(Mask t=s;t;t&=t-1){int v=first(t);degree[v]=count(near[v]&s);}
        for(Mask t=s;t;t&=t-1){
            int v=first(t);if(degree[v]!=1)continue;
            int p=first(near[v]&s);
            bool twin=false;
            for(Mask j=near[p]&s&~(1u<<v);j;j&=j-1)if(degree[first(j)]==1)twin=true;
            if(twin)return memo[s]=1+solve(s&~(1u<<v));
            if(degree[p]==2){
                auto z=pin(s,v,v,0),o=pin(s,v,v,1);
                int lb=std::max({z.lower+1,o.lower+1,std::min(z.lower,o.lower)+2});
                if(lb==goal)return memo[s]=lb;
                // Other choices can strengthen a non-tight descent.
                break;
            }
        }
        ++cores;
        int simple=num-1;
        for(Mask t=s;t;t&=t-1){
            int v=first(t);auto z=pin(s,v,v,0),o=pin(s,v,v,1);
            low[v]=z.lower;high[v]=o.lower;
            for(Pin p:{z,o})if(p.nonconstant)simple=std::max(simple,p.lower+num-p.remaining);
        }
        if(mode>=0)simple=std::max(simple,freeModel->solve(s));
        if(mode==0){
            Mask d=0;bool cubic=true;
            for(Mask t=s;t;t&=t-1){int v=first(t);if(degree[v]>=2)d|=1u<<v;if(degree[v]!=3)cubic=false;}
            int cover=count(d)-independent(d);
            int extra=(d==s && ((edges(s)>num && 2*cover<=num) || (cubic && 3*(num-cover)>cover)));
            simple=std::max(simple,num-1+cover+extra);
        }
        if(mode>0)simple=std::max(simple,std::min(previous->solve(s),freeModel->solve(s)+mode));
        if(simple==goal)return memo[s]=goal;
        int best=goal;
        if(mode>0){
            // When the first gate is a NOT, its pin removes that NOT. With
            // exactly one NOT an essential increasing input must bypass it.
            for(Mask t=s;t;t&=t-1){int v=first(t);
                auto z=previous->pin(s,v,v,0),o=previous->pin(s,v,v,1);
                best=std::min(best,std::max(z.lower,o.lower)+(mode==1?3:2));
            }
        }
        for(Mask outer=s;outer;outer&=outer-1){
            int v=first(outer);Mask vb=1u<<v;
            for(Mask inner=outer&(outer-1);inner;inner&=inner-1){
                int w=first(inner);Mask wb=1u<<w, fixed=vb|wb;
                Mask nv=near[v]&s&~fixed,nw=near[w]&s&~fixed;
                bool adj=near[v]&wb;
                bool four=nv&&nw&&(nv!=nw)&&(adj||((nv&~nw)&&(nw&~nv)));
                int both=0;
                if(pairRule){
                    for(int bits=0;bits<4;++bits){auto q=pin(s,v,w,bits);
                        if(q.nonconstant){both=std::max(both,q.lower);simple=std::max(simple,q.lower+num-q.remaining);}
                    }
                }
                for(int av=0;av<2;++av)for(int aw=0;aw<2;++aw){
                    if(mode>=0 && av!=aw)continue;
                    bool rv=aw?(adj||bool(nv&~nw)):bool(nv);
                    bool rw=av?(adj||bool(nw&~nv)):bool(nw);
                    int need=std::max({low[v]+1+(!av)+rv, high[v]+1+av+rv,
                        low[w]+1+(!aw)+rw, high[w]+1+aw+rw});
                    if(mode>=-1){
                        auto repeat=[&](int x,int control){
                            int c=control?high[x]:low[x],u=control?low[x]:high[x];
                            return std::min(std::max(c+4,u+2),std::max(c+3,u+3));
                        };
                        if(rv)need=std::max(need,repeat(v,av));
                        if(rw)need=std::max(need,repeat(w,aw));
                    }
                    if(pairRule){
                        int saved=2+int(rv||rw)+int(rv&&rw&&four);
                        need=std::max(need,both+saved);
                    }
                    best=std::min(best,need);
                }
                ++pairs;
            }
        }
        int ans=std::max(simple,best);assert(ans<=goal);
        return memo[s]=ans;
    }
};
std::vector<Mask> cage(){
    std::vector<Mask> ns(24);
    auto edge=[&](int a,int b){ns[a]|=1u<<b;ns[b]|=1u<<a;};
    int offset[3]={12,7,-7};
    for(int i=0;i<24;++i){edge(i,(i+1)%24);edge(i,(i+24+offset[i%3])%24);}
    for(auto a:ns)assert(count(a)==3);
    return ns;
}
int main(int argc,char**argv){
    if(argc>1 && std::string(argv[1])=="formula"){
        auto ns=cage();Bounder b(ns,false);Mask all=(1u<<24)-1;
        std::array<int,25> bySize;
        bySize.fill(1000);
        int best=1000;Mask witness=0;
        for(Mask bad=0;bad<=all;++bad){
            Mask rest=all^bad,active=b.active(rest);
            int k=count(bad), residual=b.edges(active)+count(active)-b.independent(active);
            int total=3*k+count(rest^active)+residual-1+int(k!=0);
            if(total<best){best=total;witness=bad;}
            bySize[k]=std::min(bySize[k],total);
        }
        std::cout<<"Signed formula lower "<<best<<" minimizing subset mask "<<witness<<"\n";
        for(int i=0;i<25;++i)std::cout<<i<<":"<<bySize[i]<<" ";
        std::cout<<"\n";return 0;
    }
    if(argc>1 && std::string(argv[1])=="polarity"){
        auto ns=cage();Mask s=(1u<<24)-1;
        Bounder binary(ns,true,-1),mono(ns,true,0,nullptr,&binary),single(ns,true,1,&mono,&binary),
            two(ns,true,2,&single,&binary),three(ns,true,3,&two,&binary);
        for(Bounder* b:{&binary,&mono,&single,&two,&three}){
            std::cout<<"Mode "<<b->mode<<" lower "<<b->solve(s)<<" upper "<<b->upper(s)
                     <<" zero "<<b->pin(s,0,0,0).lower<<" high "<<b->pin(s,0,0,1).lower<<std::endl;
        }
        return 0;
    }
    bool paired=argc==1 || std::string(argv[1])!="single";
    Bounder b(cage(),paired);Mask s=(1u<<24)-1;
    int lower=b.solve(s),upper=b.upper(s);
    std::cout<<"McGee "<<(paired?"pair":"single")<<" lower "<<lower<<" upper "<<upper<<" masks "<<b.calls
             <<" cyclic cores "<<b.cores<<" first pairs "<<b.pairs<<"\n";
    std::cout<<"Vertices zero/high lower and cost of simultaneous zero on an incident edge\n";
    for(int v=0;v<3;++v){
        std::cout<<v<<" "<<b.pin(s,v,v,0).lower<<" "<<b.pin(s,v,v,1).lower;
        for(Mask t=b.near[v];t;t&=t-1)std::cout<<" "<<b.pin(s,v,first(t),0).lower;
        std::cout<<"\n";
    }
}
