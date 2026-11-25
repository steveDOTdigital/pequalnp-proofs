// Search for a 63-gate witness by bypassing a gate of the 64-gate control
// and resynthesizing any surviving gate. Build with c++ -O2 -std=c++17.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <set>
#include <string>
#include <vector>
using Word=std::uint64_t;
using Bits=std::array<Word,9>;
constexpr int wires=90;
int raw=26;
bool pointStars=true;
struct Gate { bool isOr; int a,b; };
using Net=std::array<Gate,wires>;
using Values=std::array<Bits,wires>;
std::vector<int> rows;
Values inputs{};
Bits goal{}, active{};

bool incident(int p,int l) {int d=(p-l+13)%13;return d==0||d==1||d==3||d==9;}
bool bit(int mask,int i) {return (mask>>i)&1;}
int transform(int mask,int k,int j,bool dual) {
    int r=0; for(int i=0;i<13;++i) {
        int z=(i*k+j)%13; if(dual)z=(13-z)%13;
        if(bit(mask,z))r|=1<<i;
    }
    return r;
}
void setup() {
    for(int p=0;p<13;++p)for(int l=0;l<13;++l)
        if(incident(p,l))rows.push_back((1<<p)|(1<<(13+l)));
    std::set<int> negatives;
    const int seeds[][2]={{7,904},{13,2848},{19,708},{21,2720},{25,2656},{37,2440},{41,2370},{133,808}};
    if (raw == 26) {
        for(auto& s:seeds)for(int k:{1,3,9})for(int j=0;j<13;++j)for(int d:{0,1})
            negatives.insert(transform(s[d],k,j,d)|(transform(s[1-d],k,j,d)<<13));
    } else {
        for (int points=0; points<(1<<13); ++points) {
            if (__builtin_popcount(static_cast<unsigned>(points)) != 4) continue;
            int missing=0;
            bool quad=true;
            for (int l=0; l<13; ++l) {
                int hits=0;
                for (int p=0; p<13; ++p) if (bit(points,p) && incident(p,l)) ++hits;
                if (hits>2) {quad=false;break;}
                if (!hits) missing |= 1<<l;
            }
            if (quad) negatives.insert(points|(missing<<13));
        }
    }
    if(rows.size()!=52||negatives.size()!=(raw==26?468u:234u))std::abort();
    rows.insert(rows.end(),negatives.begin(),negatives.end());
    for(unsigned r=0;r<rows.size();++r) {
        Word b=Word(1)<<(r%64);active[r/64]|=b;
        if(r<52)goal[r/64]|=b;
        for(int i=0;i<26;++i)if(bit(rows[r],i))inputs[i][r/64]|=b;
        if(raw==27 && (rows[r] & (3<<(pointStars?13:0))))inputs[26][r/64]|=b;
    }
}
Net stars() {
    Net n{};int next=raw;
    auto gate=[&](bool isOr,int a,int b){n[next]={isOr,a,b};return next++;};
    std::vector<int> terminals;
    for(int center=0;center<13;++center) {
        std::vector<int> neighbors;
        for(int i=0;i<13;++i) {
            if (pointStars ? incident(center,i) : incident(i,center))
                neighbors.push_back((pointStars?13:0)+i);
        }
        if (raw==27) {
            int first=pointStars?13:0;
            auto a=std::find(neighbors.begin(),neighbors.end(),first);
            auto b=std::find(neighbors.begin(),neighbors.end(),first+1);
            if (a!=neighbors.end() && b!=neighbors.end()) {
                *a=26;
                neighbors.erase(b);
            }
        }
        int t=neighbors.front();
        for(size_t j=1;j<neighbors.size();++j)t=gate(true,t,neighbors[j]);
        terminals.push_back(gate(false,center+(pointStars?0:13),t));
    }
    int out=terminals[0];
    for(int j=1;j<13;++j)out=gate(true,out,terminals[j]);
    if(out!=89)std::abort();
    return n;
}
std::vector<int> order(const Net& n,int skip) {
    std::array<bool,wires> ready{};std::fill_n(ready.begin(),raw,true);
    std::vector<int> done;
    for(;;) {
        auto before=done.size();
        for(int i=raw;i<wires;++i)if(i!=skip&&!ready[i]&&ready[n[i].a]&&ready[n[i].b]) {
            ready[i]=true;done.push_back(i);
        }
        if(before==done.size())return done;
    }
}
Values run(const Net& n,const std::vector<int>& schedule,int fix=-1,bool high=false) {
    Values v=inputs;
    for(int i:schedule)for(int w=0;w<9;++w) {
        auto g=n[i];
        v[i][w]=i==fix?(high?active[w]:0):(g.isOr?v[g.a][w]|v[g.b][w]:v[g.a][w]&v[g.b][w]);
    }
    return v;
}
int main(int argc,char** argv) {
    if (argc==2) {
        const std::string mode=argv[1];
        if(mode!="--free-points" && mode!="--free-lines")return 1;
        raw=27;
        pointStars=mode=="--free-lines";
    } else if(argc!=1)return 1;
    setup();Net base=stars();
    if(run(base,order(base,-1))[89]!=goal)return 2;
    std::uint64_t bypasses=0,locations=0,candidates=0;
    for(int d=raw;d<wires;++d)for(int alias=0;alias<wires;++alias)if(alias!=d) {
        Net n=base;int out=d==89?alias:89;
        for(int i=raw;i<wires;++i)if(i!=d) {
            if(n[i].a==d)n[i].a=alias;
            if(n[i].b==d)n[i].b=alias;
        }
        auto plan=order(n,d);if(plan.size()!=static_cast<unsigned>(wires-raw-1))continue;
        ++bypasses;auto before=run(n,plan);
        for(int k:plan) {
            auto lo=run(n,plan,k,false)[out],hi=run(n,plan,k,true)[out];
            Bits must{},ban{};bool possible=true;
            for(int j=0;j<9;++j) {
                if(((lo[j]&~before[k][j])|(hi[j]&before[k][j]))!=before[out][j])return 4;
                if((lo[j]&~goal[j])||(goal[j]&~hi[j]))possible=false;
                must[j]=goal[j]&~lo[j];ban[j]=~goal[j]&hi[j];
            }
            if(!possible)continue;
            ++locations;
            std::array<bool,wires> down{};
            for(int i:plan)down[i]=i==k||down[n[i].a]||down[n[i].b];
            for(int a=0;a<wires;++a)if(a!=d&&!down[a])
            for(int b=a;b<wires;++b)if(b!=d&&!down[b])
            for(bool op:{false,true}) {
                ++candidates;bool good=true;
                for(int j=0;j<9;++j) {
                    Word v=op?before[a][j]|before[b][j]:before[a][j]&before[b][j];
                    if((must[j]&~v)||(ban[j]&v)){good=false;break;}
                }
                if(good) {
                    auto candidate=n;candidate[k]={op,a,b};auto finalOrder=order(candidate,d);
                    if(finalOrder.size()!=static_cast<unsigned>(wires-raw-1)||run(candidate,finalOrder)[out]!=goal)return 3;
                    std::cout<<"witness delete/alias/change/op/inputs: "<<d<<" "<<alias<<" "<<k<<" "<<op<<" "<<a<<" "<<b<<"\n";
                    return 0;
                }
            }
        }
    }
    std::cout<<bypasses<<" acyclic bypasses; "<<locations<<" viable gate locations; "<<candidates<<" candidate gates; zero witnesses\n";
}
