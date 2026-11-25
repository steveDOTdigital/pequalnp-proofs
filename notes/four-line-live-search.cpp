// Exact bounded synthesis on the 12 positive and 12 maximal negative rows
// of the subdivision of K4, with selected complementary point-pair ORs free.
#include <algorithm>
#include <array>
#include <cassert>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>

using Bits = std::uint32_t;
using Clock = std::chrono::steady_clock;
Bits rowMask,positives,negativeMask;
int nNeg;
std::vector<std::array<int,2>> flags;
struct Cover {
    std::uint64_t v[4]{};
    Cover operator|(const Cover& b) const {
        return {{v[0]|b.v[0],v[1]|b.v[1],v[2]|b.v[2],v[3]|b.v[3]}};
    }
    bool includes(const Cover& x) const {
        return !(x.v[0]&~v[0]) && !(x.v[1]&~v[1]) && !(x.v[2]&~v[2]) && !(x.v[3]&~v[3]);
    }
};
struct Wire {Bits value; Cover cover;};
struct Gate {int left,right; bool useOr;};
const std::array<int,6> ends={3,5,9,6,10,12};
std::vector<int> rows;
std::array<Wire,40> wires;
std::array<Gate,25> gates;
std::array<std::array<bool,15>,15> first;
int width,limit;
bool pinFifth=false;
Bits pinYes=0,pinAll=0;
std::array<Bits,40> pinned{};
std::uint64_t states=0,candidates=0,budget;
bool stopped=false,requireAnd=false,acceptSmaller=false;
Clock::time_point deadline;
Cover all;
bool target(int row) {
    for(auto e:flags) if((row&(1<<e[0])) && (row&(1<<e[1])))return true;
    return false;
}
Cover rectangle(Bits x) {
    Cover c;
    std::uint64_t cols=(~(x>>flags.size())) & negativeMask;
    for(int i=0;i<(int)flags.size();++i) if(x&(1u<<i)){
        int bit=i*nNeg, word=bit/64, shift=bit%64;
        c.v[word]|=cols<<shift;
        if(shift+nNeg>64)c.v[word+1]|=cols>>(64-shift);
    }
    return c;
}
bool search(const std::vector<int>& live,int depth,int spare,int lastRight,int lastLeft,int saved) {
    if(++states>budget || ((states&16383)==0 && Clock::now()>deadline)){
        stopped=true;return false;
    }
    if(live.size()==1)
        return wires[live[0]].value==positives && (!requireAnd || (acceptSmaller && depth<limit) || (depth>0 && !gates[depth-1].useOr));
    // With no rereads left, the suffix is a tree on the live wires. Each
    // child of an AND root must receive some true leaf on every positive row.
    if(requireAnd && spare==0){
        Bits seen=0,twice=0;
        for(int j:live){
            twice|=seen&wires[j].value;
            seen|=wires[j].value;
        }
        if((twice&positives)!=positives)return false;
    }
    int index=width+depth;
    if(depth==limit)return false;
    // A positive/negative pair has to remain separated by some live wire.
    // Removing either or both operands loses the cells that no survivor covers.
    for(int ri=1;ri<(int)live.size();++ri){
        int b=live[ri];
        if(b<lastRight)continue;
        for(int li=0;li<ri;++li){
            int a=live[li];
            if((b==lastRight && a<lastLeft) || (depth==0 && !first[a][b]))continue;
            Cover remainder;
            for(int i=0;i<(int)live.size();++i)
                if(i!=ri && i!=li)remainder=remainder|wires[live[i]].cover;
            for(int op=0;op<2;++op){
                Bits x=op?(wires[a].value|wires[b].value):(wires[a].value&wires[b].value);
                Bits test=op?positives:(rowMask^positives);
                if((wires[a].value&test)==(x&test) || (wires[b].value&test)==(x&test))continue;
                if(!(x&positives) || ((x|positives)==rowMask))continue;
                bool replaceable=false;
                for(int i=0;i<index;++i){
                    Bits old=wires[i].value;
                    // Substitution through any monotone suffix preserves all
                    // accepted flags and all rejected maximal independent rows.
                    if(!(x&positives&~old) && !(old&(rowMask^positives)&~x)){
                        replaceable=true;
                        break;
                    }
                }
                if(replaceable)continue;
                wires[index]={x,rectangle(x)};
                Cover base=remainder|wires[index].cover;
                ++candidates;
                int lowerSaved=saved;
                if(pinFifth){
                    Bits val=op?(pinned[a]|pinned[b]):(pinned[a]&pinned[b]);
                    pinned[index]=val;
                    // Delete line 3 to obtain the subdivided K4. Substituting
                    // a better prior wire is valid on every monotone suffix.
                    for(int k=0;k<index;++k){
                        Bits old=pinned[k];
                        if(!(val&pinYes&~old) && !(old&(pinAll^pinYes)&~val)){
                            ++lowerSaved;
                            break;
                        }
                    }
                    // The designated output is retained if it must be AND.
                    // An ordinary circuit at 17 gates has the same savings cap.
                    if(lowerSaved>2 && (depth+1<limit || x!=positives))continue;
                    if(lowerSaved>3)continue;
                }
                for(int keep=0;keep<4;++keep){
                    int cost=(keep&1)+((keep>>1)&1);
                    if(cost>spare)continue;
                    if(pinFifth && lowerSaved>=2 && ((a==3 && (keep&1)) || (b==3 && (keep&2))) && x!=positives)continue;
                    Cover remaining=base;
                    if(keep&1)remaining=remaining|wires[a].cover;
                    if(keep&2)remaining=remaining|wires[b].cover;
                    if(!remaining.includes(all))continue;
                    std::vector<int> next;
                    next.reserve(live.size()+1);
                    for(int j:live)if((j!=a || (keep&1)) && (j!=b || (keep&2)))next.push_back(j);
                    next.push_back(index);
                    gates[depth]={a,b,op==1};
                    if(search(next,depth+1,spare-cost,b,a,lowerSaved))return true;
                    if(stopped)return false;
                }
            }
        }
    }
    return false;
}
int main(int argc,char**argv) {
    if(argc<5 || argc>8)return 2;
    std::string shape=argc>=6?argv[5]:"k4";
    bool theta=shape=="theta", triple=shape=="triple", pencil=shape=="pencil";
    bool twoTriples=shape=="two-triples";
    if(shape!="k4" && !theta && !triple && !pencil && !twoTriples)return 2;
    int drop=argc==8?std::atoi(argv[7]):-1;
    if(argc==8 && (!twoTriples || drop<0 || drop>=11))return 2;
    if(argc>=7){
        acceptSmaller=std::string(argv[6])=="and-or-smaller";
        requireAnd=std::string(argv[6])=="and" || acceptSmaller;
        if(!requireAnd && std::string(argv[6])!="any")return 2;
    }
    int arms=triple?3:4;
    int raw=twoTriples?11:triple?8:pencil?9:10;
    int helpers=std::atoi(argv[1]);limit=std::atoi(argv[2]);budget=std::strtoull(argv[3],nullptr,10);
    if(helpers<0||helpers>3||limit<0||limit>20)return 2;
    deadline=Clock::now()+std::chrono::seconds(std::atoi(argv[4]));
    if(twoTriples){
        flags={{0,6},{0,7},{0,9},{1,7},{1,8},{1,10},{2,5},{2,8},{2,9},
               {3,9},{3,10},{4,5},{4,6},{4,10}};
    }else if(theta || triple){
        if(helpers)return 2;
        for(int i=0;i<arms;++i){
            flags.push_back({0,2+i});
            flags.push_back({2+i,2+arms+i});
            flags.push_back({2+arms+i,1});
        }
    }else if(pencil){
        if(helpers)return 2;
        for(int i=0;i<arms;++i){
            flags.push_back({0,1+i});
            flags.push_back({1+i,1+arms+i});
        }
    }else{
        for(int i=0;i<6;++i)for(int j=0;j<4;++j)if(ends[i]&(1<<j))flags.push_back({j,4+i});
    }
    auto originalFlags=flags;
    auto remap=[&](int v){return v-int(drop>=0 && v>drop);};
    if(drop>=0){
        --raw;
        flags.clear();
        for(auto [a,b]:originalFlags)if(a!=drop && b!=drop)
            flags.push_back({remap(a),remap(b)});
    }
    for(auto e:flags)rows.push_back((1<<e[0])|(1<<e[1]));
    for(int x=0;x<(1<<raw);++x)if(!target(x)){
        bool maximal=true;
        for(int j=0;j<raw;++j)if(!(x&(1<<j)) && !target(x|(1<<j)))maximal=false;
        if(maximal)rows.push_back(x);
    }
    nNeg=rows.size()-flags.size();
    assert(rows.size()<32 && flags.size()*nNeg<=256);
    rowMask=(1u<<rows.size())-1;
    positives=(1u<<flags.size())-1;
    negativeMask=(1u<<nNeg)-1;
    std::vector<int> masks;
    for(int i=0;i<raw;++i)masks.push_back(1<<i);
    if(twoTriples){
        auto addFree=[&](int bit,int a,int b){
            if((helpers&bit) && a!=drop && b!=drop)masks.push_back((1<<remap(a))|(1<<remap(b)));
        };
        addFree(1,5,7);
        addFree(2,6,8);
    }else for(int i=0;i<helpers;++i)masks.push_back((1<<(4+i))|(1<<(9-i)));
    width=masks.size();
    pinFifth=twoTriples && drop<0 && requireAnd && limit==18;
    if(pinFifth){
        std::vector<int> tests;
        for(auto [l,r]:flags)if(l!=3)tests.push_back((1<<l)|(1<<r));
        pinYes=(1u<<tests.size())-1;
        for(int x=0;x<(1<<raw);++x)if(!(x&(1<<3)) && !target(x)){
            bool max=true;
            for(int j=0;j<raw;++j)if(j!=3 && !(x&(1<<j)) && !target(x|(1<<j)))max=false;
            if(max)tests.push_back(x);
        }
        assert(tests.size()==24);
        pinAll=(1u<<tests.size())-1;
        for(int i=0;i<width;++i)for(int j=0;j<(int)tests.size();++j)
            if(masks[i]&tests[j])pinned[i]|=1u<<j;
    }
    std::vector<int> live;
    for(int i=0;i<width;++i){
        live.push_back(i);
        Bits v=0;
        for(int j=0;j<(int)rows.size();++j)if(masks[i]&rows[j])v|=1u<<j;
        wires[i]={v,rectangle(v)};
    }
    std::array<int,4> p={0,1,2,3};
    for(int a=0;a<width;++a)for(int b=a+1;b<width;++b)first[a][b]=true;
    if(twoTriples){
        std::array<int,5> perm={0,1,2,3,4};
        std::vector<int> hood(6);
        for(auto [line,point]:originalFlags)hood[point-5]|=1<<line;
        do{
            std::vector<int> im(perm.begin(),perm.end());
            for(int mask:hood){
                int moved=0;
                for(int j=0;j<5;++j)if(mask&(1<<j))moved|=1<<perm[j];
                auto it=std::find(hood.begin(),hood.end(),moved);
                if(it==hood.end())break;
                im.push_back(5+(it-hood.begin()));
            }
            if(im.size()!=11 || (drop>=0 && im[drop]!=drop))continue;
            if(drop>=0){
                im.erase(im.begin()+drop);
                for(int &v:im)v=remap(v);
            }
            for(int j=raw;j<width;++j){
                int moved=0;
                for(int k=0;k<raw;++k)if(masks[j]&(1<<k))moved|=1<<im[k];
                auto it=std::find(masks.begin(),masks.end(),moved);
                if(it==masks.end())break;
                im.push_back(it-masks.begin());
            }
            if(static_cast<int>(im.size())!=width)continue;
            for(int a=0;a<width;++a)for(int b=a+1;b<width;++b)
                if(std::make_pair(std::max(im[a],im[b]),std::min(im[a],im[b]))<std::make_pair(b,a))
                    first[a][b]=false;
        }while(std::next_permutation(perm.begin(),perm.end()));
    }else do {
        std::vector<int> im(p.begin(),p.end());
        for(int e:ends){
            int z=0;for(int i=0;i<4;++i)if(e&(1<<i))z|=1<<p[i];
            im.push_back(4+(std::find(ends.begin(),ends.end(),z)-ends.begin()));
        }
        if(triple && p[3]!=3)continue;
        if(theta || triple || pencil){
            int start=pencil?1:2;
            im=pencil?std::vector<int>{0}:std::vector<int>{0,1};
            for(int j=0;j<arms;++j)im.push_back(start+p[j]);
            for(int j=0;j<arms;++j)im.push_back(start+arms+p[j]);
        }
        bool legal=true;
        for(int i=raw;i<width;++i){
            int z=0;for(int j=0;j<raw;++j)if(masks[i]&(1<<j))z|=1<<im[j];
            auto it=std::find(masks.begin(),masks.end(),z);
            if(it==masks.end()){legal=false;break;}
            im.push_back(it-masks.begin());
        }
        if(legal)for(int a=0;a<width;++a)for(int b=a+1;b<width;++b)
            if(std::make_pair(std::max(im[a],im[b]),std::min(im[a],im[b]))<std::make_pair(b,a))first[a][b]=false;
    }while(std::next_permutation(p.begin(),p.end()));
    all=rectangle(positives);
    bool found=limit>=width-1 && search(live,0,limit-width+1,-1,-1,0);
    std::cout<<(found?"SAT":stopped?"INCOMPLETE":"EXCLUDED")<<" helpers="<<helpers
             <<" gates="<<limit<<" states="<<states<<" candidates="<<candidates<<"\n";
    if(found)for(int x=0;x<(1<<raw);++x){
        std::vector<bool> value;
        for(int m:masks)value.push_back((x&m)!=0);
        for(int j=0;j<limit;++j){
            auto g=gates[j];
            value.push_back(g.useOr?(value[g.left]||value[g.right]):(value[g.left]&&value[g.right]));
            if(wires[width+j].value==positives){assert(value.back()==target(x));break;}
        }
    }
    if(found)for(int j=0;j<limit;++j){
        std::cout<<width+j<<" "<<gates[j].left<<" "<<gates[j].right<<" "<<gates[j].useOr<<"\n";
        if(wires[width+j].value==positives)break;
    }
}
