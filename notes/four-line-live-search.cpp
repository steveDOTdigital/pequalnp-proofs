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
std::uint64_t states=0,candidates=0,budget;
bool stopped=false;
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
bool search(const std::vector<int>& live,int depth,int spare,int lastRight,int lastLeft) {
    if(++states>budget || ((states&16383)==0 && Clock::now()>deadline)){
        stopped=true;return false;
    }
    if(live.size()==1)return wires[live[0]].value==positives;
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
                bool duplicate=false;
                for(int i=0;i<index;++i)if(wires[i].value==x){duplicate=true;break;}
                if(duplicate)continue;
                wires[index]={x,rectangle(x)};
                Cover base=remainder|wires[index].cover;
                ++candidates;
                for(int keep=0;keep<4;++keep){
                    int cost=(keep&1)+((keep>>1)&1);
                    if(cost>spare)continue;
                    Cover remaining=base;
                    if(keep&1)remaining=remaining|wires[a].cover;
                    if(keep&2)remaining=remaining|wires[b].cover;
                    if(!remaining.includes(all))continue;
                    std::vector<int> next;
                    next.reserve(live.size()+1);
                    for(int j:live)if((j!=a || (keep&1)) && (j!=b || (keep&2)))next.push_back(j);
                    next.push_back(index);
                    gates[depth]={a,b,op==1};
                    if(search(next,depth+1,spare-cost,b,a))return true;
                    if(stopped)return false;
                }
            }
        }
    }
    return false;
}
int main(int argc,char**argv) {
    if(argc!=5 && argc!=6)return 2;
    bool theta=argc==6 && std::string(argv[5])=="theta";
    if(argc==6 && !theta)return 2;
    int helpers=std::atoi(argv[1]);limit=std::atoi(argv[2]);budget=std::strtoull(argv[3],nullptr,10);
    if(helpers<0||helpers>3||limit<0||limit>20)return 2;
    deadline=Clock::now()+std::chrono::seconds(std::atoi(argv[4]));
    if(theta){
        if(helpers)return 2;
        for(int i=0;i<4;++i){flags.push_back({0,2+i});flags.push_back({2+i,6+i});flags.push_back({6+i,1});}
    }else{
        for(int i=0;i<6;++i)for(int j=0;j<4;++j)if(ends[i]&(1<<j))flags.push_back({j,4+i});
    }
    for(auto e:flags)rows.push_back((1<<e[0])|(1<<e[1]));
    for(int x=0;x<1024;++x)if(!target(x)){
        bool maximal=true;
        for(int j=0;j<10;++j)if(!(x&(1<<j)) && !target(x|(1<<j)))maximal=false;
        if(maximal)rows.push_back(x);
    }
    nNeg=rows.size()-flags.size();
    assert(rows.size()<32 && flags.size()*nNeg<=256);
    rowMask=(1u<<rows.size())-1;
    positives=(1u<<flags.size())-1;
    negativeMask=(1u<<nNeg)-1;
    std::vector<int> masks;
    for(int i=0;i<10;++i)masks.push_back(1<<i);
    for(int i=0;i<helpers;++i)masks.push_back((1<<(4+i))|(1<<(9-i)));
    width=masks.size();
    std::vector<int> live;
    for(int i=0;i<width;++i){
        live.push_back(i);
        Bits v=0;
        for(int j=0;j<(int)rows.size();++j)if(masks[i]&rows[j])v|=1u<<j;
        wires[i]={v,rectangle(v)};
    }
    std::array<int,4> p={0,1,2,3};
    for(int a=0;a<width;++a)for(int b=a+1;b<width;++b)first[a][b]=true;
    do {
        std::vector<int> im(p.begin(),p.end());
        for(int e:ends){
            int z=0;for(int i=0;i<4;++i)if(e&(1<<i))z|=1<<p[i];
            im.push_back(4+(std::find(ends.begin(),ends.end(),z)-ends.begin()));
        }
        if(theta){
            im={0,1};
            for(int i:p)im.push_back(2+i);
            for(int i:p)im.push_back(6+i);
        }
        bool legal=true;
        for(int i=10;i<width;++i){
            int z=0;for(int j=0;j<10;++j)if(masks[i]&(1<<j))z|=1<<im[j];
            auto it=std::find(masks.begin(),masks.end(),z);
            if(it==masks.end()){legal=false;break;}
            im.push_back(it-masks.begin());
        }
        if(legal)for(int a=0;a<width;++a)for(int b=a+1;b<width;++b)
            if(std::make_pair(std::max(im[a],im[b]),std::min(im[a],im[b]))<std::make_pair(b,a))first[a][b]=false;
    }while(std::next_permutation(p.begin(),p.end()));
    all=rectangle(positives);
    bool found=limit>=width-1 && search(live,0,limit-width+1,-1,-1);
    std::cout<<(found?"SAT":stopped?"INCOMPLETE":"EXCLUDED")<<" helpers="<<helpers
             <<" gates="<<limit<<" states="<<states<<" candidates="<<candidates<<"\n";
    if(found)for(int x=0;x<1024;++x){
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
