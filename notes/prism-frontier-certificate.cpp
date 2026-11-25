// Generate the finite list of live wire pools for the signed triangular prism.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <map>
#include <set>
#include <string>
#include <vector>

using Word = std::uint64_t;
using Pool = std::vector<Word>;
using Rows = std::array<unsigned,64>;

struct Layer {
    std::map<Pool,unsigned> index;
    std::vector<Pool> pools;
    std::map<Pool,std::pair<unsigned,unsigned>> images;
};

class Prism {
    Word goal = 0;
    Pool raw = Pool(6);
    std::vector<unsigned> negatives;
    std::vector<Rows> actions;
    std::array<Layer,10> layers;
    std::uint64_t tested = 0;

    static Word act(Word x, const Rows& rows) {
        Word value=0;
        while (x) {
            unsigned r=__builtin_ctzll(x);
            value |= Word(1) << rows[r];
            x &= x-1;
        }
        return value;
    }

    bool separates(const Pool& wires) const {
        for (unsigned row: negatives) {
            Word indistinguishable = goal;
            for (Word w: wires) {
                indistinguishable &= ((w>>row)&1) ? w : ~w;
                if (!indistinguishable) break;
            }
            if (indistinguishable) return false;
        }
        return true;
    }

    void record(unsigned remaining, Pool wires) {
        ++tested;
        if (std::find(wires.begin(),wires.end(),goal)!=wires.end())
            throw std::runtime_error("a gate sequence reached the prism");
        if (!remaining || wires.size()>remaining+1 || !separates(wires)) return;
        std::sort(wires.begin(),wires.end());
        Layer& layer=layers[remaining];
        if (layer.images.count(wires)) return;
        Pool canonical=wires;
        unsigned which=0;
        for (unsigned i=1;i<actions.size();++i) {
            Pool candidate;
            for (Word w:wires) candidate.push_back(act(w,actions[i]));
            std::sort(candidate.begin(),candidate.end());
            if (candidate<canonical) {canonical=candidate; which=i;}
        }
        auto [item,fresh]=layer.index.emplace(canonical,layer.pools.size());
        if (fresh) layer.pools.push_back(canonical);
        layer.images.emplace(wires,std::make_pair(item->second,which));
    }

    void expand(unsigned k, const Pool& wires) {
        for (unsigned i=0;i<wires.size();++i) for (unsigned j=i+1;j<wires.size();++j) {
            Word a=wires[i],b=wires[j];
            Pool rest;
            for (unsigned t=0;t<wires.size();++t)
                if (t!=i && t!=j) rest.push_back(wires[t]);
            for (Word w:std::array<Word,4>{a&b,a&~b,~a&b,a|b}) {
                if (!w || std::binary_search(wires.begin(),wires.end(),w)) continue;
                rest.push_back(w);
                for (unsigned keep=0;keep<4;++keep) {
                    Pool next=rest;
                    if (keep&1) next.push_back(a);
                    if (keep&2) next.push_back(b);
                    record(k-1,next);
                }
                rest.pop_back();
            }
        }
    }

public:
    Prism() {
        const std::vector<std::pair<unsigned,unsigned>> edges={
            {0,2},{0,4},{2,4},{1,3},{1,5},{3,5},{0,3},{2,5},{1,4}
        };
        for (unsigned r=0;r<64;++r) {
            bool hit=false;
            for (auto [a,b]:edges) hit|=((r>>a)&(r>>b)&1)!=0;
            if (hit) goal|=Word(1)<<r; else negatives.push_back(r);
            for (unsigned i=0;i<6;++i) if ((r>>i)&1) raw[i]|=Word(1)<<r;
        }
        std::array<unsigned,6> p={0,1,2,3,4,5};
        do {
            Rows rows{};
            for (unsigned r=0;r<64;++r) for(unsigned i=0;i<6;++i)
                rows[r]|=((r>>i)&1)<<p[i];
            if (act(goal,rows)==goal) actions.push_back(rows);
        } while (std::next_permutation(p.begin(),p.end()));
    }

    void run(bool dump) {
        record(9,raw);
        for (int k=9;k>0;--k)
            for (const Pool& s:layers[k].pools) expand(k,s);
        if(actions.size()!=12 || layers[9].pools.size()!=1) throw std::runtime_error("wrong group or root");
        std::set<Word> dict;
        for (unsigned k=0;k<=9;k++) {
            const auto& layer=layers[k];
            if (!dump) std::cout<<"Budget "<<k<<" pools "<<layer.pools.size()<<" images "<<layer.images.size()<<"\n";
            for (unsigned i=0;i<layer.pools.size();i++) {
                const auto& s=layer.pools[i];dict.insert(s.begin(),s.end());
                if (dump) {std::cout<<"S "<<k<<" "<<i;for(Word w:s)std::cout<<" "<<w;std::cout<<"\n";}
            }
            if (dump) for (const auto& [s,where]:layer.images) {
                std::cout<<"L "<<k<<" "<<where.first<<" "<<where.second;
                for(Word w:s)std::cout<<" "<<w;
                std::cout<<"\n";
            }
        }
        if (dump) for (unsigned i=0;i<actions.size();i++) {
            std::cout<<"P "<<i;for (unsigned j=0;j<6;j++)std::cout<<" "<<__builtin_ctz(actions[i][1u<<j]);
            std::cout<<"\n";
        }
        if (!dump) std::cout<<tested<<" candidate pools, "<<dict.size()<<" distinct words in representatives\n";
    }
};

int main(int argc,char** argv) {
    Prism p;
    p.run(argc==2 && std::string(argv[1])=="--dump");
}
