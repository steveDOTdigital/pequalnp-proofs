// Exhaustive circuit search for the complement of the seven-cycle.
// Compile with c++ -O3 -std=c++17. No external solver is required.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <map>
#include <set>
#include <stdexcept>
#include <string>
#include <vector>

using Word = __uint128_t;
using Pool = std::vector<Word>;
using Pattern = std::array<int,7>;
using Perm = std::array<unsigned char,128>;
Word allRows(unsigned rows) { return rows==128 ? ~Word(0) : (Word(1)<<rows)-1; }
bool bit(Word w,unsigned r) { return (w>>r)&1; }
Word orient(Word w,Word mask) { return bit(w,0) ? w^mask : w; }
Word coordinate(unsigned j,unsigned rows) {
    Word w=0; for(unsigned r=0;r<rows;r++) if((r>>j)&1)w|=Word(1)<<r;
    return w;
}
Word cycleTarget() {
    Word w=0;
    for(unsigned r=0;r<128;r++)for(unsigned a=0;a<7;a++)for(unsigned b=a+1;b<7;b++)
        if(b-a!=1 && b-a!=6 && ((r>>a)&(r>>b)&1))w|=Word(1)<<r;
    return w;
}
struct Minor {
    unsigned dimension,bound;
    Word mask;
    std::vector<unsigned> rowMap;
    std::map<Word,unsigned> price;
    Minor(Pattern assignment,unsigned lb):dimension(0),bound(lb) {
        for(int z:assignment)if(z!=99)dimension=std::max(dimension,unsigned(std::abs(z)));
        unsigned rows=1u<<dimension; mask=allRows(rows);
        for(unsigned r=0;r<rows;r++){
            unsigned v=0;
            for(unsigned j=0;j<7;j++){
                int z=assignment[j];bool b=z==99 || (z && (bool(r>>(std::abs(z)-1)&1) != (z<0)));
                if(b)v|=1u<<j;
            }
            rowMap.push_back(v);
        }
        Pool signedInputs={0,mask};price[0]=0;
        for(unsigned j=0;j<dimension;j++){
            Word w=coordinate(j,rows);price[w]=1;signedInputs.push_back(w);signedInputs.push_back(w^mask);
        }
        unsigned next=2;
        for(Word a:signedInputs)for(Word b:signedInputs){
            Word w=orient(a&b,mask);
            if(!price.count(w))price[w]=next++;
        }
    }
    Word project(Word w) const {
        Word result=0;
        for(unsigned r=0;r<rowMap.size();r++)if(bit(w,rowMap[r]))result|=Word(1)<<r;
        return orient(result,mask);
    }
};
struct Reached {};
class Search {
    unsigned n,rows;
    Word goal,mask;
    bool signedMode;
    std::vector<unsigned> negatives;
    std::vector<Perm> symmetries;
    std::map<Word,Pool> orbit;
    const std::vector<Minor>& minors;
    std::map<Word,std::vector<unsigned char>> prices;
    // Distinct actual wires form the frontier of the live output cone.
    using Layer=std::set<Pool>;
    std::vector<std::array<Layer,2>> layers;
    std::uint64_t tested=0,expanded=0;
    const Pool& images(Word w) {
        auto it=orbit.find(w);if(it!=orbit.end())return it->second;
        Pool values;
        for(const auto& p:symmetries){
            Word t=0;for(unsigned r=0;r<rows;r++)if(bit(w,r))t|=Word(1)<<p[r];
            values.push_back(t);
        }
        return orbit.emplace(w,std::move(values)).first->second;
    }
    Pool representative(Pool s) {
        std::sort(s.begin(),s.end());Pool best=s,trial(s.size());
        std::vector<const Pool*> vals;for(auto w:s)vals.push_back(&images(w));
        for(unsigned j=1;j<symmetries.size();j++){
            for(unsigned i=0;i<s.size();i++)trial[i]=(*vals[i])[j];
            std::sort(trial.begin(),trial.end());if(trial<best)best=trial;
        }
        return best;
    }
    bool distinguish(const Pool& s,bool after) const {
        for(unsigned r:negatives){
            Word bad=goal;
            for(auto w:s){
                if(!bit(w,r))bad&=~w;else if(!after)bad&=w;
                if(!bad)break;
            }
            if(bad)return false;
        }
        return true;
    }
    const std::vector<unsigned char>& costs(Word w){
        auto it=prices.find(w);if(it!=prices.end())return it->second;
        std::vector<unsigned char> c;
        for(const auto& m:minors){auto v=m.price.find(m.project(w));c.push_back(v==m.price.end()?255:v->second);}
        return prices.emplace(w,std::move(c)).first->second;
    }
    bool cut(unsigned remaining,const Pool& s){
        if(minors.empty())return false;
        std::vector<const std::vector<unsigned char>*> cs;
        for(auto w:s)cs.push_back(&costs(w));
        for(unsigned j=0;j<minors.size();j++){
            unsigned zeros=0,needed=0;std::array<bool,256> bought{};bool known=true;
            for(auto c:cs){auto v=(*c)[j];if(v==255){known=false;break;}
                if(v==0)++zeros;
                if(v>1&&!bought[v]){bought[v]=true;++needed;}
            }
            if(known&&remaining+needed<minors[j].bound+zeros)return true;
        }
        return false;
    }
    void record(unsigned remaining,bool after,Pool s){
        ++tested;
        if(std::find(s.begin(),s.end(),goal)!=s.end())throw Reached{};
        if(!signedMode&&!after&&std::find(s.begin(),s.end(),goal^mask)!=s.end())throw Reached{};
        if(!remaining||s.size()>remaining+1||!distinguish(s,after))return;
        // Prune before storing, using verified minor bounds. A rotation or
        // reflection preserves the target even if the minor list is empty.
        if(cut(remaining,s))return;
        layers[remaining][after].insert(representative(std::move(s)));
    }
    void expand(unsigned k,bool after,const Pool& s){
        ++expanded;
        for(unsigned i=0;i<s.size();i++)for(unsigned j=0;j<i;j++){
            Word a=s[i],b=s[j];std::array<Word,4> forms={a&b,a|b,a&~b,b&~a};
            for(unsigned op=0;op<(signedMode?4u:2u);op++){
                Word w=forms[op];if(!w||w==mask||std::binary_search(s.begin(),s.end(),w))continue;
                for(unsigned keep=0;keep<4;keep++){
                    Pool next={w};for(unsigned z=0;z<s.size();z++)
                        if((z!=i||(keep&1))&&(z!=j||(keep&2)))next.push_back(s[z]);
                    record(k-1,after,std::move(next));
                }
            }
        }
        if(!signedMode&&!after){
            for(unsigned i=0;i<s.size();i++){
                if(std::binary_search(s.begin(),s.end(),mask^s[i]))continue;
                Pool next=s;next[i]^=mask;record(k,true,next);next.push_back(s[i]);record(k,true,std::move(next));
            }
        }
    }
public:
    Search(unsigned dim,Word target,bool signs,const std::vector<Minor>& library):
        n(dim),rows(1u<<n),goal(target),mask(allRows(rows)),signedMode(signs),minors(library) {
        std::vector<unsigned> perm;for(unsigned i=0;i<n;i++)perm.push_back(i);
        for(unsigned i=0;i<rows;i++)if(!bit(goal,i))negatives.push_back(i);
        do {
            Perm p{};bool fixed=true;
            for(unsigned r=0;r<rows;r++){
                unsigned t=0;for(unsigned j=0;j<n;j++)if((r>>j)&1)t|=1u<<perm[j];
                p[r]=t;if(bit(goal,t)!=bit(goal,r)){fixed=false;break;}
            }
            if(fixed)symmetries.push_back(p);
        }while(std::next_permutation(perm.begin(),perm.end()));
    }
    bool reaches(unsigned cap){
        layers.resize(cap+1);Pool raw;for(unsigned i=0;i<n;i++)raw.push_back(coordinate(i,rows));
        try{
            record(cap,false,raw);
            for(unsigned k=cap;k>0;k--)for(unsigned p=0;p<(signedMode?1u:2u);p++)
                for(const auto& s:layers[k][p])expand(k,p,s);
        }catch(const Reached&){return true;}
        return false;
    }
    void report()const{std::cout<<expanded<<" expanded frontiers, "<<tested<<" candidates\n";}
};
Pattern normalized(Pattern p){
    std::array<int,8> ids{};int next=1;
    for(int& z:p)if(z&&z!=99){auto& i=ids[std::abs(z)];if(!i)i=z>0?next++:-(next++);z=z>0?i:-i;}
    return p;
}
int main(){
    const std::vector<Minor> none;
    Word goal=cycleTarget();
    const std::vector<std::pair<Pattern,unsigned>> representatives={
        {{0,0,1,0,2,3,4},5},
        {{0,1,0,2,0,3,4},5},
        {{0,0,1,2,3,4,5},6},
        {{0,1,0,2,3,4,5},7},
        {{0,1,2,0,3,4,5},6},
        {{0,1,2,3,4,5,6},9},
        {{1,1,2,3,4,5,6},10},
        {{1,2,1,3,4,5,6},8},
        {{1,2,3,1,4,5,6},7},
        {{1,2,-1,3,4,5,6},7},
        {{1,2,3,-1,4,5,6},10},
        {{1,-1,2,3,4,5,6},6},
        {{1,2,3,4,5,6,99},5},
    };
    std::vector<Minor> library;
    for(const auto& [p,k]:representatives){
        Minor m(p,k);Search proof(m.dimension,m.project(goal),true,none);
        if(proof.reaches(k-1)){std::cerr<<"Failed minor bound "<<k<<"\n";return 1;}
        std::set<Pattern> images;
        for(int offset=0;offset<7;offset++)for(int dir:{-1,1}){
            Pattern im{};for(int i=0;i<7;i++)im[i]=p[(offset+7+dir*i)%7];
            images.insert(normalized(im));
        }
        for(auto im:images)library.emplace_back(im,k);
    }
    std::cout<<"Verified "<<representatives.size()<<" signed minor bounds and "<<library.size()<<" symmetry images.\n"<<std::flush;
    Word control=0;for(unsigned r=0;r<128;r++)if((!(r&1)&&(r&2))||(r&124))control|=Word(1)<<r;
    Search check(7,control,false,none);
    if(!check.reaches(6)){std::cerr<<"Failed one-NOT positive control\n";return 2;}
    Search signedFloor(7,goal,true,library);
    if(signedFloor.reaches(11)){std::cerr<<"Found a short signed circuit\n";return 3;}
    std::cout<<"Excluded eleven signed binary gates: ";signedFloor.report();std::cout<<std::flush;
    Search oneNot(7,goal,false,library);
    if(oneNot.reaches(12)){std::cerr<<"Found a short circuit using at most one NOT\n";return 4;}
    std::cout<<"Excluded twelve binary gates with one free NOT: ";oneNot.report();
}
