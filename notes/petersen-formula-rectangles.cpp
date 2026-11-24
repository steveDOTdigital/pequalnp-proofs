// Exact minimum formula leaf count on two lists of Boolean assignments.
// A formula is a tree. The rectangle recurrence permits either input polarity.
#include <algorithm>
#include <bit>
#include <cstdint>
#include <iostream>
#include <utility>
#include <vector>

int main() {
  const int edges[][2] = {{0,1},{1,2},{2,3},{0,4},{3,4},{0,5},{1,6},{2,7},{5,7},{3,8},{5,8},{6,8}};
  std::vector<int> pos, neg;
  for (auto &e : edges) pos.push_back((1<<e[0])|(1<<e[1]));
  auto f = [&](int r) { for (int e : pos) if ((e&r)==e) return true; return false; };
  const uint64_t packed[] = {18440827511444797640ULL, 18441957826578283724ULL, 18446744073709222136ULL, 18446744073709485308ULL, 18446744073708175304ULL, 18446744073709551615ULL, 18446744073709223928ULL, 18446744073709551615ULL};
  for (int r=0; r<512; ++r)
    if (f(r) != bool((packed[r/64] >> (r%64)) & 1)) return 3;
  std::vector<int> covers;
  for (int mask=0;mask<512;++mask) {
    bool coversAll = std::all_of(pos.begin(),pos.end(),[&](int edge){ return mask&edge; });
    if (coversAll && std::popcount((unsigned)mask)<5) return 4;
    if (coversAll && std::popcount((unsigned)mask)==5) covers.push_back(mask);
  }
  if (covers.size()!=3) return 5;
  for (int r=0;r<512;++r) if (!f(r)) {
    bool maximal=true;
    for (int i=0;i<9;++i) if (!(r&(1<<i)) && !f(r|(1<<i))) maximal=false;
    if (maximal) neg.push_back(r);
  }
  int h=1<<pos.size(), w=1<<neg.size();
  if (h!=4096 || w!=4096) return 2;
  // Test every choice of at most two raw variables allowed negative literals.
  std::vector<std::pair<int,int>> models = {{511,0},{511,511},{1023,0},{1023,512}};
  for (int i=0; i<9; ++i)
    for (int j=i; j<9; ++j) models.emplace_back(511,(1<<i)|(1<<j));
  for (const auto &[signals,signedMask] : models) {
    auto lift = [&](int x) { return x | ((signals==1023 && (x&5)) ? 512 : 0); };
    std::vector<uint8_t> cost(h*w,64);
    std::vector<int> pa(h,signals), na(w,signals), pz(h,signals), nz(w,signals);
    for (int s=1;s<h;++s) {
      int x=lift(pos[std::countr_zero((unsigned)s)]);
      pa[s]=pa[s&(s-1)]&x; pz[s]=pz[s&(s-1)]&~x;
    }
    for (int s=1;s<w;++s) {
      int x=lift(neg[std::countr_zero((unsigned)s)]);
      na[s]=na[s&(s-1)]&x; nz[s]=nz[s&(s-1)]&~x;
    }
    for (int p=1;p<h;++p) {
      auto row=cost.data()+p*w;
      for(int n=1;n<w;++n) if ((pa[p]&nz[n]) || (signedMask & pz[p] & na[n])) row[n]=1;
      // At an OR, partition the positive rows between its children.
      for (int sub=(p-1)&p;sub>(p^sub);sub=(sub-1)&p) {
        const auto a=cost.data()+w*sub,b=cost.data()+w*(p^sub);
        for (int n=1;n<w;++n) row[n]=std::min(row[n],(uint8_t)(a[n]+b[n]));
      }
      // At an AND, partition the negative rows. Proper submasks are ready.
      for(int n=1;n<w;++n) {
        if(row[n]<=2) continue;
        for(int sub=(n-1)&n;sub>(n^sub);sub=(sub-1)&n)
          row[n]=std::min(row[n],(uint8_t)(row[sub]+row[n^sub]));
      }
    }
    bool allowed = std::popcount((unsigned)signedMask) <= 1 ||
      std::any_of(covers.begin(),covers.end(),[&](int c){return (signedMask & ~c)==0;});
    if (signals==511 && allowed && cost.back()!=17) return 6;
    if (signals==1023 && cost.back()!=16) return 7;
    std::cout<<"signals "<<signals<<" signedMask "<<signedMask<<" boundary minimum = "<<int(cost.back())<<" leaves\n"<<std::flush;
  }
}
