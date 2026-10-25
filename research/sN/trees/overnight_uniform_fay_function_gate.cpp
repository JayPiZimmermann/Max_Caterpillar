// Exact chamber aggregation of a proposed full symmetric whole-function identity.
#include <array>
#include <algorithm>
#include <numeric>
#include <map>
#include <iostream>
#include <vector>
using V=std::array<int,9>;
struct Unit{int w,r;std::array<std::pair<int,int>,7> E;};
int main(){int m;std::cin>>m;std::vector<Unit> U(m);for(auto&u:U){std::cin>>u.w>>u.r;for(auto&e:u.E)std::cin>>e.first>>e.second;}
 V p;std::iota(p.begin(),p.end(),0);std::map<V,long long> counts;std::array<long long,9> linear{};long long perms=0;
 do{++perms;for(auto&u:U){V a{};++a[p[u.r]];--a[p[0]];for(auto[e,f]:u.E)if(p[e]>p[f]){++a[p[e]];--a[p[f]];}
  bool pos=false,neg=false;int s=0;for(int k=8;k>0;--k){s+=a[k];pos|=s>0;neg|=s<0;}
  if(!neg){for(int k=0;k<9;++k)linear[k]+=u.w*a[k];continue;}if(!pos)continue;
  int g=0;for(int x:a)g=std::gcd(g,x);int first=0;while(a[first]==0)++first;int sign=a[first]>0?1:-1;V key=a;for(auto&x:key)x/=g*sign;
  counts[key]+=(long long)u.w*g;if(sign<0)for(int k=0;k<9;++k)linear[k]+=u.w*a[k];
 }}while(std::next_permutation(p.begin(),p.end()));
 long long nonzero=0;for(auto[k,v]:counts)if(v){++nonzero;if(nonzero<=10){std::cout<<"wall "<<v;for(int x:k)std::cout<<' '<<x;std::cout<<'\n';}}
 std::cout<<"permutations "<<perms<<" distinct_mixed_walls "<<counts.size()<<" nonzero_mixed_walls "<<nonzero<<" linear";for(auto x:linear)std::cout<<' '<<x;std::cout<<'\n';
}
