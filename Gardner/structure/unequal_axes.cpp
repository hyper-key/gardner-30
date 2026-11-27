// Fully paired case: unused rows have strictly smaller span than unused columns.
// Each of the 30 diagonal lines must hit one of the 30 extreme-column holes.
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <vector>

using Mask = std::uint32_t;
constexpr Mask board = (1U<<30)-1;
Mask bit(int i) { return Mask{1}<<i; }
Mask reverse_axis(Mask w) {
    Mask r=0;
    for(;w;w &= w-1) r |= bit(29-std::countr_zero(w));
    return r;
}
Mask rotate_mod(Mask x,int k,int e) {
    return ((x<<k)|(x>>(e-k)))&(bit(e)-1);
}
struct Moments { int sum{}, squares{}; };
std::array<Moments,1<<15> lo{},hi{};
void init() {
    for (unsigned i=1;i<lo.size();++i) {
        int x=2*std::countr_zero(i)-29, y=x+30;
        auto j=i&(i-1);
        lo[i]={lo[j].sum+x,lo[j].squares+x*x};
        hi[i]={hi[j].sum+y,hi[j].squares+y*y};
    }
}
Moments active(Mask unused) {
    Mask used=board^unused;
    auto a=lo[used&((1U<<15)-1)],b=hi[used>>15];
    return {a.sum+b.sum,a.squares+b.squares};
}
int invariant(Moments v) {return 21*v.sum*v.sum-5*v.squares;}
Mask next_combination(Mask x) {
    Mask low=x&-x, up=x+low;
    return up|(((up^x)>>2)/low);
}
int main() {
    init();
    for(int e : {18,22,26}) {
        long long shortShapes=0, stepPass=0, rowOffsets=0, columnShapes=0, accepted=0;
        for(Mask tail=bit(14)-1;tail<bit(e-1);tail=next_combination(tail)) {
            ++shortShapes;
            Mask u=(tail<<1)|1;
            int span=std::bit_width(u)-1;
            // A long-axis residue c can only be used if every target row r
            // has r+c or r-c in U mod e. This condition ignores queen support.
            Mask good=1;
            for(int c=1;c<=e/2;c++) {
                if(!(u & ~(rotate_mod(u,c,e)|rotate_mod(u,e-c,e))))
                    good |= bit(c)|bit(e-c);
            }
            if(std::popcount(good)<14)continue;
            ++stepPass;
            std::vector<std::pair<Mask,int>> rows;
            for(int shift=0;shift+span<30;shift++) {
                Mask r=u<<shift;
                if(r>reverse_axis(r))continue;
                auto a=active(r);
                // A is 435-2*sum(unused row indices). 2A=(15-2x)e.
                if((2*a.sum)%e)continue;
                int v=(2*a.sum)/e;
                if(v%2==0 || v < -15 || v>15)continue;
                rows.emplace_back(r,invariant(a));
            }
            if(rows.empty())continue;
            rowOffsets+=rows.size();
            // Select thirteen nonzero offsets from the available bits, then
            // restore the two extreme columns at offsets 0,e.
            std::vector<int> offsets;
            for(Mask b=good^1;b;b &= b-1) offsets.push_back(std::countr_zero(b));
            for(Mask sel=bit(13)-1;sel<bit(offsets.size());sel=next_combination(sel)) {
                ++columnShapes;
                Mask v=1|bit(e);
                for(Mask b=sel;b;b &= b-1) v |= bit(offsets[std::countr_zero(b)]);
                for(int shift=0;shift+e<30;shift++) {
                    Mask c=v<<shift;
                    if(c>reverse_axis(c))continue;
                    int hc=invariant(active(c));
                    for(auto [r,hr]:rows) if(hr==hc) {
                        std::cout<<e<<' '<<r<<' '<<c<<'\n';
                        ++accepted;
                    }
                }
            }
        }
        std::cerr<<"span "<<e<<" short_shapes "<<shortShapes<<" good_steps "<<stepPass
                 <<" eligible_row_offsets "<<rowOffsets<<" tested_column_shapes "
                 <<columnShapes<<" resulting_pairs "<<accepted<<'\n';
    }
}
