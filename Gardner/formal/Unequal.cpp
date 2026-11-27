// Independent endpoint enumeration. All bit positions are ordinary board indices.
#include <bit>
#include <array>
#include <cstdint>
#include <iostream>
#include <cstdlib>
#include <vector>
using Mask = std::uint32_t;
constexpr Mask board = (Mask{1} << 30)-1;
struct Count {
    std::uint64_t balancedRows=0, allowedRows=0, tested=0, matches=0;
};
static std::array<int,32768> sums{}, squares{};

int total(Mask m) {
    auto hi=m>>15;
    return sums[m & 32767] + sums[hi] + 15*std::popcount(hi);
}
int sumSquares(Mask m) {
    auto hi=m>>15;
    return squares[m & 32767] + squares[hi] + 30*sums[hi] + 225*std::popcount(hi);
}
// Compute H using the 15 active keys rather than the unused coordinates.
int invariant(Mask unused) {
    Mask active = board ^ unused;
    int a = 2*total(active)-15*29;
    int a2 = 4*sumSquares(active)-116*total(active)+15*29*29;
    return 21*a*a-5*a2;
}

// A target on column lo+t must reach an unused row at column lo or lo+span.
// Every legal line through that target has at least one point on those columns.
bool endpoint_column(Mask rows, int t, int span) {
    Mask reach = (rows << t) | (rows >> t) |
                 (rows << (span-t)) | (rows >> (span-t));
    return (rows & ~reach) == 0;
}
void columns(int e, Mask rows, const std::vector<int>& inner, int idx, int left,
             Mask used, int rowH, Count& count) {
    if (left==0) {
        for(int origin=0;origin+e<30;++origin) {
            Mask cols = used<<origin;
            ++count.tested;
            if(invariant(cols)==rowH) {
                ++count.matches;
                std::cout << "MATCH unused masks " << rows << " " << cols << '\n';
            }
        }
        return;
    }
    for (int i=idx; i+left <= (int)inner.size(); ++i)
        columns(e,rows,inner,i+1,left-1,used|(Mask{1}<<inner[i]),rowH,count);
}
int main(){
    for(Mask m=1;m<32768;++m) {
        unsigned j=std::countr_zero(m);
        Mask rest=m&(m-1);
        sums[m]=sums[rest]+j;
        squares[m]=squares[rest]+j*j;
    }
    // Positive controls for endpoints and centered arithmetic use literal loops.
    for (Mask rows : {Mask{32767},Mask{0x1234567},Mask{0x22767ff}}) {
        for (int e=14;e<=29;e++) for(int t=0;t<=e;t++) {
            bool direct=true;
            for(int r=0;r<30;r++) if((rows>>r)&1) {
                bool hit=false;
                for(int z=0;z<30;z++) if((rows>>z)&1)
                    if(std::abs(r-z)==t || std::abs(r-z)==e-t) hit=true;
                direct &= hit;
            }
            if(direct!=endpoint_column(rows,t,e)) return 2;
        }
    }
    for (Mask rows : {Mask{32767}, Mask{32767}<<15, Mask{0x15555555}}) {
        int a=0, a2=0;
        for(int r=0;r<30;r++) if(!(rows & (Mask{1}<<r))) {
            int centered=2*r-29;
            a+=centered;
            a2+=centered*centered;
        }
        if(invariant(rows)!=21*a*a-5*a2) return 4;
    }
    std::array<Count,30> counts{};
    std::uint64_t rowsets=0;
    for(Mask rows=32767;rows<=board;) {
        ++rowsets;
        int rowSpan=31-std::countl_zero(rows)-std::countr_zero(rows);
        int rhs=870-4*total(rows);
        for(int e : {18,22,26}) {
            if(rowSpan>=e || rhs%e || std::abs(rhs/e)>15 || rhs/e%2==0) continue;
            Count& c=counts[e];
            ++c.balancedRows;
            std::vector<int> inner;
            for(int t=1;t<e;t++) if(endpoint_column(rows,t,e)) inner.push_back(t);
            if(inner.size()<13) continue;
            ++c.allowedRows;
            columns(e,rows,inner,0,13,1|(Mask{1}<<e),invariant(rows),c);
        }
        Mask lsb=rows & (Mask{0}-rows);
        Mask r=rows+lsb;
        rows=r|(((r^rows)>>2)/lsb);
    }
    std::cout << "short row sets " << rowsets << '\n';
    std::uint64_t found=0;
    for(int e : {18,22,26}) {
        const auto& c=counts[e]; found+=c.matches;
        std::cout << e << " balanced rows " << c.balancedRows << " endpoint rows "
                  << c.allowedRows << " H comparisons " << c.tested << " matches " << c.matches << '\n';
    }
    return found ? 1 : (rowsets==155117520 ? 0 : 3);
}
