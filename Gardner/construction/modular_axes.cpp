// Exhaustive projected row/column pairs for the perimeter-equality (15,13) case.
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>
using namespace std;
using Bits=uint32_t;
struct Axis { Bits set, steps, neg; int offset; };
int e; Bits full;
Bits bit(int k){return Bits{1}<<k;}
Bits rot(Bits w,int k){return ((w<<k)|(w>>(e-k)))&full;}
Bits negative(Bits w){
    Bits ret=w&1U;
    for(Bits u=w&~1U;u;u&=u-1) ret|=bit(e-countr_zero(u));
    return ret;
}
int indexsum(Bits w){
    // Compute the index sum by the five binary digits of all indices.
    return popcount(w&0xAAAAAAAAU)+2*popcount(w&0xCCCCCCCCU)+4*popcount(w&0xF0F0F0F0U)
        +8*popcount(w&0xFF00FF00U)+16*popcount(w&0xFFFF0000U);
}
vector<Axis> generate(){
    vector<Axis> v;
    // 0 is fixed. Iterate the other thirteen set positions by Gosper's successor.
    for(Bits x=bit(13)-1;x<bit(e-1);){
        Bits a=(x<<1)|1, low=x&-x, bump=x+low;
        x=(((bump^x)>>2)/low)|bump;
        int rem=225-e-indexsum(a);
        if(rem<0 || rem%15 || rem/15+e>=30) continue;
        Bits steps=1;
        for(int b=1;b<=e/2;b++){
            if(!(a&~(rot(a,b)|rot(a,e-b)))) steps|=bit(b)|bit(e-b);
        }
        if(popcount(steps)>=14) v.push_back({a,steps,negative(a),rem/15});
    }
    return v;
}
bool compatible(Axis a,Axis b){
    if((b.set&~a.steps)||(a.set&~b.steps)) return false;
    Bits both=a.set&b.set,opp=a.set&b.neg;
    for(Bits u=b.set;u;u&=u-1){
        int y=countr_zero(u);
        if(a.set&~(rot(both,e-y)|rot(opp,y))) return false;
    }
    return true;
}
int main(){
    for(e=14;e<=29;e++){
        full=bit(e)-1;
        auto v=generate();
        size_t accepted=0;
        for(size_t i=0;i<v.size();i++) for(size_t j=i;j<v.size();j++){
            if(compatible(v[i],v[j])){
                cout<<e<<" "<<v[i].set<<" "<<v[j].set<<" "<<v[i].offset<<" "<<v[j].offset<<"\n";
                accepted++;
            }
        }
        cerr<<e<<" eligible-axes "<<v.size()<<" compatible-pairs "<<accepted<<"\n";
    }
}
