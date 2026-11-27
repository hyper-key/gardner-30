// Independent literal enumeration, starting with unused indices on the actual board.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>
using namespace std;
struct Axis {
    int e, offset;
    unsigned mask;
    array<bool,30> inside{}, possible{};
    vector<int> residues;
};
vector<Axis> pool[30];
void placements(vector<int>& q,int next,int remaining,int total){
    if(!remaining){
        if(total) return;
        Axis x{};
        x.offset=q.front(); x.e=q.back()-q.front();
        for(int t:q) if(t!=q.back()) {
            int z=t-x.offset;x.residues.push_back(z); x.inside[z]=true; x.mask|=1U<<z;
        }
        int count=0;
        for(int b=0;b<x.e;b++){
            bool yes=true;
            for(int a:x.residues){
                if(!x.inside[(a+b)%x.e] && !x.inside[(a-b+x.e)%x.e]){
                    yes=false;break;
                }
            }
            x.possible[b]=yes;
            count+=yes;
        }
        if(count>=14) pool[x.e].push_back(x);
        return;
    }
    int minSum=remaining*(2*next+remaining-1)/2;
    // largest available array is 29 down to 30-remaining, sum k*(59-k)/2
    int maxSum=remaining*(59-remaining)/2;
    if(total<minSum||total>maxSum) return;
    for(int j=next;j<=30-remaining;j++){
        q.push_back(j);placements(q,j+1,remaining-1,total-j);q.pop_back();
    }
}
int main(){
    vector<int> q;
    placements(q,0,15,225);
    for(int e=14;e<30;e++){
        auto &v=pool[e];
        sort(v.begin(),v.end(),[](auto &a,auto &b){return a.mask<b.mask;});
        for(auto &a:v) for(auto &b:v) if(a.mask<=b.mask) {
            bool ok=true;
            for(int i:a.residues) for(int j:b.residues){
                if((!a.inside[(i+j)%e]||!b.inside[(i+j)%e]) &&
                   (!a.inside[(i-j+e)%e]||!b.inside[(j-i+e)%e])) ok=false;
            }
            if(ok) cout<<e<<" "<<a.mask<<" "<<b.mask<<" "<<a.offset<<" "<<b.offset<<"\n";
        }
    }
}
