// Search for a maximal placement with an eightfold-invariant core and two exceptions.
// Each direction is represented by an index 0..4*n-1 or 0..6*n-1 as appropriate.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <map>
#include <vector>
using namespace std;

constexpr int MAX_BOARD = 30;
using Square = pair<int,int>;
struct Orbit {
    vector<Square> cells;
    vector<pair<int,int>> counts;
};
struct Search {
    int n;
    int target;
    array<int,6*MAX_BOARD> occupied{};
    vector<Orbit> ordinary, diagonal;
    vector<Square> core;
    long long cores=0, pruned=0, pairs=0, sat=0;
    int best=10000;
    vector<Square> best_board;
    array<int,4> lines(int r,int c) const {
        return {r, n+c, 2*n+r+c, 5*n-1+r-c};
    }
    Orbit make_orbit(int i,int j) {
        vector<Square> cells;
        for(auto [a,b]: {Square{i,j},Square{j,i}}) {
            for(int r: {a,n-1-a}) for(int c: {b,n-1-b}) cells.emplace_back(r,c);
        }
        sort(cells.begin(),cells.end());
        cells.erase(unique(cells.begin(),cells.end()),cells.end());
        map<int,int> counts;
        for(auto [r,c]:cells) for(int k: lines(r,c)) counts[k]++;
        return {cells,vector<pair<int,int>>(counts.begin(),counts.end())};
    }
    void update(const Orbit &o,int sign) {
        for(auto [k,c]:o.counts) occupied[k]+=sign*c;
        if(sign==1) core.insert(core.end(),o.cells.begin(),o.cells.end());
        else core.resize(core.size()-o.cells.size());
    }
    bool fits(const Orbit &o) const {
        for(auto [k,c]:o.counts) if(occupied[k]+c>2) return false;
        return true;
    }
    void test() {
        ++cores;
        vector<Square> holes;
        vector<array<int,4>> ids;
        array<int,6*MAX_BOARD> sizes{};
        // All squares of a core under these axial reflections occupy a full
        // row, hence a square on no saturated line is an addable empty square.
        for(int r=0;r<n;r++) if(occupied[r]!=2){
            for(int c=0;c<n;c++) if(occupied[n+c]!=2) {
                auto keys=lines(r,c);
                if(occupied[keys[2]]==2||occupied[keys[3]]==2) continue;
                holes.emplace_back(r,c);
                ids.push_back(keys);
                for(auto k:keys) sizes[k]++;
            }
        }
        int singleton_sum=0, maxline=0;
        for(int k=0;k<6*n;k++){
            if(occupied[k]==1) singleton_sum+=sizes[k];
            if(occupied[k]==0) maxline=max(maxline,sizes[k]);
        }
        // Every newly blocked square is an added queen, or lies on an old
        // singleton line, or lies on the unique permitted line joining the pair.
        if((int)holes.size()-2-singleton_sum-maxline>=best) {++pruned;return;}
        vector<vector<int>> covered;
        for(size_t a=0;a<holes.size();a++){
            vector<int> line_ids;
            for(int k:ids[a]) if(occupied[k]==1) line_ids.push_back(k);
            covered.push_back(line_ids);
        }
        for(size_t a=0;a<holes.size();a++) for(size_t b=a+1;b<holes.size();b++){
            int shared=-1;
            for(int z=0;z<4;z++) if(ids[a][z]==ids[b][z]) shared=ids[a][z];
            if(shared!=-1 && occupied[shared]==1) continue; // triple
            ++pairs;
            int bound=(int)holes.size()-2;
            for(int k:covered[a]) bound-=sizes[k];
            for(int k:covered[b]) bound-=sizes[k];
            if(shared!=-1) bound-=sizes[shared];
            if(bound>=best) continue;
            array<bool,6*MAX_BOARD> blocked{};
            for(int k:covered[a]) blocked[k]=true;
            for(int k:covered[b]) blocked[k]=true;
            if(shared!=-1) blocked[shared]=true;
            int remain=0;
            for(size_t c=0;c<holes.size();c++) if(c!=a && c!=b){
                bool gone=false;
                for(int k:ids[c]) if(blocked[k]) gone=true;
                remain+=!gone;
            }
            if(remain<best){
                best=remain; best_board=core;
                best_board.push_back(holes[a]); best_board.push_back(holes[b]);
                if(!best) ++sat;
            }
        }
    }
    void recurse(size_t start,int left) {
        if(!left){ test(); return; }
        for(size_t t=start;t<ordinary.size();t++) if(fits(ordinary[t])){
            update(ordinary[t],1);recurse(t+1,left-1);update(ordinary[t],-1);
        }
    }
    void run(){
        for(int i=0;i<n/2;i++) for(int j=0;j<=i;j++){
            auto o=make_orbit(i,j);
            if(i==j) diagonal.push_back(o); else ordinary.push_back(o);
        }
        const int k=target-2;
        if(k%8==0) recurse(0,k/8);
        if(k%8==4) for(auto &d:diagonal){
            update(d,1); recurse(0,(k-4)/8); update(d,-1);
        }
        cout<<"n "<<n<<" target "<<target<<" cores "<<cores<<" pruned_by_bound "<<pruned
            <<" evaluated_legal_pairs "<<pairs<<" best_holes "<<best<<" found "<<sat<<"\n";
        sort(best_board.begin(),best_board.end());
        cout<<"{\"n\": "<<n<<", \"queens\": [";
        bool comma=false;
        for(auto [r,c]:best_board){
            if(comma) cout<<", ";
            cout<<"["<<r<<", "<<c<<"]"; comma=true;
        }
        cout<<"]}\n";
    }
};
int main(int argc,char**argv){
    if(argc!=3) return 2;
    Search s;
    s.n=atoi(argv[1]);s.target=atoi(argv[2]);
    if(s.n<2||s.n>MAX_BOARD||s.n%2||s.target<2||((s.target-2)%4)!=0) return 2;
    s.run();
}
