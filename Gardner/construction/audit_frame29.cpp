// Independent projected search. Generate cyclic necklaces, expand rotations, and
// reject only by the two exceptional residue-line budget and equal axis sums.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>
using namespace std;
using M=uint32_t;
struct Axis {M mask, allowed; int sum;};
struct Engine {
    int n, p, e;
    bool shapes_only=false;
    uint64_t counted=0;
    M last_rep=0;
    array<int,32> symbols{};
    vector<Axis> axes;
    int add[32][32]{}, sub[32][32]{};
    static M bit(int i){return 1U<<i;}
    void test_necklace(){
        M a=0, allowed=0; int clean=0;
        for(int k=0;k<e;k++) if(symbols[k+1]) a|=bit(k);
        M canonical=0;
        for(int k=1;k<=e;k++) canonical=(canonical<<1)|symbols[k];
        if(canonical<=last_rep) abort();
        last_rep=canonical;
        M fullmask=bit(e)-1, rotated=canonical;
        do{
            if(rotated<canonical) abort();
            counted+=(rotated&1U);
            rotated=((rotated<<1)&fullmask)|(rotated>>(e-1));
        }while(rotated!=canonical);
        array<M,32> defects{};
        // A step v is impossible when more than two residue cells require a
        // bad line, as a given diagonal family/key meets this column once.
        for(int y=0;y<=e/2;y++){
            M miss=0;
            for(M r=a;r;r&=r-1){
                int x=countr_zero(r);
                if(!(a&bit(add[x][y])) && !(a&bit(sub[x][y]))) miss|=bit(x);
            }
            int yr=(e-y)%e;
            defects[y]=defects[yr]=miss;
            int count=popcount(miss);
            if(count<=2) allowed|=bit(y)|bit(yr);
            if(!count) clean+=1+(yr!=y);
        }
        if(popcount(allowed)<p) return;
        // Try a first discarded difference or sum line. Count which second
        // lines can repair the columns with precisely one residual violation.
        bool strong=clean>=p;
        for(int f=0;!strong&&f<2;f++) for(int key=0;!strong&&key<e;key++){
            int viable=0;array<int,64> frequency{};
            for(M ys=allowed;ys;ys&=ys-1){
                int y=countr_zero(ys);
                int hit=f?sub[key][y]:add[key][y];
                M still=defects[y]&~bit(hit);
                if(!still) ++viable;
                else if(has_single_bit(still)){
                    int x=countr_zero(still);
                    frequency[sub[x][y]]++;frequency[e+add[x][y]]++;
                }
            }
            if(viable+*max_element(frequency.begin(),frequency.begin()+2*e)>=p) strong=true;
        }
        if(!strong) return;
        // The unary test is invariant under cyclic shifts of A: every failed
        // x merely moves by t, and both repair-line residues move by the same t.
        // Restore every orientation that includes the canonical origin.
        M rot=a, full=bit(e)-1;
        do{
            if(rot&1){
                int sum=e;
                for(M x=rot;x;x&=x-1) sum+=countr_zero(x);
                axes.push_back({rot,allowed,sum});
            }
            rot=((rot<<1)&full)|(rot>>(e-1));
        }while(rot!=a);
    }
    // Standard binary necklace recursion. A copy of the symbol one period
    // earlier keeps the current period; a higher symbol starts a new period.
    void necklaces(int t,int period,int ones){
        if(ones>p || ones+e-t+1<p) return;
        if(t>e){
            if(e%period==0 && ones==p) test_necklace();
            return;
        }
        int s=symbols[t-period];
        symbols[t]=s;necklaces(t+1,period,ones+s);
        if(s==0){symbols[t]=1;necklaces(t+1,t,ones+1);}
    }
    bool compatible(Axis a,Axis b){
        if((b.mask&~a.allowed)||(a.mask&~b.allowed)) return false;
        array<M,32> edges{}; M dl=0,sl=0;
        for(M xs=a.mask;xs;xs&=xs-1){
            int x=countr_zero(xs);
            for(M ys=b.mask;ys;ys&=ys-1){
                int y=countr_zero(ys),d=sub[x][y],s=add[x][y];
                if((a.mask&b.mask&bit(s)) || ((a.mask&bit(d))&&(b.mask&bit(sub[y][x])))) continue;
                edges[d]|=bit(s);
                if(!(dl&bit(d)) && !(sl&bit(s))){
                    dl|=bit(d);sl|=bit(s);
                    if(popcount(dl)>=3) return false; // certified 3-edge matching
                }
            }
        }
        // A bipartite graph has a vertex cover of size <=2 iff (1) there
        // are <=2 nonempty rows or columns, or (2) deleting some row leaves
        // a single nonempty column. Check those options independently.
        M columns=0; int rows=0;
        for(int d=0;d<e;d++) if(edges[d]){columns|=edges[d];rows++;}
        if(rows<=2 || popcount(columns)<=2) return true;
        for(int skip=0;skip<e;skip++) if(edges[skip]){
            M other=0;
            for(int d=0;d<e;d++) if(d!=skip) other|=edges[d];
            if(popcount(other)<=1) return true;
        }
        return false;
    }
    void run(){
        for(e=p;e<n;e++){
            axes.clear();symbols.fill(0);counted=0;last_rep=0;
            for(int i=0;i<e;i++) for(int j=0;j<e;j++){add[i][j]=(i+j)%e;sub[i][j]=(i-j+e)%e;}
            necklaces(1,1,0);
            uint64_t expected=1;
            for(int k=1;k<p;k++) expected=expected*(e-k)/k;
            if(counted!=expected) abort();
            sort(axes.begin(),axes.end(),[](Axis a,Axis b){return a.mask<b.mask;});
            for(size_t i=0;i<axes.size();i++){
                if(i && axes[i-1].mask==axes[i].mask) abort();
                Axis a=axes[i];
                if(shapes_only){cout<<e<<' '<<a.mask<<'\n';continue;}
                for(size_t j=i;j<axes.size();j++){
                    Axis b=axes[j];
                    int delta=a.sum-b.sum;
                    if(delta%(p+1) || abs(delta)>(n-1-e)*(p+1)) continue;
                    if(!compatible(a,b)) continue;
                    for(int x=0;x+e<n;x++){
                        int y=x+delta/(p+1);
                        if(y>=0 && y+e<n) cout<<e<<' '<<a.mask<<' '<<b.mask<<' '<<x<<' '<<y<<'\n';
                    }
                }
            }
            cerr<<e<<" candidate necklaces expanded to "<<axes.size()<<" eligible axes\n";
        }
    }
};
int main(int argc,char**argv){
    Engine s;
    s.n=argc>1?atoi(argv[1]):30;
    s.p=argc>2?atoi(argv[2]):14;
    if(s.n>30|| s.n<3 || s.p<1 || s.p>=s.n) return 2;
    s.shapes_only=(argc>3 && string(argv[3])=="shapes");
    s.run();
}
