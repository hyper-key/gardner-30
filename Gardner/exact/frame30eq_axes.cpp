// The two 1D exception budgets for the full split are separate.
#define FRAME29_LIBRARY
#include "frame29_axes.cpp"
#include <map>
#include <tuple>

struct Located {Axis axis;int offset;Mask original;};
int invariant(Mask unused){
    int sum=0,squares=0;
    for(int i=0;i<30;i++) if(!(unused&bit(i))){
        int x=2*i-29;sum+=x;squares+=x*x;
    }
    return 21*sum*sum-5*squares;
}
Mask rev(Mask unused){
    Mask ans=0;
    for(Mask x=unused;x;x&=x-1)ans|=bit(29-std::countr_zero(x));
    return ans;
}
// All failures in a SINGLE 1D test must be covered by <=2 typed residues.
bool side(Mask u,Mask v){
    int pick[2]={-1,-1},ref[2][2]={{-1,-1},{-1,-1}};
    bool ok[2][2]={{true,true},{true,true}};
    for(Mask yy=v;yy;yy&=yy-1){
        int y=std::countr_zero(yy);
        Mask failures=u&~(rot(u,y)|rot(u,e-y));
        for(Mask xx=failures;xx;xx&=xx-1){
            int x=std::countr_zero(xx);
            int edge[2]={(x+e-y)%e,(x+y)%e};
            if(pick[0]<0){pick[0]=edge[0];pick[1]=edge[1];}
            for(int j=0;j<2;j++)if(edge[j]!=pick[j])
                for(int k=0;k<2;k++){
                    if(ref[j][k]<0)ref[j][k]=edge[k];
                    else if(ref[j][k]!=edge[k])ok[j][k]=false;
                }
            if(!ok[0][0]&&!ok[0][1]&&!ok[1][0]&&!ok[1][1])return false;
        }
    }
    return true;
}
int main(){
    for(e=14;e<=29;e++){
        full=bit(e)-1;
        std::map<int,std::vector<Located>> buckets;
        size_t raw=0,passed=0,located=0,group_pairs=0,pairs=0;
        for(Mask x=bit(13)-1;x<bit(e-1);){
            Mask u=(x<<1)|1,low=x&-x,up=x+low;x=up|(((x^up)/low)>>2);
            Axis axis;++raw;
            if(one_dim(u,axis,true)!=2)continue;
            ++passed;
            for(int t=0;t+e<30;t++){
                Mask original=(u|bit(e))<<t;
                if(rev(original)<original)continue;
                buckets[invariant(original)].push_back({axis,t,original});++located;
            }
        }
        for(auto &[h,v]:buckets)for(size_t i=0;i<v.size();i++)for(size_t j=i;j<v.size();j++){
            ++group_pairs;
            auto a=v[i],b=v[j];
            if((a.axis.u&~b.axis.allowed)||(b.axis.u&~a.axis.allowed))continue;
            if(!side(a.axis.u,b.axis.u)||!side(b.axis.u,a.axis.u))continue;
            ++pairs;
            std::cout<<e<<' '<<a.axis.u<<' '<<b.axis.u<<' '<<a.offset<<' '<<b.offset<<'\n';
        }
        std::cout.flush();
        std::cerr<<e<<" raw "<<raw<<" one_dim "<<passed<<" located "<<located<<" equal_H "<<group_pairs<<" kept "<<pairs<<'\n';
    }
}
