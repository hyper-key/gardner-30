// Necessary 1D tests for 29 diagonal lines and two missing frame incidences.
#include <algorithm>
#include <bit>
#include <cstdint>
#include <iostream>
#include <random>
#include <vector>
using Mask=uint32_t;
Mask bit(int i){return Mask(1)<<i;}
int n=30, e;
Mask full;
Mask rot(Mask x,int k){return ((x<<k)|(x>>(e-k)))&full;}
struct Axis {Mask u,allowed; int sum;};

// A failing 1D test at row x, column y, after dropping the requirements
// involving V, can only be covered by bad line x-y or x+y modulo e.
int one_dim(Mask u, Axis &a, bool strong){
    Mask clean=0, maybe=0, defect[30]={};
    int total=e;
    for (Mask s=u; s; s&=s-1) total+=std::countr_zero(s);
    for(int v=0;v<e;v++){
        defect[v]=u&~(rot(u,v)|rot(u,e-v));
        int h=std::popcount(defect[v]);
        if(!h) clean|=bit(v);
        if(h<=2) maybe|=bit(v);
    }
    a={u,maybe,total};
    if(std::popcount(maybe)<14) return 0;
    if(!strong || std::popcount(clean)>=14) return 2;
    Mask single[60]={},two[60][60]={};
    for(Mask z=maybe&~clean;z;z&=z-1){
        int y=std::countr_zero(z);
        Mask xs=defect[y]; int x=std::countr_zero(xs); xs&=xs-1;
        int k=(e+x-y)%e,l=e+(x+y)%e;
        if(!xs){single[k]|=bit(y);single[l]|=bit(y);continue;}
        int x2=std::countr_zero(xs),k2=(e+x2-y)%e,l2=e+(x2+y)%e;
        for(int a:{k,l})for(int b:{k2,l2})two[std::min(a,b)][std::max(a,b)]|=bit(y);
    }
    for(int a=0;a<2*e;a++)for(int b=a;b<2*e;b++)
        if(std::popcount(clean|single[a]|single[b]|two[a][b])>=14) return 2;
    return 1;
}

bool compatible(Axis a,Axis b){
    if((b.u&~a.allowed)||(a.u&~b.allowed)) return false;
    int first_d=-1, first_s=-1;
    // If there is any failing edge, one of its two keys must be in a cover
    // of size <=2. The remaining failures must share a common second key.
    bool can[2][2]={{true,true},{true,true}};
    int ref[2][2]={{-1,-1},{-1,-1}};
    for(Mask yy=b.u;yy;yy&=yy-1){
        int y=std::countr_zero(yy);
        for(Mask xx=a.u;xx;xx&=xx-1){
            int x=std::countr_zero(xx), d=(e+x-y)%e,s=(x+y)%e;
            if((bit(s)&a.u&b.u)||((bit(d)&a.u)&&(bit((e-d)%e)&b.u))) continue;
            if(first_d<0){first_d=d;first_s=s;}
            int key[2]={d,s};
            for(int j=0;j<2;j++){
                if((j==0 && d==first_d)||(j==1 && s==first_s))continue;
                for(int f=0;f<2;f++){
                    if(ref[j][f]<0)ref[j][f]=key[f];
                    else if(ref[j][f]!=key[f])can[j][f]=false;
                }
            }
            if(!can[0][0]&&!can[0][1]&&!can[1][0]&&!can[1][1])return false;
        }
    }
    return true;
}

#ifndef FRAME29_LIBRARY
int main(int argc,char**argv){
    bool exhaustive=argc>1 && std::string(argv[1])=="full";
    bool pairs=exhaustive || (argc>1 && std::string(argv[1])=="pairs");
    std::mt19937 gen(291514);
    for(e=14;e<=29;e++){
        if(pairs && !exhaustive && e>17)break;
        full=bit(e)-1;
        uint64_t all=0,weak=0,strong=0;std::vector<Axis> v;
        auto test=[&](Mask u){Axis a;int t=one_dim(u,a,true);++all;weak+=t>=1;strong+=t==2;if(pairs && t==2)v.push_back(a);};
        if(exhaustive || e<=19){
            for(Mask x=bit(13)-1;x<bit(e-1);){
                test((x<<1)|1);Mask low=x&-x,up=x+low;x=up|(((x^up)/low)>>2);
            }
        } else {
            for(int i=0;i<100000;i++){
                Mask u=1;
                while(std::popcount(u)<14)u|=bit(1+std::uniform_int_distribution<int>(0,e-2)(gen));
                test(u);
            }
        }
        uint64_t congruent=0,translated=0,modpairs=0;
        if(pairs)for(size_t i=0;i<v.size();i++)for(size_t j=i;j<v.size();j++){
            int delta=v[i].sum-v[j].sum;if(delta%15)continue;delta/=15;
            if(abs(delta)>29-e)continue;congruent++;
            if(!compatible(v[i],v[j]))continue; modpairs++;
            for(int t=0;t+e<30;t++){
                int b=t+delta;if(b<0 || b+e>=30)continue;
                ++translated;
                if(exhaustive || e<=16)std::cout<<e<<' '<<v[i].u<<' '<<v[j].u<<' '<<t<<' '<<b<<'\n';
            }
        }
        std::cout.flush();
        std::cerr<<e<<" raw "<<all<<" weak "<<weak<<" strong "<<strong
                 <<" offset-compatible "<<congruent<<" modular "<<modpairs<<" translations "<<translated<<'\n';
    }
}
#endif
