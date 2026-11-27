"""Export finite diagonal obstructions for the residue-compatible unused-axis pairs."""
from collections import Counter
import json
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'exact'))
from axis_matching import matching

def generate(keys):
    out=[]
    for line in keys:
        e,a,b,ta,tb=map(int,line.split())
        ur,uc=[{t+j for j in range(e) if m>>j&1}|{t+e} for m,t in ((a,ta),(b,tb))]
        ar,ac=set(range(30))-ur,set(range(30))-uc
        dif=Counter(r-c for r in ar for c in ac)
        su=Counter(r+c for r in ar for c in ac)
        target={(r-c,r+c) for r in ur for c in uc}
        matching_pairs=matching(target)
        if len(matching_pairs)>=29:
            obstruction=['29-lines',matching_pairs[:29]]
        elif any(dif[d]<2 and su[s]<2 for d,s in target):
            obstruction=['bad-cell', min((d,s) for d,s in target if dif[d]<2 and su[s]<2)]
        elif len({s for d,s in target if dif[d]<2})>13:
            sums=sorted({s for d,s in target if dif[d]<2})[:14]
            obstruction=['forced-sums',[min((d,u) for d,u in target if u==s and dif[d]<2) for s in sums]]
        else:
            assert ur==uc==set(range(1,30,2))
            obstruction=['monochrome',None]
        out.append([line,obstruction])
    return out
if __name__=='__main__':
    doc=generate(Path('modular-pairs.txt').read_text().splitlines())
    Path('modular-certificate.json').write_text(json.dumps(doc,separators=(',',':'))+'\n')
    print(dict(Counter(row[1][0] for row in doc)))
