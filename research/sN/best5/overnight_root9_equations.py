"""Direct exact equations for three free neurons in the nine-row P4 layer."""
from fractions import Fraction as Q
from pathlib import Path
import hashlib,json
import overnight_fixed_bowtie_verify as arithmetic

HERE=Path(__file__).resolve().parent


def initialize():
    inv=json.loads((HERE/'overnight_root9_inventory.json').read_text())
    netpath=HERE/'overnight_fixed_cross_net9_17.json'
    assert hashlib.sha256(netpath.read_bytes()).hexdigest()==inv['network_sha256']
    A=[list(map(Q,a)) for a in json.loads(netpath.read_text())['first_layer'][:-2]]
    a=arithmetic
    a.BASES={int(z):[[Q(c) for c in b] for b in r['basis']] for z,r in inv['flats'].items()}
    a.VALUE={S:[max(sum(row[i] for i in S),Q(0)) for row in A] for S in a.SETS}
    matrix=a.rref([[a.VALUE[S][j] for S in a.SETS[:-1]] for j in range(7)])
    pivots=[next(i for i,c in enumerate(row) if c) for row in matrix];assert len(pivots)==7
    a.ANN=[]
    for free in range(30):
        if free in pivots:continue
        row=[Q(0)]*30;row[free]=1
        for p,r in zip(pivots,matrix):row[p]=-r[free]
        assert all(sum(row[j]*a.VALUE[S][i] for j,S in enumerate(a.SETS[:-1]))==0 for i in range(7))
        a.ANN.append(row)
    assert len(a.ANN)==23
    a.RHS=[2*sum(c*(1-int(0 in S)) for c,S in zip(row,a.SETS[:-1])) for row in a.ANN]
    a.flat.cache_clear()


def case_data(zs,ds):
    a=arithmetic;blocks=[a.flat(z) for z in zs];off=[0]
    for forms,_,_ in blocks:off.append(off[-1]+len(forms))
    def equation(i):
        assert 0<=i<49;e={}
        if i<26:
            U,o=a.LOCS[i]
            for k,(z,d) in enumerate(zip(zs,ds)):
                active=len(U)==5 or z>>a.RIDX[U]&1
                if o is not None:active=active and z>>a.RIDX[U|{o}]&1
                if active:a.add(e,blocks[k][1][U],Q(d),off[k])
            return e,Q(2*(-1)**(len(U)+1))
        for k,d in enumerate(ds):a.add(e,blocks[k][2][i-26],Q(d),off[k])
        return e,a.RHS[i-26]
    coeffoff=[0]
    for z in zs:coeffoff.append(coeffoff[-1]+len(a.BASES[z]))
    forms=[]
    for k,(local,_,_) in enumerate(blocks):
        forms.extend(tuple([Q(0)]*coeffoff[k]+list(f)+[Q(0)]*(coeffoff[-1]-coeffoff[k+1])) for f in local)
    return equation,forms,coeffoff
