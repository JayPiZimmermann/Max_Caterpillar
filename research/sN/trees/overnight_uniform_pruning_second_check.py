"""Independent rooted-path check of the full z^-4 coefficient formula.

Direct comparison data are produced with normalized heads/positive-endpoint
cuts. This checker uses root paths, orientation-defect counts, weighted rooted
shuffle moments, and distance1/2 finite-apex terms. Fraction arithmetic only.
"""
from fractions import Fraction as Q
from pathlib import Path
import itertools,json,math,time
import networkx as nx
from dfs_review_fourier import family
from overnight_uniform_pruning_infinity import rooted_cuts,sides
from overnight_uniform_pruning_jets import direct_coefficients

HERE=Path(__file__).parent

def path_formula(unit,xi):
    n=len(xi)+2;G=nx.Graph(unit['edges']);root=unit['root'];edges=unit['edges'];cut=rooted_cuts(unit);eps=[e for C,e in cut];global_sign=math.prod(eps);S=sum(xi);half=Q(S,2);k=n-4
    finite=Q(0);outside=Q(0);counts={0:0,1:0,2:0};path2_checks=0
    # The apex is finite. Only distance1 or2 between outlier vertices survives.
    for u,v in itertools.combinations(G.nodes,2):
        path=nx.shortest_path(G,u,v);dist=len(path)-1
        if dist>2:continue
        pe={frozenset(e) for e in zip(path,path[1:])};slots=[i for i in range(n) if i not in [u,v]]
        for vals in itertools.permutations(xi):
            w={i:x for i,x in zip(slots,vals)};w[u]=w[v]=-half;a=w[0];den=Q(1);qpath=[]
            for edge,(C,e) in zip(edges,cut):
                q=sum(w[i] for i in C)
                if frozenset(edge) in pe:qpath.append((q,e))
                else:den*=q*(q+e*a)
            assert den
            weight=Q(1)
            if dist==1:
                q,e=qpath[0];weight=3*q*q+3*q*e*a+a*a
            finite+=2*Q((-a)**k,den)*weight
            if dist==2 and path2_checks<10:
                # Alter the independent frequency of the middle vertex and
                # shift both outlier centres to preserve total frequency zero.
                middle=path[1];changed=dict(w);changed[middle]+=7;changed[u]-=Q(7,2);changed[v]-=Q(7,2);den2=Q(1)
                for edge,(C,e) in zip(edges,cut):
                    if frozenset(edge) in pe:continue
                    q=sum(changed[i] for i in C);den2*=q*(q+e*a)
                assert den2==den
                path2_checks+=1
    # The apex is an outlier. Reroot at the partner vertex v.
    for v in G:
        rp=nx.shortest_path(G,root,v);path={frozenset(e) for e in zip(rp,rp[1:])};bad=[j for j,(edge,e) in enumerate(zip(edges,eps)) if frozenset(edge) in path and e==-1];b=len(bad)
        if b>2:continue
        Cs=[]
        for C in sides(edges,edges):Cs.append(set(G)-C if v in C else C)
        slots=[i for i in G if i!=v]
        for vals in itertools.permutations(xi):
            w=dict(zip(slots,vals));qs=[sum(w[i] for i in C) for C in Cs];rho=[]
            for edge,e,q in zip(edges,eps,qs):rho.append(q-half if frozenset(edge) in path else e*q-half)
            rho.extend(Q(qs[j]-S,2) for j in bad)
            R=sum(rho);h2=(R*R+sum(t*t for t in rho))/2
            H=[Q(1),-k*half-R,Q(math.comb(k,2))*half*half+k*half*R+h2][2-b]
            outside+=2*(-1)**n*global_sign*Q(-1,2)**b*Q(math.prod(qs[j] for j in bad),math.prod(qs))*H
            counts[b]+=1
    return finite,outside,counts,path2_checks

def main():
    start=time.monotonic();checks=[];units=[{'root':u['root'],'edges':u['edges']} for u in family(5,'all')]
    for u in units:
        xi=[1,3,9];f,o,c,p=path_formula(u,xi);old,new=direct_coefficients(u,xi);assert f+o==new
        checks.append({'arity':5,'unit':u,'xi':xi,'finite_apex':str(f),'outlier_apex':str(o),'total':str(new),'path_defect_assignments':c,'cylindrical_controls':p})
    E=[(1,2),(2,3),(3,4),(4,5),(3,6)]
    for root,rev in [(1,False),(3,True),(6,False)]:
        u={'root':root,'edges':[(v,u) if rev else (u,v) for u,v in E]};xi=[1,3,9,27,81];f,o,c,p=path_formula(u,xi);_,new=direct_coefficients(u,xi);assert f+o==new
        checks.append({'arity':7,'unit':u,'xi':xi,'finite_apex':str(f),'outlier_apex':str(o),'total':str(new),'path_defect_assignments':c,'cylindrical_controls':p})
    result={'status':'EXACT_ALL_APEX_SECOND_COEFFICIENT_CONTROLS_PASS','checked_units':len(checks),'rows':checks,'seconds':time.monotonic()-start,'scope':'Checks the general path/moment formula, not a uniform matching separator.'}
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print(result['status'],len(checks),result['seconds'],flush=True)
if __name__=='__main__':main()
