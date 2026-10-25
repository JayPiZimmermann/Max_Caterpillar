"""N5 structural gate for all alternating-vector J-wedge-K currents.

K is arbitrary on each oriented augmented tree, subject only to sum K=0
and equivariance under that tree's orientation-preserving automorphisms.
Ask whether its leaf-head values can equal the already certified N5 score.
This is an exact necessary compatibility test, not a kernel-descent proof.
"""
from pathlib import Path
import itertools,json,time
import networkx as nx
import sympy as S
from overnight_uniform_pruning_edge_current import signed_roots
from overnight_uniform_pruning_signed5_check import score as known_score
from overnight_uniform_pruning_signed5_check import canon
from overnight_uniform_pruning_edge_current import HERE,fmpq,fmpq_mat

def desired(B,H):
    G=nx.Graph(B);u,v=H;E=[e for e in B if e!=H]
    if G.degree(v)==1:apex=v;root=u;sgn=1
    elif G.degree(u)==1:apex=u;root=v;E=[(b,a)for a,b in E];sgn=-1
    else:return None
    p={apex:0};p.update({w:i+1 for i,w in enumerate(x for x in range(5)if x!=apex)})
    unit={'root':p[root],'edges':[(p[a],p[b])for a,b in E]}
    return sgn*known_score(unit)

def canonical_leaf(B,H):
    G=nx.Graph(B);u,v=H;E=[e for e in B if e!=H]
    if G.degree(v)==1:apex=v;root=u;sgn=1
    elif G.degree(u)==1:apex=u;root=v;E=[(b,a)for a,b in E];sgn=-1
    else:return None
    p={apex:0};p.update({w:i+1 for i,w in enumerate(x for x in range(5)if x!=apex)})
    return sgn,canon(p[root],[(p[a],p[b])for a,b in E])

def normalized_key(U):
    keys=[]
    for p0 in itertools.permutations(range(1,5)):
        p={0:0,**{i+1:p0[i]for i in range(4)}};h=[0]*5;h[0]-=1;h[p[U['root']]]+=1;E=[]
        for u,v in U['edges']:
            u,v=p[u],p[v];E.append(tuple(sorted((u,v))))
            if u>v:h[u]+=1;h[v]-=1
        keys.append((tuple(h),tuple(sorted(E))))
    return min(keys)

def main():
    start=time.monotonic();cases=[];units=json.loads((HERE/'overnight_uniform_pruning_signed_gate.json').read_text())['units'];index={canon(u['root'],u['edges']):i for i,u in enumerate(units)};constraints=[];constraint_labels=[]
    for i,u in enumerate(units):
        if max(dict(nx.Graph(u['edges']).degree()).values())==3:
            row=[0]*26;row[i]=1;constraints.append(row);constraint_labels.append('deficient '+str(i))
    representatives={}
    for i,u in enumerate(units):
        k=normalized_key(u)
        if k in representatives:
            row=[0]*26;row[i]=1;row[representatives[k]]=-1;constraints.append(row);constraint_labels.append('equal function '+str((i,representatives[k])))
        else:representatives[k]=i
    for G in nx.nonisomorphic_trees(5):
        E=list(G.edges)
        for bits in itertools.product((0,1),repeat=4):
            B=[(v,u)if b else(u,v)for(u,v),b in zip(E,bits)];J=signed_roots(G);rows=[[1]*5];rhs=[0];symbolic_rhs=[[0]*26];labels=['zero_sum'];oriented=set(B)
            for p in itertools.permutations(range(5)):
                if {(p[u],p[v])for u,v in B}!=oriented:continue
                sign=(-1)**sum(p[i]>p[j]for i in range(5)for j in range(i+1,5))
                for v in range(5):
                    row=[0]*5;row[p[v]]+=1;row[v]-=sign;rows.append(row);rhs.append(0);symbolic_rhs.append([0]*26);labels.append('automorphism '+str(p)+' vertex '+str(v))
            for H in B:
                val=desired(B,H)
                if val is None:continue
                u,v=H;F=G.copy();F.remove_edge(u,v);C=nx.node_connected_component(F,u);sj=sum(J[w]for w in C);row=[-(J[u]-J[v])if w in C else 0 for w in range(5)];row[u]+=sj;row[v]-=sj;rows.append(row);rhs.append(val);labels.append('head '+str(H));sr=[0]*26;sgn,key=canonical_leaf(B,H);sr[index[key]]=sgn;symbolic_rhs.append(sr)
            A=S.Matrix(rows);b=S.Matrix(rhs);good=A.rank()==A.row_join(b).rank();entry={'oriented_tree':B,'J':J,'compatible':good,'rank':A.rank()}
            for rel in A.T.nullspace():
                cr=list((rel.T*S.Matrix(symbolic_rhs)));cr=[S.Rational(x)for x in cr]
                if any(cr):constraints.append(cr);constraint_labels.append('current on '+str(B))
            if not good:
                rel=next(z for z in A.T.nullspace()if(z.T*b)[0]);entry.update(contradiction={labels[i]:str(z)for i,z in enumerate(rel)if z},pairing=str((rel.T*b)[0]),rows=rows,rhs=rhs,labels=labels)
            cases.append(entry)
    target=[0]*26
    for mask in range(1,8):
        cuts={j for j in range(1,4)if mask>>(j-1)&1};edges=[(max([0]+[i for i in cuts if i<j])+1,j+1)for j in range(1,4)];root=max(cuts)+1;target[index[canon(root,edges)]]+=(-1)**(5+len(cuts))
    C=S.Matrix(constraints);t=S.Matrix([target]);forced=C.rank()==C.col_join(t).rank();architecture={'constraints':len(constraints),'rank':C.rank(),'target_forced_zero':forced,'signed_caterpillar_vector':target}
    if forced:
        w,params=C.T.gauss_jordan_solve(S.Matrix(target));w=w.subs({p:0 for p in params});architecture['contradiction_combination']=[{'weight':str(w[i]),'reason':constraint_labels[i],'row':list(map(str,constraints[i]))}for i in range(len(w))if w[i]]
    D=json.loads((HERE/'overnight_uniform_pruning_signed_gate.json').read_text());M=fmpq_mat([[fmpq(x)for x in row]for row in D['rows']]);RR,rank=M.rref();R=S.Matrix([[S.Rational(str(RR[i,j]))for j in range(27)]for i in range(rank)]);ker=(C*R[:,:26].T).nullspace();responses=[(v.T*R[:,26])[0]for v in ker];architecture['exact_grid_intersection']={'dimension':len(ker),'target_responses':list(map(str,responses)),'scope':'No nonzero response here closes the current architecture only after the load-bearing grid relations are proved as all-frequency identities.'}
    rels=R[:,:26].nullspace();rels.sort(key=lambda v:sum(bool(x)for x in v));known=S.zeros(26,1);known[3]=-3;known[16]=1
    base=C.col_join(known.T);architecture['prior_proved_relation_alone_forces_zero']=base.rank()==base.col_join(t).rank()
    chosen=[];cur=C
    for v in rels:
        if cur.rank()!=cur.col_join(v.T).rank():cur=cur.col_join(v.T);chosen.append(v)
        if cur.rank()==cur.col_join(t).rank():break
    for v in chosen[:]:
        others=[w for w in chosen if w is not v];test=C.col_join(S.Matrix.hstack(*others).T)if others else C
        if test.rank()==test.col_join(t).rank():chosen=others
    architecture['load_bearing_grid_relations']=[{str(i):str(x)for i,x in enumerate(v)if x}for v in chosen]
    combined=C.col_join(S.Matrix.hstack(*chosen).T);w,params=combined.T.gauss_jordan_solve(S.Matrix(target));w=w.subs({p:0 for p in params});architecture['conditional_contradiction_combination']=[{'weight':str(w[i]),'reason':constraint_labels[i]if i<len(constraints)else 'grid_relation '+str(i-len(constraints)),'row':list(map(str,list(combined.row(i))))}for i in range(len(w))if w[i]]
    out={'status':'EXACT_N5_ARBITRARY_CURRENT_SPACE_GATE','cases':len(cases),'incompatible_cases':sum(not x['compatible']for x in cases),'first_failure':next((x for x in cases if not x['compatible']),None),'architecture':architecture,'scope':'The first-failure test concerns the particular certified N5 score. The architecture test instead permits every score obeying deficient vanishing, whole-function head slides, and arbitrary alternating current vectors; target_forced_zero excludes all such current-based separators at N5 using the proved signed caterpillar identity.','seconds':time.monotonic()-start};Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
