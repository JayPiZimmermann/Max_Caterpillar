"""Emit elementary Lean proof terms for a proposed rational (9,14) identity.

No numerical search or external certificate is used. Rational arithmetic only
chooses algebraic rewrites; Lean must prove all inequalities, identities, and
closed-cone coverage. Only the Lean kernel result is evidence.
"""
from fractions import Fraction as Q
from itertools import permutations
from pathlib import Path

HERE=Path(__file__).resolve().parent
# Proposed exact coefficients; no external certificate is a dependency.
W=[[Q(v) for v in row] for row in [[-1, 1, 0, 0, 0], [-1, 0, 1, 0, 0], [0, -1, 1, 0, 0], [-1, 0, 0, 1, 0], [-1, 0, 0, 0, 1], [0, 0, 0, 1, -1], [0, 0, 1, 0, -1], [1, 0, 0, 0, 0], [-1, 0, 0, 0, 0]]]
V=[[Q(v) for v in row] for row in [['0', '1/2', '-1/2', '-1/2', '0', '0', '-1/2'], ['1/2', '0', '0', '-1/2', '0', '1/2', '-1/2'], ['1/2', '0', '1/2', '0', '0', '1/2', '-1/2'], ['0', '0', '0', '0', '0', '1', '-1'], ['0', '0', '1/2', '0', '0', '1/2', '-1/2'], ['0', '1/2', '-1/2', '-1/2', '0', '0', '0'], ['0', '1/2', '-1/2', '0', '-1/2', '0', '0'], ['0', '1/2', '0', '0', '-1/2', '0', '0'], ['0', '1/2', '0', '0', '0', '1/2', '-1/2'], ['1', '0', '0', '-1', '0', '0', '0'], ['1/2', '0', '0', '-1/2', '0', '1/2', '0'], ['1', '0', '0', '0', '-1', '0', '0']]]
D=[Q(v) for v in ['1', '-1', '1', '1', '-1', '-1', '-1', '1', '-1', '1', '-1', '1']]
R=[Q(v) for v in ['-1/2', '1/2', '0', '0', '1', '1/2', '0']]
edges=[(next(i for i,v in enumerate(row) if v==1),next(i for i,v in enumerate(row) if v==-1)) for row in W[:7]]
def q(v):
 if v.denominator==1:return str(v.numerator)
 return f'({v.numerator}/{v.denominator} : ℝ)'
def lin(v,term):
 return ' + '.join(f'({q(c)}) * ({term(i)})' for i,c in enumerate(v) if c) or '(0 : ℝ)'
def vec(v):return '!['+','.join(str(c) if c.denominator==1 else f'{c.numerator}/{c.denominator}' for c in v)+']'
def matrix(M):return '!['+',\n    '.join(vec(v) for v in M)+']'
features=[f'relu (x {i} - x {j})' for i,j in edges]
args=[lin(v,lambda i:features[i]) for v in V]
rem= 'x 0 + '+lin(R,lambda i:features[i])
rhs=' +\n    '.join(f'({q(d)}) * relu ({a})' for d,a in zip(D,args))+' +\n    '+rem
head='''import MaxCaterpillar.SmallN.Common
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace MaxCaterpillar.WidthTradeoff.P4
open BigOperators MaxCaterpillar.SmallN
open MaxNN.Caterpillar.Corrections
'''
defs=head+f'noncomputable def rhs (x : Point 5) : ℝ :=\n    {rhs}\n\n'+'''
theorem max_eq (x : Point 5) (t : Fin 5)
    (h0 : x 0 ≤ x t) (h1 : x 1 ≤ x t) (h2 : x 2 ≤ x t)
    (h3 : x 3 ≤ x t) (h4 : x 4 ≤ x t) : Maximum 5 x = x t := by
  apply maximum_eq_of_le x t
  intro i
  fin_cases i
  exacts [h0,h1,h2,h3,h4]

theorem relu_scale (c u : ℝ) (hc : 0 ≤ c) : relu (c*u) = c*relu u := by
  unfold relu
  rcases le_total 0 u with h | h
  · rw [max_eq_right h, max_eq_right (mul_nonneg hc h)]
  · rw [max_eq_left h, max_eq_left (mul_nonpos_of_nonneg_of_nonpos hc h), mul_zero]

theorem relu_scale_neg (c u : ℝ) (hc : 0 ≤ c) :
    relu (-(c*u)) = c*relu u - c*u := by
  have h := relu_sub_relu_neg_self (c*u)
  rw [relu_scale c u hc] at h
  linarith
end MaxCaterpillar.WidthTradeoff.P4
'''
(HERE/'UpperNineDefs.lean').write_text(defs)
orders=list(permutations(range(5)))
for chunk in range(4):
 lines=['import research.sN.width_tradeoff.UpperNineDefs',head.split('\n',1)[1]]
 for idx in range(chunk*30,(chunk+1)*30):
  order=orders[idx];rank={x:i for i,x in enumerate(order)}
  hs=[f'(h{i} : x {order[i+1]} ≤ x {order[i]})' for i in range(4)]
  lines.append(f'theorem chamber{idx} (x : Point 5) '+ ' '.join(hs)+' : Maximum 5 x = rhs x := by')
  for i,(a,b) in enumerate(edges):
   active=rank[a]<rank[b]
   expr=f'x {a} - x {b}' if active else '0'
   theorem='relu_eq_self' if active else 'relu_eq_zero'
   lines.append(f'  have f{i} : {features[i]} = {expr} := {theorem} (by linarith only [h0,h1,h2,h3])')
  activeW=[row if rank[a]<rank[b] else [Q(0)]*5 for row,(a,b) in zip(W,edges)]
  for k,v in enumerate(V):
   g=[sum(v[j]*activeW[j][i] for j in range(7)) for i in range(5)]
   values=[sum(g[i] for i in order[:l]) for l in range(1,5)]
   gl=lin(g,lambda i:f'x {i}')
   if min(values)>=0 or max(values)<=0:
    positive=min(values)>=0
    target=gl if positive else '0'
    theorem='relu_eq_self' if positive else 'relu_eq_zero'
    lines += [f'  have o{k} : relu ({args[k]}) = {target} := by',
      f'    rw [show ({args[k]}) = ({gl}) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]',
      f'    exact {theorem} (by linarith only [h0,h1,h2,h3])']
   else:
    scale=next(c for c in g if c);normal=[c/scale for c in g];nl=lin(normal,lambda i:f'x {i}')
    c=abs(scale)
    if scale>0:
     target=f'({q(c)}) * relu ({nl})';ident=f'({q(c)}) * ({nl})';lem=f'relu_scale ({q(c)}) ({nl}) (by norm_num)'
    else:
     target=f'({q(c)}) * relu ({nl}) - ({q(c)}) * ({nl})';ident=f'-(({q(c)}) * ({nl}))';lem=f'relu_scale_neg ({q(c)}) ({nl}) (by norm_num)'
    lines += [f'  have o{k} : relu ({args[k]}) = {target} := by',
      f'    rw [show ({args[k]}) = ({ident}) by simp only [f0,f1,f2,f3,f4,f5,f6]; ring]',
      f'    exact {lem}']
  lines += [f'  have hm : Maximum 5 x = x {order[0]} := max_eq x {order[0]} '+ ' '.join(['(by linarith only [h0,h1,h2,h3])']*5)+'',
     '  rw [hm]', '  simp only [rhs,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11]', '  simp only [f0,f1,f2,f3,f4,f5,f6]', '  ring', '']
 lines+=['end MaxCaterpillar.WidthTradeoff.P4']
 (HERE/f'UpperNineCells{chunk}.lean').write_text('\n'.join(lines)+'\n')
# All-order coverage by insertion sorting; branch hypotheses explicitly discharge
# the consecutive-order hypotheses of each closed-cone lemma.
lines=[f'import research.sN.width_tradeoff.UpperNineCells{i}' for i in range(4)]
lines += [head.split('\n',1)[1], 'theorem identity (x : Point 5) : Maximum 5 x = rhs x := by']
counter=[0]
def cover(done,pending,space,hyps):
 if not pending:
  idx=orders.index(tuple(done));args=' '.join('(by linarith only ['+','.join(hyps)+'])' for _ in range(4))
  lines.append(space+f'exact chamber{idx} x {args}');return
 v=pending[0]
 def insert(k,path,hh):
  if k==len(done):cover(done+[v],pending[1:],path,hh);return
  h=f'h{counter[0]}';counter[0]+=1
  lines.append(path+f'rcases le_total (x {v}) (x {done[k]}) with {h} | {h}')
  lines.append(path+'·')
  insert(k+1,path+'  ',hh+[h])
  lines.append(path+'·')
  cover(done[:k]+[v]+done[k:],pending[1:],path+'  ',hh+[h])
 insert(0,space,hyps)
cover([0],[1,2,3,4],'  ',[])
lines+=['','end MaxCaterpillar.WidthTradeoff.P4']
(HERE/'UpperNineIdentity.lean').write_text('\n'.join(lines)+'\n')
lines=['import research.sN.width_tradeoff.UpperNineIdentity',head.split('\n',1)[1]]
lines += [f'private def firstQ : Fin 9 → Fin 5 → ℚ := {matrix(W)}',
 f'private def rowsQ : Fin 12 → Fin 9 → ℚ := {matrix([v+[Q(0),Q(0)] for v in V])}',
 f'private def outQ : Fin 12 → ℚ := {vec(D)}',
 f'private def remQ : Fin 9 → ℚ := {vec(R+[Q(1),Q(-1)])}',
 'private def first : Fin 9 → Fin 5 → ℝ := fun j i => firstQ j i',
 'private def rows : Fin 12 → Fin 9 → ℝ := fun k j => rowsQ k j',
 'private def out : Fin 12 → ℝ := fun k => outQ k',
 'private def rem : Fin 9 → ℝ := fun j => remQ j',
 'private noncomputable def features (x : Point 5) : Fin 9 → ℝ := !['+', '.join(features+['relu (x 0)','relu (-x 0)'])+']',
 '''private theorem first_eval (x : Point 5) (j : Fin 9) :
    relu (∑ i, first j i*x i) = features x j := by
  fin_cases j <;> norm_num [first, firstQ, features, Fin.sum_univ_succ] <;>
    congr 1 <;> ring_nf <;> rfl

private theorem expansion (x : Point 5) :
    Maximum 5 x =
      ∑ k, out k * relu (lf (rows k) fun j => relu (∑ i, first j i*x i)) +
      lf rem (fun j => relu (∑ i, first j i*x i)) := by
  simp_rw [first_eval]
  rw [identity]
  simp [lf, rows, rowsQ, out, outQ, rem, remQ, features, Fin.sum_univ_succ, rhs]
  have h := relu_sub_relu_neg_self (x 0)
  ring_nf
  linarith [h]

/-- Exact max-five at physical widths (9,14), rational weights, zero biases. -/
theorem max_five_nine_fourteen :
    ∃ net : Network 5 9 14,
      (∀ x, net.eval x = Maximum 5 x) ∧
      net.HasRationalWeights ∧ net.HasZeroBiases := by
  apply network_of_rows first (fun j i => ?_) rows (fun k j => ?_)
    out (fun k => ?_) rem (fun j => ?_) (Maximum 5) expansion
  all_goals apply mem_ratField_iff.mpr
  · exact ⟨firstQ j i, rfl⟩
  · exact ⟨rowsQ k j, rfl⟩
  · exact ⟨outQ k, rfl⟩
  · exact ⟨remQ j, rfl⟩

#print axioms max_five_nine_fourteen
end MaxCaterpillar.WidthTradeoff.P4
''']
(HERE/'UpperNineNetwork.lean').write_text('\n\n'.join(lines))
