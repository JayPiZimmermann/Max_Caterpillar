"""Valid absolute-value inequalities from short rational linear circuits.

If sum_i c_i f_i=0, then sum_(i!=j)|c_i||f_i(x)| >= |c_j||f_j(x)|.
The producer may use any discovered relation; checking the displayed
linear identity and rational Farkas witness suffices independently.
"""
import functools
import itertools
from fractions import Fraction as Q
from flats_loc import nullspace


@functools.lru_cache(maxsize=2048)
def block_circuits(forms,max_size=4):
    result=[]
    for size in range(3,max_size+1):
        for inds in itertools.combinations(range(len(forms)),size):
            relations=nullspace(list(zip(*(forms[i] for i in inds))),size)
            if len(relations)==1 and all(relations[0]):
                result.append(tuple((i,c) for i,c in zip(inds,relations[0])))
    return tuple(result)


def circuits(forms,offsets,max_size=4):
    result=[]
    for k in range(len(offsets)-1):
        ids=[i for i,f in enumerate(forms) if any(f[offsets[k]:offsets[k+1]])]
        local=tuple(tuple(forms[i][offsets[k]:offsets[k+1]]) for i in ids)
        for rel in block_circuits(local,max_size):
            result.append(tuple((ids[i],c) for i,c in rel))
    return result


def inequalities(forms,offsets,max_size=4):
    result=[]
    for rel in circuits(forms,offsets,max_size):
        for focus,coef in rel:
            row=[Q(0)]*(len(forms)+1)
            for i,c in rel:row[i+1]=abs(c)*(-1 if i==focus else 1)
            result.append(row)
    return result
