"""dim W_N (ambient) versus dim V^TI_N; usage: dims.py N [prime]."""
import sys
import time
import flint
from ambient import Ambient, unit_kink_sets, units_of, cell_data, base_funcs

P1 = 2_147_483_629


def sparse_to_nmod(rows, ncols, p):
    M = flint.nmod_mat(len(rows), ncols, p)
    for r, row in enumerate(rows):
        for c, x in row.items():
            M[r, c] = x % p
    return M


def main(N, p=P1):
    t0 = time.time()
    U = units_of(N)
    perms, data, D = unit_kink_sets(N, U)
    A = Ambient(N, D)
    C = A.constraints()
    _, bdata = cell_data(N, base_funcs(N))
    vecs = [A.vector(row) for row in data] + [A.vector(row) for row in bdata]
    _, mdata = cell_data(N, [('max',)])
    mvec = A.vector(mdata[0])
    # sanity: every vector satisfies the constraints
    for v in vecs + [mvec]:
        for r in C:
            assert sum(x * v.get(k, 0) for k, x in r.items()) == 0
    rC = sparse_to_nmod(C, A.nvars, p).rank()
    rV = sparse_to_nmod(vecs, A.nvars, p).rank()
    rVm = sparse_to_nmod(vecs + [mvec], A.nvars, p).rank()
    print(f'N={N} p={p} units={len(U)} cells={len(perms)} '
          f'kinkdirs/cell avg={sum(map(len, D))/len(D):.1f} distinct={len(set().union(*map(set, D)))} '
          f'nvars={A.nvars} constraints={len(C)}')
    print(f'  dim W_N = {A.nvars - rC}   dim V^TI_N = {rV}   codim = {A.nvars - rC - rV}  '
          f'max in V: {rVm == rV}   ({time.time()-t0:.1f}s)')


if __name__ == '__main__':
    main(int(sys.argv[1]), int(sys.argv[2]) if len(sys.argv) > 2 else P1)
