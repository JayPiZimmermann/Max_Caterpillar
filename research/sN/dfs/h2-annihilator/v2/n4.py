import sys
from germ2d import *
N = int(sys.argv[1]) if len(sys.argv) > 1 else 4
G = Germs(N)
pts = [tuple(int(c) for c in a.split(',')) for a in sys.argv[2:]] or [(0, -2, -2, -1), (0, -2, -1, 0)]
for x0 in pts:
    Hs, u, v, rays = G.rays2d(x0)
    B = 1 + max(abs(dot(h, r[0])) for h in G.hyps for r in rays)
    print('x0', x0, 'hyps', Hs)
    for r in rays:
        print('   ray', r[0], 'on', r[1])
    rows = []
    active = []
    for f in G.funcs:
        g = G.germ(f, x0, rays, B)
        w = weights_from_values(g, rays)
        if any(w):
            active.append((f, w))
        rows.append(g)
    rk = rank(rows)
    print('  germ rank (incl. 2 linear) =', rk, 'of', len(rays))
    ann = nullspace(rows, len(rays))   # functionals c with sum c_i psi(r_i) = 0
    # remove linear: functionals killing all linear functions are already among them
    for c in ann:
        print('  annihilator functional on values:', [str(x) for x in c])
    W = [w for f, w in active]
    print('  distinct weight vectors of active functions:')
    for f, w in sorted(set((str(f[0]) + ':' + str(f[1:]), tuple(w)) for f, w in active), key=lambda t: t[1])[:80]:
        print('    ', w, f)
