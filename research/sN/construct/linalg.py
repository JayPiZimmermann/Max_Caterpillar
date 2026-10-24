"""Exact rational linear algebra helpers (Fractions)."""
from fractions import Fraction as Fr

def solve(rows, rhs, nvar):
    """rows: list of dict{var:coef}; rhs list. Returns (consistent, particular solution dict, pivots, free vars)."""
    piv = {}  # pivot var -> (rowdict, rhs)
    order = []
    for r, b in zip(rows, rhs):
        r = {k: Fr(v) for k, v in r.items() if v != 0}; b = Fr(b)
        # reduce
        for pv in order:
            if pv in r:
                pr, pb = piv[pv]; f = r[pv]
                for k, v in pr.items():
                    nv = r.get(k, 0) - f * v
                    if nv == 0: r.pop(k, None)
                    else: r[k] = nv
                b -= f * pb
        if not r:
            if b != 0: return False, None, None, None
            continue
        pv = min(r); f = r[pv]
        r = {k: v / f for k, v in r.items()}; b = b / f
        # eliminate pv from existing pivots
        for q in order:
            qr, qb = piv[q]
            if pv in qr:
                g = qr[pv]
                for k, v in r.items():
                    nv = qr.get(k, 0) - g * v
                    if nv == 0: qr.pop(k, None)
                    else: qr[k] = nv
                piv[q] = (qr, qb - g * b)
        piv[pv] = (r, b); order.append(pv)
    sol = {pv: piv[pv][1] for pv in order}
    free = [v for v in range(nvar) if v not in piv]
    return True, sol, piv, free
