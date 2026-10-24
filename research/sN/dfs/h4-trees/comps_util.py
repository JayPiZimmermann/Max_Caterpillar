def comps(vs, adj):
    vs = set(vs); out = []
    while vs:
        s = vs.pop(); st = [s]; K = {s}
        while st:
            u = st.pop()
            for w in adj[u]:
                if w in vs: vs.remove(w); K.add(w); st.append(w)
        out.append(K)
    return out
