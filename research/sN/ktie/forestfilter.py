import sys, ast
def forest(M, k):
    p = list(range(k))
    def f(x):
        while p[x] != x: x = p[x]
        return x
    for i, j in M:
        a, b = f(i), f(j)
        if a == b: return False
        p[a] = b
    return True
k = int(sys.argv[1]); n = 0; ap = 0
for line in sys.stdin:
    if not line.startswith('MATCH'): continue
    i = line.index('['); v = ast.literal_eval(line[6:i].strip()); M = ast.literal_eval(line[i:line.rindex(']') + 1])
    if forest(M, k):
        n += 1
        apex = any(v[t] == -1 and all(t not in e for e in M) for t in range(k))
        ap += apex
        print(line.strip(), 'apex' if apex else '')
print('forest matches', n, 'with apex', ap)
