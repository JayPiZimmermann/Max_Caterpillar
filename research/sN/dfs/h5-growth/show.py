import pickle, sys, collections
d = pickle.load(open(sys.argv[1], 'rb'))['d']
N = len(next(iter(d))[0])
def apexes(k):
    h, M = k; nodes = {i for e in M for i in e}
    return tuple(i for i in range(N) if h[i] == -1 and i not in nodes)
print('support', len(d))
print('apex hist', collections.Counter(apexes(k) for k in d))
print('coef hist', collections.Counter(str(v) for v in d.values()))
for k, v in sorted(d.items(), key=lambda kv: (apexes(kv[0]), kv[0])):
    h, M = k
    print(f'{str(v):>6}  apex {apexes(k)}  h={h}  M={sorted(M)}')
