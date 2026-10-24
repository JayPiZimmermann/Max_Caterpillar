import json,sys,numpy as np
from fractions import Fraction as Fr
for f in sys.argv[1:]:
    J=json.load(open(f)); N=J["N"]
    A=np.array([[float(Fr(v)) for v in r] for r in J["first_layer"]]); W=np.array([[float(Fr(v)) for v in r] for r in J["second_layer"]]); d=np.array([float(Fr(v)) for v in J["output"]])
    rng=np.random.default_rng(123); X=rng.standard_normal((10**6,N))*rng.uniform(0.01,1e3,(10**6,1))
    X[:1000,1:]=X[:1000,:1]  # ties
    F=np.maximum(np.maximum(X@A.T,0)@W.T,0)@d
    print(f, A.shape, W.shape, "max rel err", (np.abs(F-X.max(1))/np.abs(X).max(1)).max())
