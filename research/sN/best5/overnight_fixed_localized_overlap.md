# A finite localized function and the residual interval overlap

This is an exact identity for the natural eight-row first hidden layer.
It neither constructs the missing target nor proves impossibility at
arbitrary second hidden layer width.

Use the group coordinates

    (a,b,p)=(sigma(u),sigma(v),sigma(u-v)),
    (c,d,q)=(sigma(s),sigma(t),sigma(s-t)).

Each group image consists of the three faces

    A: a=b+p;    B: p=0, 0<=a<=b;    C: b=0, 0<=a<=p.

The parameters `h1=b+p-a` and `h2=d+q-c` are nonnegative. For a linear
form g in the six features, define the four-ReLU expression

    P(g)=-sigma(g)+sigma(g-h1)+sigma(g+h2)-sigma(g-h1+h2).

For fixed nonnegative h1,h2, this is the overlap length of the intervals
`[0,h1]` and `[g,g+h2]`. In particular P is nonnegative, vanishes if
either h is zero, and vanishes when `g>=h1` or `g<=-h2`.

Now set

    Q=P(0)-P(b)-P(-d)+P(b-d).

This is a finite shallow expression supported entirely on B×B:

* Any A face has h1=0 or h2=0, so every P term vanishes.
* On the first C face, b=0, so the four terms cancel in pairs.
* On the second C face, d=0, so they also cancel in pairs.

On B×B put `X=b-a` and `Y=d-c`. There h1=X, h2=Y, b>=X, and d>=Y.
Thus P(b)=P(-d)=0 and

    Q=min(X,Y)+P(b-d).

Reflecting both intervals around b shows that P(b-d) is precisely the
overlap length of `[a,b]` and `[c,d]`. Consequently, if R is the desired
localized interaction `min(sigma(b-a),sigma(d-c))`, then

    Q = R + (overlap of [a,b] and [c,d], localized to B×B).

Q actually uses only nine ReLUs after the globally fixed signs are
simplified:

    Q=-sigma(h2-h1)-sigma(a-p)+sigma(a-p+h2)
      -sigma(q-c)+sigma(q-c-h1)+P(b-d).

This proves that collective cancellation can localize a nonzero function
to B×B with finitely many units. It explains why the earlier independence
proof for the narrower individually localized blocks does not settle the
all-width question.

## A larger restricted family still has an unavoidable residual

For any real `lambda,mu>=1`, define

    Q_lambda,mu=P(0)-P(lambda*b)-P(-mu*d)+P(lambda*b-mu*d).

The same support argument applies. On B×B it equals

    min(X,Y)+P(lambda*b-mu*d).

The residual functions in this family are linearly independent modulo
linear functions on the interior of B×B. Indeed use independent positive
coordinates `(a,c,X,Y)`, with `b=a+X,d=c+Y`. The four residual normals are

    (lambda,-mu,lambda,-mu),
    (lambda,-mu,lambda-1,-mu),
    (lambda,-mu,lambda,-mu+1),
    (lambda,-mu,lambda-1,-mu+1).

After dividing by lambda and setting `t=mu/lambda`, `k=1/lambda`, their
first two coordinates are `(1,-t)`, while the last two are

    (1,-t), (1-k,-t), (1,-t+k), (1-k,-t+k).

The last normal is unique to its parameter pair: both its third
coordinate is below one and its fourth is above -t. It cannot coincide
with any other corner type; equality with another last corner forces
the same t,k, hence the same lambda,mu. Every such hyperplane crosses
the positive orthant because the first two coefficients have opposite
signs. A nonzero finite linear combination therefore has an uncancelled
gradient jump on a generic point of one unique last hyperplane.

Thus no finite linear combination of these Q functions can cancel all
residual overlaps while retaining the target min(X,Y). General shallow
expressions may use shifted blocks and additional cancellations outside
this family; no normal-form reduction to this family has been proved.
