# Independent audit of the 650000 quadratic constant

The mathematical/source audit found no scope gap in `Quadratic.lean`.
The final kernel status is recorded by `quadratic_check.exit` and its log;
this note does not substitute for a successful checker exit.

The audited target is the original nine-array affine-skip network, with
arbitrary real parameters and biases, exact on every real input, input
arity N at least three, and **total** original first hidden width at most
N squared. Its second hidden width is at least N squared divided by650000.
Neither a structural conjecture nor a probability conclusion is an input.

The proof uses the already established all-real five-input matching
obstruction H(5,2). It first takes an actual half restriction preserving
both hidden index types. The sharper support statistic is the fourth falling
factorial, not the fourth power: its budget is

    16 sum_j (support_size_j)_4 <= 105 h1.

The number of non-braid rows is bounded separately by h1, so no unproved
simultaneous selection of two different good half restrictions is used.
Support-three rows contribute zero to the falling moment but are still
charged in this separate count.

For tail arity m at least100000 the proof takes K=floor(m/12). It uses the
literal bad-isolated-rank event bound41K/(10m), coverage at least9/20,
and actual neuron-event cost at most465/K squared. The factor2/7 in that
cost is proved from the scalar maximum of y squared times exp(-y); it does
not assume a distributional improvement.

The arithmetic closes with m squared divided by151900. The half restriction
satisfies N squared at most4.1m squared, so the resulting denominator is
at most622790, strictly below650000. The same4.1 scaling gives the support
budget105*4.1/16=26.90625 below27. The cases N at most250000 follow from
the independent linear lower bound N at most2h2+2.

`QuadraticCheck.lean` restates the raw-array contract and the actual half
restriction contract independently. It also checks concrete caterpillar
networks at N=3 and N=250001, the first odd arity past the small-arity branch.
The latter keeps the large second width symbolic and tests the hypothesis
class without expanding a factorial-size construction.
