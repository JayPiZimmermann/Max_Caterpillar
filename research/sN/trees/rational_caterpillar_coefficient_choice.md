# One rational coefficient choice for the Caterpillar Net

This is the coefficient-selection step of the single Caterpillar Net in
the paper. It is a mathematical proof, not a new Lean declaration.

Let D be the finite caterpillar face dictionary together with its auxiliary
functions, V its real span, and A the auxiliary span. Every function in D
is continuous and takes rational values at rational inputs. The dictionary
theorem gives max_N in V.

Choose a basis g_1,...,g_a of A from the auxiliary functions and extend it
by face functions to a basis g_1,...,g_d of V. For each added function
choose one normalized head–hinge pair. These are the retained functions K;
their number is d-a = dim(V/A).

Choose rational inputs y_1,...,y_d such that

    E_ij = g_j(y_i)

is invertible. Such inputs exist: otherwise the evaluation vectors on Q^N
would lie in a proper subspace of R^d. A nonzero linear functional
annihilating that subspace would give a nontrivial combination of the g_j
vanishing on Q^N, hence everywhere by continuity, contradicting their
linear independence.

Define the coefficients directly by the finite rational linear system

    c = E^(-1) (max_N(y_1),...,max_N(y_d))^T.

Both E and the right side are rational, so c is rational. The unique
global basis coordinates of max_N solve the same system, and therefore

    max_N(x) = sum_j c_j g_j(x)

for every real input x. The first a terms give the rational auxiliary
remainder; the other terms give the retained face coefficients.

Compile these coefficients using the paper's fixed first hidden layer and
the two signed-remainder neurons. All matrix entries are rational and all
biases zero. The second hidden layer has dim(V/A)+2 neurons, before zero
padding to the explicit combinatorial width bound. The dimension estimate
describes this same construction; it is not a second network or a later
conversion of an irrational network.

No integration or projection on an infinite-dimensional rational vector
space is needed. The basis and evaluation points are finite choices; this
argument asserts no efficiency bound for finding them. The existing Lean
rational-projection theorem proves the compatible coefficient-existence
statement by another proof route.
