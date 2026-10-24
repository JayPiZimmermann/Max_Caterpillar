"""Rationalized 4-neuron identity for max_5 read off fitkp_N5_k5.npy (trial 23; neuron 3 had d = 0).
p_ij = relu(x_i - x_j).
  max_5 = x1 + p01
        + relu(x4 - x2 - p02 + p34)
        - relu((x1 - x2 - x3 + x4)/2 + p01/2 - p02 + p12/2 - p13/2 - p14/2 + p34)
        + 1/2 relu(-x1 + x2 - x3 + x4 - p01 + p12 - p13 + p14)
        + 1/2 relu(-x1 + x2 + x3 - x4 - p01 + p12 + p13 - p14)
"""
from fractions import Fraction as Fr
h = Fr(1, 2)
N = 5
R = ([0, 1, 0, 0, 0], {(0, 1): 1})
NEURONS = [
    (1, [0, 0, -1, 0, 1], {(0, 2): -1, (3, 4): 1}),
    (-1, [0, h, -h, -h, h], {(0, 1): h, (0, 2): -1, (1, 2): h, (1, 3): -h, (1, 4): -h, (3, 4): 1}),
    (h, [0, -1, 1, -1, 1], {(0, 1): -1, (1, 2): 1, (1, 3): -1, (1, 4): 1}),
    (h, [0, -1, 1, 1, -1], {(0, 1): -1, (1, 2): 1, (1, 3): 1, (1, 4): -1}),
]
