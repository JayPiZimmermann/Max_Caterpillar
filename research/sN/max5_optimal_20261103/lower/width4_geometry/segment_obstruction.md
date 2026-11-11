# A shared-contact segment forces a balanced crossing row

Status: mathematical proof, independently derived from the actual shallow
functions. No Lean or solver-refutation claim is made in this note.

## Model and exact conclusion

Suppose

    MAX5 = ell + R + ReLU(g) + ReLU(h)

is an exact identity, with finite homogeneous shallow functions using an
actual common dictionary. Put q_i=-e_i and assume

    g(q3)=g(q4)=h(q3)=h(q4)=0.

Assume the consolidated coefficients of ReLU(x3-x4) in both g and h are
nonzero (in the application both equal +1). All other first normals omit
coordinate3 or coordinate4, with at most one exception a. The exceptional
normal is not proportional to e3-e4.

Then the exception exists, both a3 and a4 are nonzero, and necessarily

    a3+a4=0.

This conclusion does not assume a fixed sign of g or h on a face.
It follows from the full continuum of triple-contact points on a segment.

## Why the two zero sets cover the segment

For 0<t<1 put

    q(t)=-t*e3-(1-t)*e4.

Exactly inputs0,1,2 tie at the maximum there. If g(q(t)) and h(q(t))
were both nonzero, both outer ReLUs would linearize in a neighborhood.
The directional germ of the output would be shallow, while the germ of
MAX5 restricted to the top three directions is MAX3. This is impossible:
every homogeneous shallow function has a linear odd part, whereas
MAX3+MIN3 is not linear. Thus

    g(q(t))=0 or h(q(t))=0                  for every 0<t<1.

Both scalar curves vanish at t=0 and t=1 by the shared-contact assumptions.

## All possible breakpoints of the curves

A first normal omitting one of coordinates3,4 has constant sign on this
open segment, and its ReLU is affine in t on the entire closed segment.
The root34 term has one breakpoint, at s=1/2, with a nonzero derivative
jump. Reversing its orientation changes only an affine summand, since
ReLU(1-2t)=ReLU(2t-1)+1-2t. With the application's coefficient +1, its
jump is +2 in each core.

The sole exceptional row contributes ReLU(-t*a3-(1-t)*a4). It has an
interior breakpoint only if a3,a4 have opposite signs, at

    tau = -a4/(a3-a4).

If there is no such breakpoint, the only breakpoint in either core curve
is s. Otherwise the only possible breakpoints are s and tau. A zero
second-layer coefficient can remove the exceptional breakpoint from one
of the curves; this creates no additional case.

## Elementary two-curve lemma

Two continuous piecewise-affine functions f,k on [0,1], both zero at the
endpoints, cannot have all of the following properties:

* their zero sets cover (0,1);
* both have a nonzero slope jump at s in (0,1);
* their only possible additional common breakpoint tau lies strictly on
  one side of s.

Proof. Suppose tau<s, including the case of no additional breakpoint.
On (s,1), each function is affine and zero at1. If neither were identically
zero there, neither could vanish anywhere in (s,1), contradicting zero
coverage. Relabel so f is identically zero on (s,1).

The nonzero slope jump of f at s and continuity imply that f is nonzero
throughout a sufficiently short interval immediately to the left of s,
chosen to avoid tau. Hence k is identically zero on that interval. By
continuity k(s)=0, and its left slope is zero. Its nonzero slope jump makes
its right slope nonzero. Since k is affine all the way from s to1, this
contradicts k(1)=0. The case tau>s is the same argument with t replaced
by1-t. This proof uses no derivative beyond slopes of affine functions.

Apply the lemma to f(t)=g(q(t)) and k(t)=h(q(t)). The exceptional knot
must coincide with s=1/2. Equivalently a3+a4=0. It must actually cancel
the root breakpoint in at least one of the curves; the next calculation
makes this exact.

## Midpoint identities and coefficient signs

Let p=q3+q4. For any first row a define

    delta(a)=(|a3|+|a4|-|a3+a4|)/2 >= 0.

The scalar ReLU identity gives

    ReLU(a.p)-ReLU(a.q3)-ReLU(a.q4)=-delta(a).

Linear terms have zero defect. Consolidating the root34 contributions
and using its coefficient +1 in both cores gives

    g(p)=-1-sum_nonroot g_j*delta(a_j),
    h(p)=-1-sum_nonroot h_j*delta(a_j).

At least one of these values is exactly zero, by the same local MAX3
argument. In the one-exception case the balance conclusion gives
delta(a)=|a3|>0, so

    g_j=-1/|a3| or h_j=-1/|a3|.

In particular at least one exceptional-row coefficient is strictly
negative. In the no-exception case both midpoint values equal -1, an
immediate contradiction.

## Application to the six minimal-root same-label classes

The mandatory roots are02,12,34, with consolidated root34 coefficient+1
in both cores, as fixed by the unique quadruple-contact comparator germs.

* Classes275,307,353,355 have no nonroot row containing both3 and4.
  The midpoint calculation excludes them immediately.
* Class280 has exactly one such row, of exact support034. The segment
  lemma forces a3+a4=0; its zero coordinate sum then forces a0=0,
  contradicting exact support034. This excludes class280 analytically.
* Class277 has exactly one such row, of exact support0134 (physical row5).
  It is therefore necessary that

      a5_3+a5_4=0,     a5_0+a5_1=0.

  Thus its direction is b*(x0-x1)+c*(x3-x4), with b,c nonzero.
  At least one of g5,h5 equals -1/|c|. The segment argument alone does
  not exclude this balanced case.

These deductions concern the stated support classes and exact contact
pattern. They do not exclude the other support classes or all physical
networks of widths(9,4).

The independent support-predicate checker `check_midpoint_supports.py`
recounts the current frozen 387-class same-label cover: exactly 225 classes
have no nonroot row meeting both 3 and 4, and hence satisfy the midpoint
obstruction. Their physical-root counts are 4 classes with 3 roots,
47 with 4 roots, 107 with 5 roots, and 67 with 6 roots. The remaining 162
classes include the two minimal-root classes 277 and 280. Applying the
segment argument additionally excludes 280. The count does not reprove
the earlier cover's completeness; that remains a separate dependency.
