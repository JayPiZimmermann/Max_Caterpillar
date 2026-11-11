# Primary-source audit of two cited upper bounds

Neither cited deposit supplies a polynomial second-hidden-layer width for
**exact** MAX while keeping the first hidden layer O(N^2). Both original
PDFs were downloaded and inspected, including the theorem statements and
width-counting sections. This is a scope/formula audit, not an independent
verification of all their proofs. No author was contacted and no repository
source was edited.

## Tallavarjula and Rastegar: exact, factorial-sized second layer

Primary deposit: [Two Hidden Layers Suffice for Exact ReLU Representation,
DOI 10.5281/zenodo.23377648](https://zenodo.org/records/23377648), deposited
14 October 2026, metadata version v1.0.1-preprint. The PDF is
`two_hidden_layers_JMLR_SUBMIT_READY_manuscript.pdf`. A submission-ready
filename is not evidence of journal acceptance.

Theorem 2, PDF p.2, states for every n>=2 a standard scalar-output,
two-hidden-layer network computing max(X_1,...,X_n) on **all real inputs**:

\[
W_1(n)\le\binom n2+n+1,\qquad
W_2(n)\le2+\sum_{r=1}^{n-1}(r-1)!(4^r-3^r).
\]

All biases are zero, first-hidden-layer weights lie in {-1,0,1}, second
hidden weights are integers of absolute value at most n, and a common
output denominator divides (n-1)!. The standard model has no bypass
connections. Section 6 explicitly reconstructs reverse comparison
functions from the retained first layer, passes the baseline through two
channels, and counts the unmerged level-r units as

\[
A_r=(r-1)!(4^r-3^r).
\]

The displayed second-width construction is exp(O(n log n)), not a
polynomial guarantee. The paper says this explicitly after Theorem 3 and
again following Eq. (6.7), PDF pp.3 and10. Table 1 gives second-width bounds
10, 84, 1,134, 19,878 for n=3,4,5,6 and
663,425,974,306,638 for n=13. These are construction bounds, not lower
bounds or optimality claims. Nothing in these statements supplies an exact
polynomial-width replacement for the repository's all-arity upper bound.

## Lu: polynomial common width, but in approximation closure

Primary deposit: [Sharp Closure Thresholds for Two-Hidden-Layer ReLU
Networks, DOI 10.5281/zenodo.22728502](https://zenodo.org/records/22728502),
v1, September 2026. The
[author's primary publication page](https://shunqilu.github.io/publications/sharp-closure-thresholds.html)
also describes the scope. The deposit explicitly identifies itself as a
preprint that has not been peer reviewed.

Write

\[
\kappa_d=\binom d2-\lfloor d^2/4\rfloor.
\]

There are two upper constructions, which must not be conflated:

* At the **critical first width** kappa_d, Theorem 2.6 and Corollary 2.10
  give a fixed architecture with a parameter sequence converging to MAX
  on [0,1]^d in every finite L^p. The explicit second width, Eq. (2.29), is

  \[
  M_d=\left\lceil16\lceil d/2\rceil!\lfloor d/2\rfloor!
           (3/2)^{d-2}\right\rceil
       =\exp(O(d\log d)).
  \]

  The matching first-width threshold is analytic for d>=40 and uses the
  stored finite tournament inputs for 14<=d<40. For d=14 the introduction
  reports widths (42,16,355,852,100).
* Theorem 2.12 gives the **common closure width** for every d>=5:

  \[
  \max\{d,\kappa_d\}\le r_{\rm cl}(d)\le w_{\rm cl}(d)
       \le\kappa_d+d-1.
  \]

  Here w_cl bounds both hidden widths, so this does give O(d^2) widths
  in both layers for arbitrarily accurate L^2 approximation, with
  unrestricted parameters that may diverge along the sequence. It is an
  approximation result, rather than an exact finite-parameter MAX network.

Theorem 2.13 separately states an exact first-width **lower** bound

\[
r_{\rm ex}(d)\ge\binom d2-\lfloor4d/3\rfloor,
\]

and explicitly says general exact realizability is not established there.
At the critical width the zero error infimum is unattained. Thus the
polynomial common-width closure theorem cannot be presented as an exact
polynomial second-width upper bound.

## Safran 2601.01417: exact lower bound, different resource

Primary paper: [A Depth Hierarchy for Computing the Maximum in ReLU
Networks via Extremal Graph Theory](https://arxiv.org/abs/2601.01417),
arXiv v1, 4 January 2026. Its main Theorem 1.1 concerns **exact equality**
on [0,1]^d, not approximation. If depth k counts hidden layers plus the
affine output and 3<=k<=log_2(log_2 d), it states

\[
\operatorname{width}(N)\ge0.1\,
 d^{\,1+1/(2^{k-2}-1)}.
\]

The definition on PDF p.4 makes width the **largest hidden-layer width**.
For two hidden layers k=3, this is a quadratic max(h1,h2) bound in the
stated dimension range. It does not separately force h2 to be quadratic
when h1 already is quadratic. The introduction compares this exact lower
bound with earlier L^2 approximation upper bounds of Safran, Reichman,
and Valiant; those comparisons do not turn the upper bounds into exact
networks. Some January-2026 open-problem remarks are chronologically
superseded by later constructions and should not be quoted as current
nonexistence claims.

## Safe conclusion

The audited sources preserve an exact-width gap: their displayed exact
all-arity construction has O(N^2) first width and exp(O(N log N)) second
width. They do not supply the queried exact polynomial second layer.
This audit does not establish that no other source gives a better upper
bound, nor that the displayed construction cannot be compressed further.
The repository's 2^{O(N log N)} construction can safely be described as an
available upper bound, without calling it the globally best known bound.

The local research cache retains the PDFs, extracted text, deposit metadata
and checksum records. Those downloaded papers are not included in this proof
publication; the primary links above identify the sources. The public Zenodo
APIs and file downloads were accessible through urllib.
