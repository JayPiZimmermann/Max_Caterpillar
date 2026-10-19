# Building the paper

`main.tex` is the short article on the caterpillar construction for
$\operatorname{MAX}_N$. Its introduction may cite general representation
theorems for context, and the conclusion cites width lower bounds from the
literature. These background results are not formalized here. The Lean links and checked claims in this repository
concern only the maximum construction and the mathematical steps used in the
paper.

The document uses the ICLR 2027 style from the arXiv v2 source of
[2610.01728](https://arxiv.org/abs/2610.01728), together with its Lean-reference
commands and structured proof commands. Build it with:

```sh
python3 scripts/paper_links.py
cd paper
tectonic -k --keep-logs main.tex
```

Alternatively, use `latexmk -pdf main.tex` with a current TeX installation.
The bibliography is embedded, and no shell escape is required.

Source paths and line numbers are resolved from declaration names in
`lean-map.json`. The generator updates `main.tex`, `lean-links.tex`, and
`lean-links.json`. Remote links use the repository's `main` branch.

Every displayed formula uses a numbered `align` environment. Equation numbers
link to the Lean proof, except the Wang--Sun background theorem, whose equations
link to its published source because its proof is not included here.
Multiline calculations use `aligned` or
`split` under one number, or give each row its own label. Lean links occur in
theorem, lemma, definition, proof, or paragraph headings rather than running
prose. Every proof uses the labelled `Proof` environment and ends with one QED
square.

The proof has three geometric stages: correction by support functions of
exposed caterpillar faces, reconstruction from facet differences, and the
arity induction proving the caterpillar class identity. The size section then
normalizes and counts the face descriptions before compiling them into a
network with widths

$$
\binom N2+N+1
\quad\text{and}\quad
3^{N-2}C_N-N(N-1)+2.
$$

The definitions of the network, maximum, and widths are in
`MaxCaterpillar/Definitions.lean`; the paper-facing proof steps are in
`MaxCaterpillar/Lemmas.lean`; and the main width and asymptotic statements are
in `MaxCaterpillar/Theorems.lean` and `MaxCaterpillar/Asymptotics.lean`.
