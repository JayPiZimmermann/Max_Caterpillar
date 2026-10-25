# Support audit of the actual ordered lifts

The fixed canonical-gauge ordered simplex lifts already require more than
two pages in their surviving geometric forest inventory. At six labels,
the cube with head $(3,-1,0,-2,0,0)$, generators corresponding to
$02,03,14,25$, and coefficient $-3$ survives the top-rank and height tests.
The three edges $03,14,25$ cross pairwise, so three pages are necessary.

At seven labels the surviving support contains 41,774 pyramids,
5,439 distinct forests and 536 heads. Of those forests, 931 are
noncrossing, 4,081 require two pages and 427 require three.
The maximum positive head mass is 11.

`overnight_upper_actual_support.py` constructs the actual lifts through
simplex dimension six, verifies each cubical boundary, and computes the
crossing graph's chromatic number exactly. It does not extend raw powers.
The successful bounded run took 8.9 seconds.

This refutes a two-page support shortcut for the **current gauge**.
It does not exclude another gauge, another geometric decomposition, or
the existence of a uniform exponential construction.
