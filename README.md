# planar-build #

Generate all the cubic planar graphs with one triangle, two squares, five pentagons,
and arbitrarily many hexagons. There are infinitely many, so this cuts off at
MAX_FACES.

The same approach should work with other constraints on the
number of faces of each size. Just changing the macros N_TRI, N_SQ,
and N_PENT may suffice. Bear in mind that 3\*N_TRI + 2\*N_SQ + N_PENT
must be 12, or there will be no solutions!

The code does a kind of depth-first search with backtracking. It starts with
an adjacent triangle and hexagon (with one triangle, two squares, and five pentagons,
it is impossible for the triangle to be totally surrounded by squares and pentagons.)
One of the "open" outer faces is chosen, and edges and vertices are added to close it.
We keep going with a new outer face, until achieving success or a graph which can't
close up, then backtrack.

It would be trivial to convert to a breadth-first search, which might be advantageous
since all the results with *n* faces would be reported before continuing on to *n*+1
faces.

[Nauty](http://users.cecs.anu.edu.au/~bdm/nauty/) is used to remove isomorphic graphs.
You will need to download and build nauty, and symlink or place the headers
nauty.h, nausparse.h, and gtools.h in this directory
(or otherwise arrange that #include will find them.)
Link with the object archive nauty.a.

Currently, the output lists the sizes of the faces adjacent to the unique triangle
and each of the two squares. This is really not very informative, and after you get
up to a few thousand graphs, extremely repetitive (many different graphs have the same
description).
The program `planar-fast.cc` instead just reports the number of graphs
with a given number of hexagons.

You can build like so:

    g++ -std=gnu++14 -Wall -Wextra -O2 -march=native -DMAX_FACES=30 planar.cc nauty.a -o planar

To make it more verbose, add `-DINFO_LVL=1` or 2 or 3.  
To skip assertions (making it faster), add `-DNDEBUG`.  
To build for debugging:

    g++ -std=gnu++14 -Wall -Wextra -ggdb -DINFO_LVL=3 -DFLUSH planar.cc nauty.a -o planar-db

To build planar-fast:

     g++ -std=gnu++14 -Wall -Wextra -O2 -march=native -DMAX_FACES=34 planar-fast.cc nauty.a -o planar-fast
