# Spanning-Tree
Generate spanning trees on grid graphs

# Introduction
We intend to prove/disprove whether we can uniformly generate spanning trees on \infty \times m grid graphs by socalled Subshifts of Finite Type (SFT). The idea is to split a spanning tree into 1 \times m boxes, the graphs inside the boxes we will call 'letters' in the alphabet of all subgraphs of the 1 \times m box. They are not necessarily spanning forests, for instance we could take the letter to be one single horizontal edge, when we would have to make a spanning tree on both sides of the lattice. 

Not all subgraphs are letters. For example, every letter contains at least one horizontal edge
To each box (or letter) we associate a unique set of points (vertices), namely the ones on the left hand side of the box. We allow vertical edges to only occur on the left hand side of the box, so that concatenation of letters doesn't lead to multi-edges.
Not all letters can follow eachother. Loops are not allowed and, for example, suppose we have a vertex in a certain box that is not connected to any other vertex. Then in the box to the left hand side the unique horizontal edge toward that vertex must be contained. 
This way we want to generate a spanning tree. We might hope to connect the letters through some Markov Chain. But the problem is more difficult, since a spanning tree does not contain loops. In a sequence of letters that are allowed to follow eachother piecewise, it might not result in a spanning tree because a loop might be created over a longer distance. For this we need extra information of each box. It turns out that knowledge of the route at which two vertices are connected is enough. We add an extra symbol in {+,-}, where + indicates the whole path connecting two vertices lies to the left of the box, and - indicates otherwise. This is done for every pair of vertices on the left vertical line of points associated to the box. There are 1/2m(m-1) of these, and another 2m-1 {0,1}-values indicate whether an edge is present or not.

There are two well-known ways to randomly generate a spanning tree

* Wilson's Algorithm
* Aldous Broder Algorithm

More info: http://www.maths.bath.ac.uk/~aj276/teaching/USF/USFnotes.pdf
