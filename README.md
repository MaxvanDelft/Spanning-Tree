# Computation of the partition matrix

Andre\'e came up with a nifty algorithm to compute the partition matrix.  First we separate the letter into elementary letters. These letters look very much like the identity letter: = (the letter with all horizontal edges). The only difference is they have one extra vertical edge or one missing horizontal edge. The ones with an extra vertical edge we call vertical elementary letters, and with a missing horizontal edge we call horizontal elementary letters. For these elementary letters it is easy to check whether the letter can be added to a start partition and to compute the end partition is easy too, because they look so much like the identity. We will exploit this further.

For all these elementary letters there is a transition matrix from partition to partition. We computed them, but instead of filling them with ones and zero's we filled them with the vertical/horizontal index that was added/removed or the empty set if the letter did not cause that transition. Each vertical elementary letter vi is in this way associated to a matrix Vi and each horizontal edge hi is associated to a matrix Hi.

The multiplication of Vi and Vj for any i,j yields a matrix with all possible transition caused by the identity letter, but where both vertical edges i and j are also present. The same holds for horizontal elementary letters.

Let the identity matrix I be the matrix with the empty string on the diagonal and the empty set elsewhere.

Vi + I is the matrix where either vertical edge i is added or not.
Hi + I is the matrix where either horizontal edge i is removed or not.

Let
* Wi = Vi + I,
* Gi = Hi + I

Now according to Dijkstra's method: The multiplication of two of these matrices gives all paths of 2 letters. We must define the right multiplication operator: S1\*S2 = set of all (s1\*s2) for all s1 in S1, s2 in S2.

The addition corresponds to the set union.

Let W = prod_{i=1}^{m-1} Wi and G = prod_{i=1}^{m} Gi. Then E = WG is the partition matrix for E-letters (The E-letters are encoded by which vertical edges were added and which horizontal edges were removed). Also F=GW is the partition matrix for 3-letters.
