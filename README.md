
My father came up with a nifty algorithm to compute the partition matrix.  First we separate the letter into elementary letters. These letters look very much like the identity letter: = (the letter with all horizontal edges). The only difference is they have one extra vertical edge or one missing horizontal edge. The ones with an extra vertical edge we call vertical elementary letters, and with a missing horizontal edge we call horizontal elementary letters. For these elementary letters it is easy to check whether the letter can be added to a start partition and to compute the end partition is easy too, because they look so much like the identity. We will exploit this further.

For all these elementary letters there is a transition matrix from partition to partition. We computed them, but instead of filling them with ones and zero's we filled them with the vertical/horizontal index that was added/removed or the empty set if the letter did not cause that transition. Each vertical elementary letter v_i is in this way associated to a matrix V_i and each horizontal edge h_i is associated to a matrix H_i.

The multiplication of V_i and V_j for any i,j yields a matrix with all possible transition caused by the identity letter, but where both vertical edges i and j are also present.
The multiplication of H_i and H_j for any i,j yields a matrix with all possible transition caused by the identity letter, except that both horizontal edges i and j are absent.

Let the identity matrix I be the matrix with the empty string on the diagonal and the empty set elsewhere.

V_i + I is the matrix where either vertical edge i is added or not.
H_i + I is the matrix where either horizontal edge i is removed or not.

Let
*W_i = V_i + I,
*G_i = H_i + I

Now according to Dijkstra's method: The multiplication of two of these matrices gives all paths of 2 letters. We must define the right multiplication operator: S_1*S_2 = set of all (s_1*s_2) for all s_1 in S_1, s_2 in S_2.

The addition corresponds to the set union.

Let W = prod_{i=1}^m W_i$ and G = prod_{i=1}^{m+1} G_i. Then E = WG is the partition matrix for E-letters (The E-letters are encoded by which vertical edges were added and which horizontal edges where removed). Also F=GW is the partition matrix for 3-letters.
