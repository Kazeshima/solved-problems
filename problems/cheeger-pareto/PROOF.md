# An exact certificate for the floor-corrected conjecture

Let $k=\lfloor |V|/2\rfloor$. An admissible set has at most $k$ vertices. Write $c(S)$ for its number of crossing edges and $x(S)=\sum_{v\in S}x_v$. The question asks whether every coordinatewise maximal nonnegative real vector satisfying $x(S)\le c(S)$ on all admissible sets has $x(V)\ge k h(G)$. Here $h(G)$ is the least ratio $c(S)/|S|$ over nonempty admissible sets. [Original question](https://math.stackexchange.com/questions/5118288)

## The finite calculation

Decode [graph6.txt](graph6.txt) in upper-triangular column order on vertices 0 through 9. The resulting 18 edges are

~~~text
07 08 09   12 13 14 18 19   23 39   45 46 48 49   56 59   78 79
~~~

Each two-digit entry lists its endpoints. The triangles on $\{0,7,8\}$, $\{1,2,3\}$, and $\{4,5,6\}$ each contain two neighbors of vertex 9, so the graph is connected.

| Size | Number of sets | Least boundary | Least boundary among sets containing 9 |
|---:|---:|---:|---:|
| 0 | 1 | 0 | — |
| 1 | 10 | 2 | 6 |
| 2 | 45 | 3 | 7 |
| 3 | 120 | 4 | 6 |
| 4 | 210 | 6 | 6 |
| 5 | 252 | 7 | 7 |

The table uses all 638 admissible labeled sets. For a reproducible calculation, range over integers $0\le m<2^{10}$ with at most five set bits. Count one edge when exactly one endpoint bit is set. Minimize by bit count, both with and without the restriction that bit 9 is set. A second count adds the numbers of outside neighbors of the selected vertices. The exact minimum ratio is $4/3$, attained on each of the three triangles above. [All labeled cuts](evidence/cuts.tsv) · [Verifier](verify.py)

## Real Pareto maximality and the attained minimum

Put $x=6e_9$. The last column proves feasibility for every set containing 9. Every other set has $x(S)=0$. Adjoining 9 to each of the three triangles gives three four-vertex sets, each with $x(S)=c(S)=6$. They cover $V$.

If a feasible real $y$ dominates $x$, the nonnegative differences $y_v-x_v$ sum to at most zero on each of those tight sets. Every difference vanishes. This proves Pareto maximality over the full real polytope.

If a feasible $z$ has total mass below 6, increase $z_9$ by $6-z(V)$. Every set containing 9 now has mass at most 6, and the sums on the other sets stay feasible. Thus every efficient vector has total mass at least 6. The minimum is attained at $x$, giving

$$
\rho(G)=6<\frac{20}{3}=5h(G).
$$

The [paper](output/pdf/paper.pdf) proves the same bounds directly from the triangle structure. The discovery program in the submitted archive used floating-point optimization to look for graphs. The calculation above and the [Lean proof](CheegerPareto.lean) use exact arithmetic.
