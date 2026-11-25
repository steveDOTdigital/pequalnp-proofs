# Three singleton-clean families with vertex cover six

Take six points and nine lines, one with three points and eight with two each. Require four-cycle-free incidence and at least $|S|+2$ distinct incident lines for every nonempty set $S$ of points. Attach any number of private leaves at any points, and optionally add isolated inputs. Every resulting graph has an optimal monotone circuit whose ANDs reject all singletons.

There are three core types. Fixing the triple to bits zero, one and two, representatives have the following nine line masks. The last columns are lower bounds on the high cofactor at any point of the core and at a newly attached single leaf, respectively.

| Line masks | Point high | New leaf high |
| --- | ---: | ---: |
| 7, 9, 10, 12, 17, 18, 33, 36, 48 | 18 | 20 |
| 7, 9, 10, 12, 17, 18, 36, 40, 48 | 19 | 20 |
| 7, 9, 10, 17, 20, 24, 34, 36, 40 | 19 | 20 |

Each core has 15 vertices, 19 edges and cover number six by Hall's theorem. Its star construction costs 24. Adding $t$ private leaves increases the number of vertices, the number of edges and the star budget by $t$. Repeated sibling leaves preserve cleanliness by OR substitution, so consider at most one per point.

For a high pin at a point, the leaf at that point gives one independent OR literal. Each other added leaf is essential in the high cofactor and can be set to zero for a further unit of cost. The other center remains available, and setting that center with its private leaf creates an edge while all neighbors of the pinned point can remain off. For a high pin on a new leaf, its center is an independent literal and the residual contains precisely the edges avoiding the center. The other $t-1$ added leaves again cost at least one gate apiece. The displayed lower bounds therefore rule out dirty points and dirty leaves in any extremal circuit smaller than $24+t$, by the [six-gate high-pin bound](singleton-high-pin.md).

Any remaining dirty singleton is a core line $x$. After deleting $x$, any omitted nonempty point set $S$ would require at least $|S|+1$ lines in a cover, by the expansion assumption. Consequently all six points constitute the unique cover of size six of the remaining core. A circuit beating the star has at most nine units of excess fanout. Its six cold point marks and the three hot shared wires exhaust all nine. There is a point of core degree at least four because the 19 incidences are distributed over six points. Its four required exits contradict the upper bound of three, exactly as in the [cover-five proof](singleton-high-pin.md). This leaves the unrestricted desk theorem open.

Run **python3 -B notes/six-point-singleton-cores.py** at the repository root. The [program](six-point-singleton-cores.py) enumerates every choice of eight allowed pairs, checks expansion for every point subset, identifies isomorphic copies and computes the table using the cover-five restriction bounds.
