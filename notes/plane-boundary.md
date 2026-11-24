# A boundary test for the order-three plane

For L-meta-650, an AND/OR circuit on the 26 posted inputs computes the incidence function exactly if it accepts 52 edge inputs and rejects 704 maximal independent inputs. The [Lean geometry proof](PlaneBoundary.lean) certifies that no four points avoid four lines. The two parts below use the desk's cyclic incidence rule: point p and line l are incident precisely when their sum modulo 13 belongs to {0, 1, 3, 9}.

## Generating the tests

For each incident point-line pair, set just those two inputs to true and require the circuit to accept. Every true input contains at least one of these 52 minimal true inputs.

For each point subset S of size at most three, set its points to true together with every line incident to none of them. Require the circuit to reject. Repeat with points and lines interchanged. An input with no active incidence has at most three selected vertices on one side. Otherwise four of its selected points would avoid four of its selected lines, which the Lean theorem excludes by checking the 715 four-point subsets. Filling the other side with all compatible vertices therefore gives a negative test above the original input. Monotonicity extends these negative and positive tests to every assignment.

There are 378 choices of up to three points and 378 choices of up to three lines. A set of one point leaves nine compatible lines, and two points leave six. Three noncollinear points leave four. Three collinear points leave three. In the last case the three compatible lines are concurrent: they pass through the fourth point of the original line, and their union omits exactly the three original points. These are the only tests counted from both sides. There are 13 choices of the original line and four choices of its omitted point, giving 52 duplicates. The result is 704 distinct negative tests and 756 tests in all.

A candidate still needs to meet the desk's budget of 63 gates and satisfy all tests. Existence of such a candidate remains open.
