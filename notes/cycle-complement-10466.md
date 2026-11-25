# A single NOT on the complement of the seven-cycle

For desk case L-meta-10466, a 14-gate monotone circuit computes the graph edge function. An exhaustive finite search excludes every implementation with at most twelve binary AND/OR gates and one additional NOT. Thus a circuit containing a NOT costs at least 14 gates. A circuit without a NOT already gives its own monotone replacement.

[Reproducible search](cycle-complement-10466.cpp) · [Lean construction and transfer to the project evaluator](CycleComplement10466.lean)

The C++ enumeration supplies the lower bound. The Lean file checks the 14-gate upper bound on all 128 inputs and the conditional implication from the finite exclusion to replacement. The lower-bound search still needs a Lean certificate for an upstream proof submission.

## Finite search

A wire is its 128-bit truth column. Trim gates outside the output cone, remove constants and copies, and replace a duplicate column by its earlier occurrence. A malformed reference reads false. An AND or OR on fewer than two arguments is constant or a copy, and a NOT with arguments reads only the first. Every raw variable is essential because it belongs to a graph edge.

The pool contains the live signals crossing the current gate position. For each binary gate the search picks two different live signals, appends their AND or OR and tries each possibility for retaining their operands. A NOT may occur once, on any live signal. It may retain or discard the old signal and consumes no binary budget. Replacing a later NOT output by an already available identical column requires no extra gate. The algorithm tests for the goal before pruning, including a final NOT. With $k$ binary gates left, a cone can consume at most $k+1$ live signals. Two inputs indistinguishable on the pool must get the same answer. After the NOT is spent, a positive row must have some live signal high where each negative row is low, since every subsequent gate is monotone. Rotations and reflections of the cycle preserve the target.

## Restriction bounds

Thirteen representative restrictions identify or complement inputs, or set them to constants. For each representative the program independently enumerates smaller signed binary circuits on four to six inputs. Wire inversions are free in this subsidiary search. Store each word in the orientation that is zero on the all-zero assignment. Up to an output complement, the four possible binary combinations are $a\land b$, $a\lor b$, $a\land\neg b$ and $\neg a\land b$. Input permutations are used only when they preserve the truth column. The thirteen verified bounds yield 98 distinct restrictions under the cycle's symmetries.

For a restriction let $b$ be its signed lower bound and $z$ the number of live source wires becoming constant. If all other projected sources can be supplied by raw inputs and $h$ distinct one-gate signals up to sign, any continuation with $k$ binary gates yields a signed implementation costing at most $h+k-z$. To count the deletions, follow only wires produced entirely from constant sources. A connected component containing $t$ sources needs at least $t-1$ internal binary gates to join them. Since the restricted output is nonconstant and all sources are live in the original cone, each component reaches a further binary gate with one constant operand. This gate simplifies, and different components cannot charge the same such gate. Unary inversions cost nothing and cannot join two components. Summing gives at least $z$ binary deletions. The program prunes only if $h+k-z<b$.

The signed seven-input search excluded eleven binary gates in 111 expanded frontiers. The one-NOT search excluded twelve binary gates in 34,324 expanded frontiers, testing 8,123,391 candidate pools. A positive control needs all seven inputs and uses a NOT followed by six binary gates. The standalone verifier finds this control before running the full search.

From the proof repository, run the following with a C++17 compiler supporting 128-bit integers.

```sh
python3 - <<'PY'
from pathlib import Path
import subprocess
import tempfile

with tempfile.TemporaryDirectory() as directory:
    binary = Path(directory) / "check"
    subprocess.run(["c++", "-std=c++17", "-O3",
                    "notes/cycle-complement-10466.cpp", "-o", binary], check=True)
    subprocess.run([binary], check=True)
PY
```
