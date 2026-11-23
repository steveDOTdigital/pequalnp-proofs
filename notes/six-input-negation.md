# One NOT gate saves a gate on six inputs

The circuit has six inputs and fifteen monotone outputs. A circuit with one NOT gate computes them using seventeen gates. Every AND/OR circuit computing the same outputs needs at least eighteen, and an eighteen-gate circuit attains the bound. This refutes L-meta-1035, which asserts the opposite for every family on at most seven inputs. [Lean proof](SixInputNegation.lean)

## Construction

Write the inputs as a control bit `x` and five data bits `z₁,…,z₅`. Let `Zᵢ = z₁ ∧ ⋯ ∧ zᵢ`. Require the following fourteen auxiliary functions as outputs, alongside the fifteenth output `F = Z₅`.

| Outputs | Range | Gates |
| --- | --- | ---: |
| `Aᵢ = x ∧ Zᵢ` | 1 through 5 | 5 |
| `Bᵢ = x ∨ zᵢ` | 1 through 5 | 5 |
| `Cᵢ = B₁ ∧ ⋯ ∧ Bᵢ` | 2 through 5 | 4 |

Compute the A and C outputs by extending each prefix with one AND gate. When `x = 0`, `C₅ = F`. When `x = 1`, `A₅ = F`. Three additional gates compute `A₅ ∨ (¬x ∧ C₅)`. For an eighteen-gate AND/OR circuit, use four additional AND gates to compute `F` directly from the data bits.

## Why any monotone circuit needs eighteen gates

Let `P` be the input with control zero and every data bit one. For each data bit `i`, let `Nᵢ` have control one and every data bit one except bit `i`. Say a signal separates `i` if its value is one on `P` and zero on `Nᵢ`. Raw data bit `i` separates exactly its own index. The control bit separates none.

Each A output is zero on `P`. Each B and C output is one on every `Nᵢ`. Thus the fourteen auxiliary outputs separate nothing. They are distinct functions, each different from the input wires and the default false wire, so each needs its own gate.

For an AND or OR gate to separate an index, some parent must separate it. Trace the final output backwards through the circuit in reverse gate order, stopping at raw inputs or an auxiliary output. Start with one wire. Expanding a gate adds at most one wire to the frontier because it has at most two inputs. Count a shared wire once. The final output separates all five indices, so the frontier must reach all five raw data wires. At least four gates in addition to the fourteen auxiliary gates are necessary. The formal invariant in `advance` counts the union of indices separated by any set of wires and accommodates repeated inputs, constants and out-of-range wires.

The same argument works with any number `k ≥ 2` of data bits. There are `3k − 1` distinct auxiliary outputs. The one-NOT construction uses `3k + 2` gates, and the exact AND/OR minimum is `4k − 2`. The linked Lean file specializes this construction and both bounds to five data bits. Its final declaration proves the negation of the desk's exact posted statement.
