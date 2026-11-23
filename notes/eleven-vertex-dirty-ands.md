# AND gates in range 19 of the eleven-vertex graph search

L-meta-1343 asks for a 22-gate lower bound for an eleven-vertex edge function. Range 19 concerns circuits with at least two AND gates true on independent sets, including one true on exactly the input set {0,1,3,5}. Call those AND gates dirty. For this range, **at least six AND gates are necessary, even with arbitrarily many OR gates**. If there are exactly six AND gates, at least three are dirty. The total-gate lower bound remains open.

## Removing the OR budget

An AND gate with fewer than two operands can be padded by the constant true. With OR gates free, either operand of an AND is a disjunction of raw inputs, constants and earlier AND gates. Every independent input extends to a maximal independent set. A monotone signal is therefore dirty exactly when it is true on one of the 24 maximal independent inputs. A circuit computes the graph function if it is false on those inputs and true on the 16 two-vertex edges. A raw input cannot be a direct term of the final disjunction, since its singleton is independent.

Replace every reference to a clean AND gate in a later operand by false. As a new output take the OR of all the resulting clean gates. On every negative boundary input this preserves all gate values by induction, so exactly the original dirty gates remain dirty, including the one true on the designated input. At each positive edge at least one original clean gate was true: the original output disjunction had to be true, and could only include clean AND gates. Take the first original clean gate true there. Removing references to earlier clean gates does not change its value at that edge, since all were already false. This proves the new output is correct.

The dirty gates can now be placed first, followed by clean terminal AND gates. Each nonzero terminal has two nonempty disjunctions without common sources. A common raw input or a common dirty gate would make it true on some independent input. A constant-true operand would leave the other operand as the whole terminal; any nonempty disjunction of raw inputs or dirty gates is unsound. Every raw cross-pair from the two operands must form an edge, since a nonedge is contained in a maximal independent set. A terminal that is identically false may be replaced by a duplicate of a useful terminal. This also pads a smaller representation to the tested number of AND gates.

## Checked cases

The [checker](check-eleven-vertex-dirty-ands.py) selects both operands of every AND and checks the boundary inputs. Earlier dirty gates may appear in later operands, including those of other dirty gates. The program demands a negative witness for each dirty gate, including the specified anchor for at least one, and orders only interchangeable operands and terminals. CaDiCaL ran with internal proof checking enabled.

| Total AND gates | Dirty AND gates | Result |
| ---: | ---: | --- |
| 5 | 2 | UNSAT |
| 5 | 3 | UNSAT |
| 5 | 4 | UNSAT |
| 6 | 2 | UNSAT |
| 9 | 2 | SAT, fixed positive control |

At least one useful terminal is required. Padding only with clean terminals covers circuits with fewer than five AND gates. The positive control uses seven vertex-cover stars and the two dirty signals given by pairs {0,1} and {3,5}. Its edge function was checked on all 2,048 inputs. Run `python3.11 notes/check-eleven-vertex-dirty-ands.py /path/to/cadical` on the research branch.

The AND-gate search does not bound the number of OR gates. A separate exact search tests the assigned 21-total-gate question.

## Seven AND gates suffice with exactly two dirty gates

Write xᵢ for input i. Compute the following two intermediate functions.

- D = (x₇ ∨ x₁₀) ∧ (x₆ ∨ x₉).
- H = (x₁ ∨ x₄ ∨ x₉) ∧ (x₀ ∨ x₈).

Take the OR of these five terms.

1. x₁₀ ∧ x₀
2. (x₈ ∨ x₉) ∧ (x₅ ∨ H)
3. (x₆ ∨ x₇) ∧ (x₃ ∨ D)
4. (x₅ ∨ x₁₀) ∧ x₂
5. x₄ ∧ (x₁ ∨ x₁₀)

The binary circuit uses seven AND gates and fifteen OR gates. Every gate reaches the output. H is true when exactly inputs {0,1,3,5} are on. D is true on the independent input {9,10}. The five terminal AND gates are each false on every independent input. The checker evaluates all 2,048 inputs, verifies the edge function and identifies the two dirty gates. Together with the six-AND exclusion, this gives an exact minimum of seven AND gates for the specified range with exactly two dirty gates. The total-size search asks whether any circuit in the range can save one more gate.
