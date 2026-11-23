"""Exact unrestricted cost of the six-cycle and two opposite-pair disjunctions."""

import argparse
from pathlib import Path
from runpy import run_path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("solver")
    parser.add_argument("--seconds", type=int, default=180)
    args = parser.parse_args()
    search = run_path(str(Path(__file__).with_name("search-three-matchings.py")))
    x = search["INPUTS"]
    cycle = 0
    for i in range(6):
        cycle |= x[i] & x[(i + 1) % 6]

    # Three two-edge stars at even centers use six gates. Two ORs
    # finish the cycle, and two more compute the auxiliary outputs.
    stars = [x[i] & (x[(i - 1) % 6] | x[(i + 1) % 6]) for i in (0, 2, 4)]
    assert (stars[0] | stars[1] | stars[2]) == cycle
    outputs = [cycle, x[0] | x[3], x[1] | x[4]]
    result = search["synthesize"](args.solver, 0, 9, args.seconds, check=True,
                                  six_input_outputs=outputs)
    if result != "UNSAT":
        raise SystemExit("Nine-gate exclusion was inconclusive: " + result)
    print("Ten gates are necessary and sufficient for the three outputs.")


if __name__ == "__main__":
    main()
