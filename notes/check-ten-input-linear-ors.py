"""Reproduce the ten-input exclusions for L-meta-955. Pass a CaDiCaL executable."""
from pathlib import Path
from runpy import run_path
import sys

checker = run_path(str(Path(__file__).with_name("check-nine-input-linear-ors.py")))
solver = sys.argv[1] if len(sys.argv) > 1 else "cadical"
cases = [core for core in checker["surviving_cores"](10) if not checker["connectivity_excludes"](core)]
assert len(cases) == 317
excluded_by_count = 0
excluded_by_sat = 0
for core in cases:
    excess = sum(row.bit_count() - 3 for row in core)
    double_points = sum(sum(row >> x & 1 for row in core) == 2 for x in range(10))
    # Apply the ten-point deletion argument only to the explicitly checked
    # five-star case. The nine-input theorem covers the smaller restrictions.
    if len(core) == 5 and all(row.bit_count() == 4 for row in core) and double_points == 10:
        assert double_points > len(core) + excess - 2
        excluded_by_count += 1
    else:
        formula = checker["encode"](core, 10, excess - 2)
        assert not checker["solve"](solver, formula), core
        excluded_by_sat += 1
print(f"{excluded_by_count} excluded by counting, {excluded_by_sat} excluded by checked SAT")
assert (excluded_by_count, excluded_by_sat) == (1, 316)
