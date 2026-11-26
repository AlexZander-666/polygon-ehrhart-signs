"""Compare the finite Lean evidence to a second enumeration of all coefficient numerators."""
from importlib.util import spec_from_file_location, module_from_spec
from pathlib import Path
import re

root = Path(__file__).resolve().parent
spec = spec_from_file_location("published", root / "research/polygon/codimension/check.py")
published = module_from_spec(spec)
spec.loader.exec_module(published)
checked = 0
negative = 0
for n in range(3,65):
    leaf = root / f"formal/Polygon/Finite64/N{n:02}.lean"
    match = re.search(r'def numerators : List ℤ := \[([^\]]+)\]',leaf.read_text())
    assert match is not None, leaf
    row = [int(c) for c in match.group(1).split(",")]
    assert row == published.coefficients_from_published(n), n
    for r,c in enumerate(row):
        d=2*n+2-r
        assert c!=0 and (c<0)==(r>0 and d>=27 and d%4 in (0,3)), (n,r)
        negative+=c<0
    checked+=len(row)
assert (checked,negative)==(4340,1378)
print(f"PASS 62 rows, {checked} exact integer numerators, {negative} negative.")
