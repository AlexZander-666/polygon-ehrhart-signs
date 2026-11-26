"""Exact finite kernel checks for the uniform sign theorem."""
from fractions import Fraction as Q
from math import factorial

g = []
for d in range(96):
    value = Q(5**d, factorial(d))
    for j in range(1, d//2 + 1):
        value -= Q(2**(2*j+1), factorial(2*j+2))*g[d-2*j]
    g.append(value)
    assert value and (value < 0) == (d >= 27 and d % 4 in (0, 3))
    if d >= 2:
        assert abs(g[d-2]) <= 108*abs(value)
    if d >= 27:
        assert abs(g[d-2]) <= 28*abs(value)
assert max(range(2, 96), key=lambda d: abs(g[d-2]/g[d])) == 24
assert 10**14*Q(2,3)**94 < 1
assert 10*Q(2*95+1, 2*95-1) < 12
assert Q(10)*(10*Q(22,7)+1)/(30-1) < 12
assert Q(5,12)*Q(35,129)/(1-Q(135,192)) < Q(2,5)
assert 10*Q(25,65)**65 < Q(1,32)
print("degree\tg_d\tabs(previous_same_parity/g_d)")
for d, value in enumerate(g):
    print(d, value, abs(g[d-2]/value) if d >= 2 else "-", sep="\t")
