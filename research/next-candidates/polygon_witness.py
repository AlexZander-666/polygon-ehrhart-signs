"""Check a convex polygon face-poset witness by two independent counting identities."""
import argparse
from fractions import Fraction
from itertools import accumulate
from math import comb
import json


def trace_counts(n, m):
    """Sum over the colors of a cyclic list of vertices; count each intervening edge."""
    total = 0
    for start in range(m):
        v = [int(j == start) for j in range(m)]
        for _ in range(n):
            prefix = list(accumulate(v))
            suffix = 0
            for j in reversed(range(m)):
                weighted = (m-j) * v[j]
                v[j] = (m-j)*prefix[j] + suffix
                suffix += weighted
        total += v[start]
    return total


def zigzags(n, m):
    """Counts for paths on 1,3,...,2n-1 vertices, starting at a minimal vertex."""
    v = [1]*m
    counts = [sum(v)]
    for _ in range(1, n):
        v = list(accumulate(v))
        v = list(reversed(list(accumulate(reversed(v)))))
        counts.append(sum(v))
    return counts


def via_published_recurrence(n, bound):
    """Equation (4.1) of Lundström–Saud Maia Leite v5."""
    crown = [0]
    previous = zigzags(n, 0)
    for m in range(1, bound+1):
        current = zigzags(n, m)
        increment = n*previous[n-1] + current[n-2]
        increment += sum((n-d)*previous[n-d-1]*current[d-1] for d in range(1, n))
        crown.append(crown[-1] + increment)
        previous = current
    return crown


def verify(n):
    degree = 2*n + 2
    bound = degree + 2
    trace = [0] + [trace_counts(n, m) for m in range(1, bound+1)]
    zigzag = via_published_recurrence(n, bound)
    assert trace == zigzag
    # Independently sum over (bottom,top), and over the length of their interval.
    values = [sum(trace[hi-lo+1] for lo in range(q+1) for hi in range(lo, q+1))
              for q in range(degree+2)]
    assert values == [sum((q+2-m)*zigzag[m] for m in range(1, q+2))
                      for q in range(degree+2)]
    assert values[0] == 1
    diffs = values[:]
    newton = []
    for _ in range(degree+1):
        newton.append(diffs[0])
        diffs = [y-x for x,y in zip(diffs,diffs[1:])]
    assert diffs == [0]
    # Derivative of the Newton interpolation expansion at zero.
    slope = sum(Fraction((-1)**(k-1)*newton[k], k) for k in range(1,degree+1))
    # Independent derivative using the cardinal Lagrange polynomials at 0,...,d.
    lagrange = sum(Fraction((-1)**(j+1)*comb(degree,j)*values[j]-values[0],j)
                   for j in range(1,degree+1))
    assert slope == lagrange
    return slope, values


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sides", type=int, default=13)
    args = parser.parse_args()
    if args.sides < 3:
        parser.error("A convex polygon has at least three sides")
    control, _ = verify(7)
    assert control == Fraction(1523,180)
    value, values = verify(args.sides)
    degree = 2 * args.sides + 2
    print(json.dumps({"n": args.sides, "dimension": degree, "coefficient": str(value),
                      f"ehrhart_for_q_0_to_{degree + 1}": values}, indent=2))
