"""Check the limiting kernel and complete finite coefficient patterns by exact arithmetic."""
from csv import DictReader
from fractions import Fraction as Q
from math import comb, factorial
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[1] / "next-candidates"))
from polygon_witness import via_published_recurrence


def kernel(last):
    result = []
    for d in range(last + 1):
        value = Q(5**d, factorial(d))
        for h in range(2, d + 1, 2):
            value -= result[d - h] * Q(2**(h + 1), factorial(h + 2))
        result.append(value)
    return result


def coefficients_from_published(n):
    degree = 2*n + 2
    crown = via_published_recurrence(n, degree + 2)
    values = [sum((q+2-m)*crown[m] for m in range(1, q+2)) for q in range(degree+2)]
    # Form P(X)=product_{i=0}^D (X-i) once, then synthetic division by X-i.
    p = [1]
    for i in range(degree + 1):
        p = [a-i*b for a, b in zip([0]+p, p+[0])]
    row = [0]*(degree+1)
    for i in range(degree + 1):
        quotient = [0]*(degree+1)
        quotient[-1] = p[-1]
        for h in reversed(range(degree)):
            quotient[h] = p[h+1]+i*quotient[h+1]
        assert p[0] == -i*quotient[0]
        multiplier = (-1)**(degree-i)*comb(degree,i)*values[i]
        for h, coefficient in enumerate(quotient):
            row[h] += multiplier*coefficient
    assert sum(c*(degree+1)**h for h,c in enumerate(row)) == factorial(degree)*values[-1]
    return row


def main():
    g = kernel(28)
    print("d\tg_d")
    for i,c in enumerate(g):
        print(f"{i}\t{c}")
    assert all(x>0 for x in g[:27]) and all(x<0 for x in g[27:])
    assert all(abs(g[d-2]/g[d])<=108 for d in range(2,29))
    assert all(abs(g[d-2]/g[d])<=28 for d in (27,28))
    for d in (27,28):
        pole_scale = 10 if d%2 else 2*(d-1)
        upper = Q(22,7)**(d-1 if d%2 else d) * Q(8+4*3**(d-2),factorial(d-2)*pole_scale)
        assert upper < Q(1,5)
    bound = Q(5,4)*Q(35,129)*(1+Q(135,254)/(1-Q(135,192)))
    print(f"uniform normalized error upper bound for n>=65: {bound}")
    assert bound < 1
    with (HERE.parent / 'binomial-trace' / 'signs-through-64.tsv').open() as f:
        reference = {int(r['sides']):r for r in DictReader(f,delimiter='\t')}
    count=0
    for n in range(3,65):
        row = coefficients_from_published(n)
        degree=2*n+2
        neg=[r for r in range(degree+1) if row[r]<0]
        prediction=[r for r in range(1,degree+1)
                    if degree-r>=27 and (degree-r)%4 in (0,3)]
        assert neg==prediction and len(neg)==max(n-12,0) and all(row)
        assert reference[n]['negative_degrees']==(','.join(map(str,neg)) or '-')
        count += len(row)
    print(f"PASS {count} coefficients, 62 complete polygon rows, no zero in degrees 0..2n+2.")
    print("Published crown recurrence + integer Lagrange interpolation agree with determinant table.")
    print("PASS boundary comparisons, adjacent ratios, kernel signs and finite coverage.")

if __name__ == '__main__':
    main()
