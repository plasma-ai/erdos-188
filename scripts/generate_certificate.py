"""Generate `Erdos188/LowerBound/Certificate/Data.lean`.

The data are the dyadic starting values `(c₀, c₁)` of every polynomial
approximation of `J₀(√n t)` on the intervals `[0,2], [2,4], …, [78,80],
[80,81]`, the positivity breakpoints of every interval, and a dyadic upper
bound on residual plus join error for every (interval, radius) pair.

The first interval starts from `(1, 0)`, and each later start is the
preceding polynomial's endpoint value and derivative rounded to the nearest
multiple of `2^-32`. The error bounds are computed by a mirror of the Lean checker in
`Erdos188/LowerBound/Certificate/Checker.lean` and rounded up to multiples of
`2^-64`. The script then reruns the full mirrored check before writing.

Run from the repository root with Python 3 (standard library only):

    python3 scripts/generate_certificate.py
"""

from fractions import Fraction as Rat
from pathlib import Path

DEGREE = 44
NUM_INTERVALS = 41
START_SCALE = 2**32
ERROR_SCALE = 2**64
ERROR_BUDGET = Rat(1, 100)
RADII = [1, 3, 4, 7, 9, 13, 16, 21, 31, 36, 43]
COEFFS = [322, -544, 320, -352, 384, -224, 192, -224, -224, 64, 96]
OUTPUT = (Path(__file__).resolve().parent.parent
          / 'Erdos188' / 'LowerBound' / 'Certificate' / 'Data.lean')


# Mirrors of the Lean definitions, in the same order as `Checker.lean`.

def eval_poly(c, x):
    result = Rat(0)
    for ck in reversed(c):
        result = ck + x*result
    return result


def add_poly(p, q):
    if len(p) < len(q):
        p, q = q, p
    return [p[k] + (q[k] if k < len(q) else 0) for k in range(len(p))]


def scale_poly(r, p):
    return [r*c for c in p]


def mul_linear(u, w, p):
    if not p:
        return []
    return add_poly([u*c for c in p] + [Rat(0)], [Rat(0)] + [w*c for c in p])


def deriv_poly(p):
    return [k*p[k] for k in range(1, len(p))]


def shift_poly(u, w, p):
    result = []
    for c in reversed(p):
        result = add_poly([c], mul_linear(u, w, result))
    return result


def bernstein(c):
    if not c:
        return []
    a, rest = c[0], c[1:]
    beta = bernstein(rest)
    big_n = len(rest)
    return [a] + [a + Rat(j+1, big_n)*b for j, b in enumerate(beta)]


def abs_int_bound(h, c):
    return sum((abs(ck)*h**(k+1)/(k+1) for k, ck in enumerate(c)), Rat(0))


def residual_num(n, a, p):
    return add_poly(mul_linear(a, 1, deriv_poly(deriv_poly(p))),
                    add_poly(deriv_poly(p), scale_poly(n, mul_linear(a, 1, p))))


def residual_bound(n, a, h, p):
    q = residual_num(n, a, p)
    if a == 0:
        return abs_int_bound(h, q[1:]) if q[0] == 0 else None
    return abs_int_bound(h, q) / a


def join_weight(n):
    q = 1
    while not n < q*q:
        q += 1
    return q


def join_bound(n, h, p, c0, c1):
    return (abs(eval_poly(deriv_poly(p), h) - c1)
            + join_weight(n)*abs(eval_poly(p, h) - c0))


def build_poly(n, a, c0, c1):
    c = [c0, c1]
    for k in range(DEGREE-1):
        if a == 0:
            c.append(-(n*c[k]) / ((k+2)*(k+2)))
        else:
            cm = c[k-1] if k else 0
            c.append(-((k+1)*(k+1)*c[k+1] + n*a*c[k] + n*cm)
                     / (a*(k+1)*(k+2)))
    return c


def interval_start(k):
    return 2*k


def interval_width(k):
    return 2 if k+1 < NUM_INTERVALS else 1


def check_piece(p, u, v):
    return u < v and all(ERROR_BUDGET <= b
                         for b in bernstein(shift_poly(u, v-u, p)))


def check_pieces(p, h, u, breaks):
    if not breaks:
        return False
    for v in breaks:
        if not check_piece(p, u, v):
            return False
        u = v
    return u == h


# The fixed positivity subdivisions: `[2,4]` at `3, 7/2` and `[4,6]` at
# `9/2, 5`, in local coordinates.
BREAKS = {1: [Rat(1), Rat(3, 2), Rat(2)], 2: [Rat(1, 2), Rat(1), Rat(2)]}


def round_dyadic(x, scale):
    return (2*scale*x.numerator + x.denominator) // (2*x.denominator)


def ceil_dyadic(x, scale):
    return -((-scale*x.numerator) // x.denominator)


def main():
    # Starting values: `(1, 0)`, then each endpoint rounded to `2^-32`.
    start = [[(START_SCALE, 0)]*len(RADII)]
    for k in range(NUM_INTERVALS-1):
        row = []
        for n, (m0, m1) in zip(RADII, start[k]):
            p = build_poly(n, interval_start(k), Rat(m0, START_SCALE),
                           Rat(m1, START_SCALE))
            h = interval_width(k)
            row.append((round_dyadic(eval_poly(p, h), START_SCALE),
                        round_dyadic(eval_poly(deriv_poly(p), h),
                                     START_SCALE)))
        start.append(row)
    # Error bounds and the mirrored check.
    errors = []
    min_bernstein = None
    for k in range(NUM_INTERVALS):
        a, h = interval_start(k), interval_width(k)
        polys, row = [], []
        for i, n in enumerate(RADII):
            m0, m1 = start[k][i]
            p = build_poly(n, a, Rat(m0, START_SCALE), Rat(m1, START_SCALE))
            polys.append(p)
            r = residual_bound(n, a, h, p)
            assert r is not None
            if k+1 < NUM_INTERVALS:
                n0, n1 = start[k+1][i]
                r += join_bound(n, h, p, Rat(n0, START_SCALE),
                                Rat(n1, START_SCALE))
            assert n <= join_weight(n)**2
            row.append(ceil_dyadic(r, ERROR_SCALE))
        errors.append(row)
        combined = [Rat(191)]
        for ci, p in zip(COEFFS, polys):
            combined = add_poly(scale_poly(Rat(ci), p), combined)
        assert check_pieces(combined, h, Rat(0), BREAKS.get(k, [Rat(h)]))
        u = Rat(0)
        for v in BREAKS.get(k, [Rat(h)]):
            m = min(bernstein(shift_poly(u, v-u, combined)))
            min_bernstein = m if min_bernstein is None else min(m, min_bernstein)
            u = v
    total = sum(abs(ci)*sum(Rat(errors[k][i], ERROR_SCALE)
                            for k in range(NUM_INTERVALS))
                for i, ci in enumerate(COEFFS))
    assert total <= ERROR_BUDGET
    print(f'weighted error bound {float(total):.6g}, '
          f'smallest Bernstein coefficient {float(min_bernstein):.6g}')
    write_lean(start, errors)


def lean_rat(x):
    return str(x.numerator) if x.denominator == 1 else f'{x.numerator}/{x.denominator}'


def lean_list(items, indent, width=100):
    # A Lean list literal of `items` opening at column `indent - 1`, wrapped
    # at `width` columns, with continuation lines indented by `indent` spaces.
    lines, line = [], ' '*(indent-1) + '['
    for j, item in enumerate(items):
        piece = item + (', ' if j+1 < len(items) else ']')
        if len(line) + len(piece.rstrip()) > width and line.strip(' ['):
            lines.append(line.rstrip())
            line = ' '*indent
        line += piece
    return '\n'.join(lines + [line])[indent-1:]


def write_lean(start, errors):
    lines = [
        'module',
        '',
        '/-!',
        '# Certificate data',
        '',
        'Generated by `scripts/generate_certificate.py`; do not edit by hand.',
        '',
        'Entry `k` of `certificate` belongs to the interval `[2k, 2k + 2]` (`[80, 81]` for',
        '`k = 40`). For the `i`-th radius `n` of `kernelRadius`, `start[i] = (m₀, m₁)` gives',
        'the starting values `c₀ = m₀ / 2^32`, `c₁ = m₁ / 2^32` of the approximation of',
        '`J₀(√n t)`, and `err[i] = e` gives the error bound `e / 2^64`. `breaks` are the right',
        'endpoints of the positivity pieces in the local coordinate `t - 2k`.',
        '-/',
        '',
        '@[expose] public section',
        '',
        'namespace Erdos188.LowerBound.Certificate',
        '',
        '/-- The certificate data of one polynomial interval. -/',
        'structure IntervalCert where',
        '  /-- Right endpoints of the positivity pieces, in local coordinates. -/',
        '  breaks : List Rat',
        '  /-- Numerators over `2^32` of the starting values `(c₀, c₁)`, one pair per radius. -/',
        '  start : List (Int × Int)',
        '  /-- Numerators over `2^64` of the residual-plus-join error bounds, one per radius. -/',
        '  err : List Nat',
        '  deriving Inhabited',
        '',
        '/-- The certificate data, one entry per polynomial interval. -/',
        'def certificate : List IntervalCert := [',
    ]
    for k in range(NUM_INTERVALS):
        breaks = lean_list([lean_rat(b) for b in BREAKS.get(k, [Rat(interval_width(k))])], 14)
        pairs = lean_list([f'({m0}, {m1})' for m0, m1 in start[k]], 14)
        errs = lean_list([str(e) for e in errors[k]], 12)
        sep = ',' if k+1 < NUM_INTERVALS else ''
        lines += [
            f'  -- interval {k}: [{interval_start(k)}, {interval_start(k) + interval_width(k)}]',
            f'  {{ breaks := {breaks}',
            f'    start := {pairs}',
            f'    err := {errs} }}{sep}',
        ]
    lines += [
        '  ]',
        '',
        'end Erdos188.LowerBound.Certificate',
        '',
    ]
    OUTPUT.write_text('\n'.join(lines))
    print(f'wrote {OUTPUT}')


if __name__ == '__main__':
    main()
