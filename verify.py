#!/usr/bin/env python3
"""
Verification script for "A Three-Parameter Reduction of the Perfect Cuboid
Problem, and the Resolution of a Distinguished Family".

Reproduces Table 1 and the counts quoted in Section 6.

Usage:   python3 verify.py 2000
Runtime: roughly 2 minutes at N=2000 on a typical laptop.
         Pure standard library; no packages required.

Expected output at N=2000:

    family A (y^2 = xz)                    199
    product-only (y^2 != xz)               158
      Q > 0                                 28
        d | S   (A^2 an integer)             2
          A^2 a perfect square               0
    sf(m1) >= 2x^2 among the 158            66
    m1 a perfect square: famA 199/199, product-only 0/158
"""

import sys
from math import isqrt, gcd


def is_square(n):
    if n < 0:
        return False
    r = isqrt(n)
    return r * r == n


def squarefree_kernel(n):
    """Product of primes dividing n to an odd power."""
    k = 1
    d = 2
    while d * d <= n:
        if n % d == 0:
            e = 0
            while n % d == 0:
                n //= d
                e += 1
            if e % 2:
                k *= d
        d += 1 if d == 2 else 2
    if n > 1:
        k *= n
    return k


def main(N):
    fam_a = prod_only = 0
    q_pos = integral = square = 0
    sf_fail = 0
    m1sq_a = m1sq_c = 0
    integral_cases = []

    # x > y > z > 0, all odd, gcd(x, y, z) = 1
    for x in range(3, N, 2):
        xx = x * x
        for y in range(3, x, 2):
            yy = y * y
            f1 = xx + yy
            for z in range(1, y, 2):
                if gcd(gcd(x, y), z) != 1:
                    continue
                zz = z * z
                R = f1 * (xx - zz) * (yy - zz)
                if not is_square(R):
                    continue

                k = isqrt(R)
                m = x * y * z
                S = xx + yy - zz
                h = gcd(m, k)
                m1 = m // h

                if y * y == x * z:                      # family A
                    fam_a += 1
                    if is_square(m1):
                        m1sq_a += 1
                    continue

                prod_only += 1
                if is_square(m1):
                    m1sq_c += 1
                if squarefree_kernel(m1) >= 2 * xx:
                    sf_fail += 1

                if m <= k:                              # Q <= 0, so A^2 <= 0
                    continue
                q_pos += 1

                d = m1 - k // h
                if S % d:                               # A^2 not an integer
                    continue
                integral += 1
                A2 = m1 * (S // d)
                assert A2 * (m - k) == m * S            # cross-check
                integral_cases.append((x, y, z, m1, S // d, A2))
                if is_square(A2):
                    square += 1

    print(f"N = {N}\n")
    print(f"  family A (y^2 = xz)                  {fam_a:6d}")
    print(f"  product-only (y^2 != xz)             {prod_only:6d}")
    print(f"    Q > 0                              {q_pos:6d}")
    print(f"      d | S   (A^2 an integer)         {integral:6d}")
    print(f"        A^2 a perfect square           {square:6d}")
    print()
    print(f"  sf(m1) >= 2x^2 among product-only    {sf_fail:6d}")
    print(f"  m1 a perfect square: famA {m1sq_a}/{fam_a}, "
          f"product-only {m1sq_c}/{prod_only}")
    print()
    for x, y, z, m1, e, A2 in integral_cases:
        print(f"  integral A^2: (x,y,z)=({x},{y},{z})  "
              f"m1={m1}  e={e}  A^2={A2}  square={is_square(A2)}")


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 2000)
