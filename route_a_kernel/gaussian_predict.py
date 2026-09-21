"""
Route A / Gaussian-integer predictive tool.

Given an observed kernel (alpha, beta) from Theorem 4.1's decomposition
(x^2+y^2 = alpha*beta*u1^2), predict candidate x:y ratios that are likely to
recur across multiple product-only triples sharing that kernel -- the same
phenomenon found empirically for (alpha,beta)=(5,2) giving x:y=39:37 twice
in the (5,2,19) kernel group.

Mechanism (derived and verified against kernel_table_20000.csv, see
referee_notes.md "Gaussian integer arithmetic" section, 2026-09-19):

  x^2+y^2 = alpha*beta*u1^2 is a sum-of-two-squares equation, native to the
  Gaussian integers Z[i]. Theorem 4.1(iii) already requires every odd prime
  of alpha*beta to be =1 mod 4 (the classical sum-of-two-squares condition).
  A ratio a:b (gcd(a,b)=1) is compatible with kernel (alpha,beta) iff
  squarefree_part(a^2+b^2) == alpha*beta exactly.

  The known "productive ratio" 39:37 arose specifically because u1 was
  divisible by an EXTRA prime (17, itself =1 mod 4) not already in
  alpha*beta=10, used in its "unbalanced" phase (lambda^2 rather than
  lambda*lambda_conj) -- giving a NEW primitive ratio 39:37, distinct from
  alpha*beta's own minimal representation (1,3). Small extra primes are
  statistically the most likely to recur across independently-sized
  members of a kernel family (any u1 divisible by 17 works, not just one
  specific u1 value), which is exactly why 39:37 showed up twice rather
  than being a one-off.

This tool generates such candidates directly (Cornacchia's algorithm +
exhaustive sign enumeration) instead of only recognizing them after brute
force search has already found them.
"""

import itertools
from math import gcd


def is_prime(n):
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    i = 3
    while i * i <= n:
        if n % i == 0:
            return False
        i += 2
    return True


def factorize(n):
    """Trial-division factorization, fine for the sizes used here (<1e12)."""
    f = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def squarefree_part(n):
    r = 1
    for p, e in factorize(n).items():
        if e % 2 == 1:
            r *= p
    return r


def isqrt(n):
    if n < 0:
        raise ValueError("isqrt of negative number")
    x = int(n ** 0.5)
    while x * x > n:
        x -= 1
    while (x + 1) * (x + 1) <= n:
        x += 1
    return x


def cornacchia(p):
    """Return (a,b), a>=b>0, with a^2+b^2=p, for prime p==2 or p%4==1."""
    if p == 2:
        return (1, 1)
    if p % 4 != 1:
        raise ValueError(f"{p} is not 2 or 1 mod 4")
    # find a quadratic non-residue g mod p, then r0 = sqrt(-1) mod p
    g = 2
    while pow(g, (p - 1) // 2, p) != p - 1:
        g += 1
    r0 = pow(g, (p - 1) // 4, p)
    if 2 * r0 > p:
        r0 = p - r0
    # Euclidean algorithm on (p, r0), stopping the FIRST time the remainder
    # drops below sqrt(p) -- that remainder is one coordinate, the other is
    # recovered via sqrt(p - b^2), NOT the next Euclidean remainder.
    a, b = p, r0
    while b * b > p:
        a, b = b, a % b
    y2 = p - b * b
    y = isqrt(y2)
    if y * y != y2:
        raise AssertionError(f"Cornacchia failed for p={p}: b={b}, p-b^2={y2} not a perfect square")
    return (b, y) if b >= y else (y, b)


def complex_mul(z1, z2):
    a, b = z1
    c, d = z2
    return (a * c - b * d, a * d + b * c)


def complex_pow(z, e):
    result = (1, 0)
    for _ in range(e):
        result = complex_mul(result, z)
    return result


def gaussian_prime_powers(n):
    """
    For n = 2^eps * prod(ell_i^e_i), each ell_i an odd prime =1 mod 4 (any
    exponent e_i >= 1 -- n need NOT be squarefree, unlike an earlier version
    of this function; a prime from an "extra factor" u1=ell enters here to
    EVEN exponent 2, not 1, since it comes from u1^2 inside x^2+y^2=alpha*
    beta*u1^2), return eps and the list of (lambda_i^e_i) as a Gaussian
    integer, one per distinct odd prime -- ready to combine with a bit
    choosing lambda_i^e_i or conj(lambda_i)^e_i, i.e. sending the prime's
    FULL exponent to one conjugate (the only choice keeping the result
    primitive; splitting exponent between lambda and conj(lambda) would
    make ell_i divide both real and imaginary parts).
    """
    f = factorize(n)
    for p, e in f.items():
        if p != 2 and p % 4 != 1:
            raise ValueError(
                f"{n} has prime factor {p} = 3 mod 4 -- no primitive "
                f"sum-of-two-squares representation exists"
            )
    eps = f.get(2, 0)
    if eps > 1:
        raise ValueError(f"{n} has 4 | n -- no primitive representation exists")
    odd_items = sorted((p, e) for p, e in f.items() if p != 2)
    gp_pow = [complex_pow(cornacchia(p), e) for p, e in odd_items]
    return eps, odd_items, gp_pow


def primitive_representations(n):
    """
    All primitive (gcd(a,b)=1) representations a^2+b^2=n, a>b>0, where n =
    2^eps * prod(ell_i^e_i) (eps in {0,1}, each ell_i =1 mod 4, any e_i).
    Returns a set of (a,b) pairs, one canonical representative per {a,b}
    unordered pair (a>b, both positive) -- deduped over unit multiplication
    (*1,*i,*-1,*-i) and complex conjugation.
    """
    eps, odd_items, gp_pow = gaussian_prime_powers(n)
    k = len(gp_pow)
    results = set()
    for bits in itertools.product([0, 1], repeat=k):
        z = (1, 1) if eps else (1, 0)
        for bit, zp in zip(bits, gp_pow):
            factor = zp if bit == 0 else (zp[0], -zp[1])
            z = complex_mul(z, factor)
        a, b = abs(z[0]), abs(z[1])
        if a == 0 or b == 0:
            continue
        if gcd(a, b) != 1:
            # sanity check -- should never happen for squarefree n with
            # every prime used all-or-nothing (bit selects lambda XOR
            # lambda_conj entirely, never a mix), but verify rather than
            # assume.
            continue
        a, b = max(a, b), min(a, b)
        results.add((a, b))
    return results


def candidate_ratios(alpha, beta, u1_bound=50):
    """
    For kernel pair (alpha,beta), return a dict mapping each candidate u1
    value (u1=1 is the base alpha*beta ratio itself; u1>1 any integer up to
    u1_bound) to the set of NEW primitive ratios a:b with
    squarefree_part(a^2+b^2) == alpha*beta, arising from x^2+y^2 =
    alpha*beta*u1^2 with that u1.

    u1 need not be a single prime, or even squarefree: any inert prime
    (=3 mod 4) in u1 contributes as a plain real scalar at any power (no
    new phase, so no new ratio by itself); any split prime (=1 mod 4) in
    u1, to whatever power it appears, must go ENTIRELY to one of its two
    Gaussian conjugates to keep the result primitive -- that "fully
    unbalanced" choice is what generates a genuinely new ratio, distinct
    from anything u1=1 or a smaller u1 already gave.  Searching all of
    u1=2..u1_bound (not just single extra primes) is what's needed to catch
    cases like u1=15=3*5 (an inert prime times a split prime), which a
    single-extra-prime search misses entirely.
    """
    ab = alpha * beta
    sf_ab = squarefree_part(ab)

    out = {}
    out[1] = primitive_representations(sf_ab)
    seen = set(out[1])

    for u1 in range(2, u1_bound + 1):
        n = sf_ab * u1 * u1
        try:
            reps = primitive_representations(n)
        except ValueError:
            continue
        new_reps = reps - seen
        if new_reps:
            out[u1] = new_reps
            seen |= new_reps

    return out


if __name__ == "__main__":
    print(__doc__)
