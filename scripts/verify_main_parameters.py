#!/usr/bin/env python3
"""Recompute printed finite parameters and the Gold hyperplane identity exactly."""
from fractions import Fraction
from math import ceil, comb, floor, log2
import json


def gaussian(n, r, q):
    a = Fraction(1)
    for i in range(r):
        a *= Fraction(q ** (n-i)-1, q ** (r-i)-1)
    assert a.denominator == 1
    return int(a)


def retention(d, w, r):
    return Fraction(2**(r*(d-w))*gaussian(d-r,w-r,2),gaussian(d,w,2))


def verify():
    N, q = 2**27, 2**128
    L = 2**12 * 3 * gaussian(13, 6, 4)
    Z = max(L-floor(Fraction(2**15*comb(L,2),q-N)),
            ceil(Fraction(L*(q-N), q-N + 2**15*(L-1))))
    eps = Fraction((2**12-1)*(2**8-1), N-1)
    p = retention(27,19,12)
    assert p > 1-eps
    B = ceil(p*Z)
    agreement = Fraction(63,128) + Fraction(1,256)*(1-Fraction(63,128))
    assert L == 345166818251997829058040360960
    assert Z == 345161081863282574298189647743
    assert B == 342482627693920113354525730019
    assert agreement == Fraction(16193,32768)
    assert 128-log2(B) < 29.889
    assert Fraction(B,1325775*N*N) > 2**23.77
    half_epsilon = Fraction(3*(2**12-1), N-1)
    half_p = retention(27,25,12)
    assert half_p > 1-half_epsilon
    half_B = ceil(half_p*Z)
    half_agreement = Fraction(63,128) + Fraction(1,4)*(1-Fraction(63,128))
    assert half_epsilon == Fraction(12285,134217727)
    assert half_B == 345129489779595974011716533694
    assert half_agreement == Fraction(317,512)
    assert half_agreement-Fraction(1,2) == Fraction(61,512)
    # Certify the printed probability inequality with integers, not log2.
    assert half_B**1000 > 2**98123
    half_checks = 0
    for d in range(6, 49):
        n = 2**d
        for t in range(2, (d-2)//2+1):
            eps_half = Fraction(3*(4**t-1), n-1)
            old_support = n//2-n//(2**(t+1))
            union_size = old_support + Fraction(n,4)*(1-Fraction(old_support,n))
            assert union_size == Fraction(5*n,8)-Fraction(3*n,2**(t+3))
            assert union_size.denominator == 1 and union_size > n//2
            assert 0 < eps_half < Fraction(3,4)
            assert old_support//2-1+n//4 < n//2
            assert union_size**2 < n*(n//2-1)
            half_checks += 1
    checks = 0
    for j in range(1, 8):
        for n in range(j+3, j+10):
            d, t = 2*n-1, n-1-j
            delta = 2*n-t
            gold = 2**(2*t)*(2**delta-1)*gaussian(n-1,t,4)
            direct = 2**(2*n-2*j-2)*(2**(n+j+1)-1)*gaussian(n-1,j,4)
            old = 2**(2*n-2*j-2)*(2**(n+j)-1)*gaussian(n-1,j,4)
            assert gold == direct and gold > 2*old
            assert Fraction(2**d,2**(2*t)) == 2**(2*j+1)
            checks += 1
    return {'native_field': {'N':N,'q':q,'L':L,'Z':Z,'epsilon':str(eps),
            'retention_probability':str(p),'B':B,'agreement':str(agreement),
            'raw_probability_bits':128-log2(B),
            'large_characteristic_count_ratio_bits':log2(Fraction(B,1325775*N*N))},
            'half_rate_native': {'retention_probability':str(half_p),'B':half_B,
            'agreement':str(half_agreement),'common_agreement':'1/2',
            'source_gap':'61/512','raw_probability_bits':128-log2(half_B),
            'printed_probability_integer_check':True},
            'half_rate_transfer_checks':half_checks,
            'hyperplane_identity_checks':checks}

if __name__ == '__main__':
    print(json.dumps(verify(), indent=2))
