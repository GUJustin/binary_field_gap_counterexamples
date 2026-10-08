#!/usr/bin/env python3
"""Exact checks of the fixed-extension corollary and exact padding constant."""
from fractions import Fraction
from math import ceil, floor, comb, log2
import json
from verify_main_parameters import gaussian

checks = 0
finite_bound_checks = 0
for c in range(9):
    for e in range(2, 6):
        for d in (24, 25, 32, 33, 64, 65, 96, 97, 128, 129):
            t = d//2-e if c<=1 else (d+c-1)//(c+1)
            if not 2<=t<=d//2:
                continue
            N, q = 2**d, 2**(e*(d+c))
            Delta = d+c-t*(c+(d%2==0))
            assert Delta>=1
            L = 4**t*(2**Delta-1)*gaussian(d//2,t,4)
            delta = Fraction(N,4**t)
            H = q-N
            Z = max(L-floor(delta*comb(L,2)/H), ceil(Fraction(L*H,H+delta*(L-1))))
            assert 0<=Z<q
            checks += 1
            if delta*(L-1)>=H and q>=max(2*N,8*delta):
                assert Z>=Fraction(q,8*delta)
                finite_bound_checks += 1
                if c<=1:
                    assert Fraction(Z,q)>=Fraction(1,16*4**e)

D,r,w=27,12,19
p=Fraction(2**(r*(D-w))*gaussian(D-r,w-r,2),gaussian(D,w,2))
product=Fraction(1)
for i in range(r):
    product *= (1-Fraction(2**i,2**w))/(1-Fraction(2**i,2**D))
assert p==product
L=4**6*3*gaussian(13,6,4)
N=2**D
def count(q):
    Z=max(L-floor(Fraction(2**15*comb(L,2),q-N)),
          ceil(Fraction(L*(q-N),q-N+2**15*(L-1))))
    return Z,ceil(p*Z)
Z,B128=count(2**128)
_,B192=count(2**192)
assert B128==342482627693920113354525730019
assert B192==342488319568189566418277839502
print(json.dumps({'admissible_fixed_extension_checks':checks,
                 'finite_constant_bound_checks':finite_bound_checks,
                 'exact_padding_probability':str(p),
                 'current_field_F128':{'Z':Z,'exact_padding_count':B128,
                    'raw_probability_bits':128-log2(B128),
                    'gain_in_bits':log2(Fraction(B128,342470008761586154232811210191))},
                 'field_F192_exact_padding_count':B192},indent=2))
