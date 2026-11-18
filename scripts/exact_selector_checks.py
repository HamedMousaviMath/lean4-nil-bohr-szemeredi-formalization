from fractions import Fraction as F
from itertools import product
from math import floor

def z(alpha, beta, n):
    return alpha * beta * n * (n - 1) / 2 - alpha * n * floor(beta * n)

def bracket(alpha, beta, n):
    return alpha * (n + 1) * floor(beta * (n + 1))

def fraction(x):
    return x - floor(x)

bracket_count = 0
for denominator in range(2, 14):
    for numerator in range(1, denominator):
        beta = F(numerator, denominator)
        for alpha in (F(-5, 3), F(0), F(2, 3), F(11, 7)):
            for n in range(-30, 31):
                t = fraction(beta * n)
                assert floor(beta * (n + 1)) - floor(beta * n) == (t >= 1-beta)
                assert bracket(alpha, beta, n) == -z(alpha, beta, n+1) + alpha*beta*(n*n+n)/2
                assert bracket(alpha, beta, n) + z(alpha, beta, n) == (
                    alpha*beta*(n*n+n)/2 - alpha*t + alpha*(n+1)*(t >= 1-beta)
                )
                bracket_count += 1

vertices = list(product((0,1), repeat=3))
cube_count = 0
localized_count = 0
for denominator in range(2, 12):
    for numerator in range(1, denominator):
        beta = F(numerator, denominator)
        for n0 in range(-8, 9):
            for steps in product(range(-3, 4), repeat=3):
                ns = [n0 + sum(bit*h for bit,h in zip(omega,steps)) for omega in vertices]
                remainders = [fraction(beta*n) for n in ns]
                cube_count += 1
                if max(remainders)-min(remainders) >= F(1,2):
                    continue
                assert sum((-1)**sum(omega)*z(F(2,3),beta,n)
                           for omega,n in zip(vertices, ns)) == 0
                localized_count += 1

ns = [1+2*sum(omega) for omega in vertices]
remainders = [fraction(F(1,4)*n) for n in ns]
alternating = sum((-1)**sum(omega)*z(F(2,3),F(1,4),n) for omega,n in zip(vertices,ns))
assert min(remainders) == F(1,4) and max(remainders) == F(3,4)
assert alternating == F(-16,3)
print(f"Checked bracket identities in {bracket_count} rational cases.")
print(f"Checked {localized_count} localized cube cancellations among {cube_count} cubes.")
print(f"Exactly-half-length endpoint example: fractional parts in [1/4, 3/4], alternating sum = {alternating}.")
