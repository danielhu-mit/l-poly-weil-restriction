from sage.rings.all import Integer, Integers, QQ, ZZ
from sage.rings.finite_rings.finite_field_constructor import GF
from sage.functions.other import sqrt, floor, ceil
from sage.rings.number_field.number_field import NumberField
from sage.schemes.elliptic_curves.constructor import EllipticCurve
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.matrix.constructor import Matrix
from sage.arith.misc import gcd, factor
from sage.rings.fast_arith import prime_range

import time

from sage.all import load
from sage.libs.pari import pari
# from sage.libs.pari.convert_sage import gen_to_sage

load('average_poly_extension.pyx')

ap_at_p = pari('read("LPoly_torsion.gp")')

def compute_all_ap(E, N, check_on=1, torsion_on=0, kappa=None):
    """
    Given an elliptic curve E defined over a number field, compute traces at all good primes up to N
    Parameters:
    - E, an elliptic curve whose base ring is a number field L
    - N, an integer (in our applications, N <= 2^30)
    - check_on, equal to 1 if we compare result with Pari/GP (takes much longer) and 0 otherwise
    - torsion_on, equal to 1 if we compute the torsion subgroup of E/L beforehand and 0 otherwise
    - kappa, the parameter in remainder forest (defaults to ceil(lg(lg(N)))+1)
    Returns a dictionary
    - keys: integer primes, excluding bad primes
    - values: a list, each of whose elements is a 2-element list [residue deg, trace]
    Prints the following information to console
    - Short Weierstrass model for E
    - Number of torsion points on E/K if torsion_on, otherwise 1
    - Bad primes (dividing disc(min poly), N(disc(E)), or N(E.a6()))
    - Time taken by remainder forest (in s)
    - Time taken by factoring & BSGS (in s)
    """
    L = E.base_ring()

    poly, alpha, n = L.absolute_polynomial(), L.gen(), L.absolute_degree()

    D = poly.discriminant()
        
    Es = E.short_weierstrass_model()
    print(f'Short Weierstrass model: {Es}')

    f = [Es.a6(), Es.a4(), L(0), L(1)]
    E_disc = Es.discriminant().norm()
    B_norm = f[0].norm()

    torsion = E.torsion_order() if torsion_on else 1
    print(f'Torsion computed = {torsion}')

    bad_primes = sorted(list({2, 3} | {f[0] for x in [E_disc, B_norm, D] for f in factor(x)}))
    print(f'Bad primes: {bad_primes}')

    start_time = time.time()

    R = QQ['x']; x = R.gen()
    S = R['t']; t = S.gen()

    # convert defining polynomial of E into a list of polynomials in S
    # necessary for the conversion using companion matrices
    f_poly = [S(a.list()) for a in f]
    # compute the Hasse-Witt matrix
    M = Matrix([
        [0, 0, (3-2*x)*f_poly[3]],
        [2*x*f_poly[0], 0, (2-2*x)*f_poly[2]],
        [0, 2*x*f_poly[0], (1-2*x)*f_poly[1]]
    ])

    # call remainder forest
    indices = prime_range(N, algorithm="pari_isprime")
    m = lambda p: p
    k = {p: p for p in indices}
    V0 = Matrix([[0, 0, 1]])
    l = remainder_forest_number_field(M, t, k, poly.list(), indices=indices, m=m, kbase=1, V=V0, kappa=kappa)

    print(f'Time to forest: {round((time.time() - start_time), 3)}')

    start_time = time.time()
    
    # finally, build the dictionary of results
    result = {}
    for p, M in l.items():
        if p in bad_primes:
            continue
        try:
            var = M.base_ring().gen()
            result[p] = ap_at_p(L, var, alpha, p, Es, M, f[0], torsion, check_on).sage()
        except (ArithmeticError, ValueError, IndexError) as e:
            print(f'{p}: {e} (SHOULD NOT HAPPEN)')

    end_time = time.time()
    print(f'Time to process: {round((time.time() - start_time), 3)}')
    return result