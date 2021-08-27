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

    L = E.base_ring()

    poly, alpha, n = L.absolute_polynomial(), L.gen(), L.absolute_degree()
    print(poly)

    D = poly.discriminant()
        
    Es = E.short_weierstrass_model()
    f = [Es.a6(), Es.a4(), L(0), L(1)]
    E_disc = Es.discriminant().norm()
    B_norm = f[0].norm()

    torsion = E.torsion_order() if torsion_on else 1
    print(f'Torsion computed = {torsion}')

    start_time = time.time()

    R = QQ['x']; x = R.gen()
    S = R['t']; t = S.gen()

    f_poly = [S(a.list()) for a in f]
    M = Matrix([
        [0, 0, (3-2*x)*f_poly[3]],
        [2*x*f_poly[0], 0, (2-2*x)*f_poly[2]],
        [0, 2*x*f_poly[0], (1-2*x)*f_poly[1]]
    ])

    # print(M)

    indices = prime_range(N, algorithm="pari_isprime")
    m = lambda p: p
    k = {p: p for p in indices}
    V0 = Matrix([[0, 0, 1]])
    l = remainder_forest_number_field(M, t, k, poly.list(), indices=indices, m=m, kbase=1, V=V0, kappa=kappa)

    print(f'Time to forest: {round((time.time() - start_time), 3)}')

    start_time = time.time()

    bad_primes = sorted(list({2, 3} | {f[0] for x in [E_disc, B_norm, D] for f in factor(x)}))
    
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
    return bad_primes, result