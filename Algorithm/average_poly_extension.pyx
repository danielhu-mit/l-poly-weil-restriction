# distutils: libraries = rforest
# distutils: include_dirs = /usr/local/include
# distutils: extra_compile_args = -fPIC

r"""
Wrapper for remainder forests.

The remainder forest construction is an efficient mechanism for computing
a sequence of quantities of the form ``V M(0) \cdots M(k_i-1) \pmod{m_i}``,
where `M` is a square matrix over `\ZZ[x]`, `V` is a matrix over `\ZZ`,
and `k_i` and `m_i` are sequences of integers.
"""

from cython cimport sizeof
from libc.stdlib cimport malloc, free
from sage.libs.gmp.types cimport mpz_t
from sage.libs.gmp.mpz cimport *
from sage.rings.integer_ring import ZZ
from sage.rings.integer cimport Integer
from sage.matrix.constructor import Matrix
from sage.functions.log import log
from sage.functions.other import ceil
from sage.combinat.integer_vector import IntegerVectors
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from collections import defaultdict
from cysignals.signals cimport sig_on, sig_on_no_except, sig_off

from sage.matrix.special import companion_matrix
from itertools import product

cdef extern from "<rforest.h>":
    void mproduct (mpz_t z, mpz_t *m, long n)

    void rforest (mpz_t *A,   # array of size rows*dim*n (outputs)
                  mpz_t *V,   # array of rows*dim (updated on return)
                  int rows,   # number of rows of V
                  mpz_t *M,   # array of size dim*dim*(deg+1)
                  int deg,    # max deg of polynomial entries of M
                  int dim,    # dimension of square matrix M over Z[x]
                  mpz_t *m,   # array of n positive moduli
                  long kbase, # initial offset
                  long *k,    # array of n values of k
                  long n,     # number of moduli and rows*dim outputs
                  mpz_t z,    # integer divisible by product of the moduli
                  int kappa)  # log_2 of number of trees in the forest

def remainder_forest(M, m, k, kbase=0, indices=None, V=None, ans=None, kappa=None):
    """
    Compute modular reductions of matrix products using a remainder forest.

    INPUT:

     - ``M``: a matrix of polynomials with integer coefficients.
     - ``m``: a list or dict of integers, or a function (see below)
     - ``k``: a list or dict of integers, or a function (see below). This list must be strictly monotone.
     - ``kbase``: an integer (defaults to 0).
     - ``indices``: a list or generator arbitrary values (optional). If included,
       we treat ``m`` and ``k`` as lambda functions to be evaluated on these indices.
     - ``V``: a matrix of integers (optional). If omitted, use the identity matrix.
     - ``ans``: a dict of matrices (optional).
     - ``kappa``: a tuning parameter (optional). This controls the number of trees in the forest.

    OUTPUT:

     - if ``ans`` is omitted, a dict ``l`` indexed by ``indices`` (or by default
       ``range(len(m))``) in which
       ``l[i] == V*prod(M.apply_map(lambda x: x(j)) for j in range(kbase, k[i])) % m[i]``.
       If ``ans`` is included, we return ``None`` and update ``ans[i]`` to
       ``ans[i]*(V*prod(M.apply_map(lambda x: x(j)) for j in range(kbase, k[i])) % m[i])``.
       Entries of ``ans`` whose keys do not appear in ``indices`` are unaffected.

    EXAMPLES:

    For every prime `p` up to 1000, we confirm Wilson's theorem that
    `(p-1)! \equiv -1 \pmod{p}`, and identify the primes for which the
    congruence holds modulo `p^2` (these are called Wilson primes)::

        sage: P.<x> = ZZ[]
        sage: M = Matrix([x])
        sage: m = [p^2 for p in prime_range(600)]
        sage: k = [p for p in prime_range(600)]
        sage: l = remainder_forest(M, m, k, kbase=1)
        sage: all(l[i]%k[i] == k[i]-1 for i in range(len(l)))
        True
        sage: [k[i] for i in range(len(l)) if l[i] == m[i]-1]
        [5, 13, 563]

    Redo the previous example using indices and ``return_dict``::

        sage: P.<x> = ZZ[]
        sage: M = Matrix([x])
        sage: indices = prime_range(600)
        sage: m = lambda p: p^2
        sage: k = lambda p: p
        sage: d = remainder_forest(M, m, k, kbase=1, indices=indices)
        sage: all(d[p]%p == p-1 for p in indices)
        True
        sage: [p for p in indices if d[p] == p^2-1]
        [5, 13, 563]

    A simple example where the matrix product computes a sum::

        sage: P.<x> = ZZ[]
        sage: M = Matrix([[1,0],[x,1]])
        sage: m = [n for n in range(1, 100)]
        sage: k = [n for n in range(1, 100)]
        sage: V = Matrix([[0,1]])
        sage: l = remainder_forest(M, m, k, V=V)
        sage: all(l[i][0,1] == 1 for i in range(1, len(l)))
        True
        sage: all(l[i][0,0] == (0 if i%2==0 else (i+1)//2) for i in range(len(l)))
        True
    """
    cdef:
        mpz_t *A1
        mpz_t *V1
        mpz_t *M1
        mpz_t *m1
        int rows, deg, dim, kappa1
        bint mdict, kdict, ansdict
        Integer tmp
        long *k1
        long n, i, j, j2, t, kbase1
        mpz_t z

    # Sanitize input.

    if not M.is_square():
        raise ValueError("Matrix must be square")
    dim = M.dimensions()[0]
    if V is None:
        rows = dim
    else:
        rows = V.dimensions()[0]
        if V.dimensions()[1] != dim:
            raise ValueError("Matrix dimension mismatch")
    if indices is None:
        n = len(m)
        if len(k) != n:
            raise ValueError("m and k must have the same length")
    else:
        try:
            n = len(indices)
        except TypeError:
            n = sum(1 for _ in indices)

    # Allocate and set input variables.

    deg = 0
    for i in range(dim):
        for j in range(dim):
            if M[i,j] in ZZ:
                continue
            deg = max(deg, M[i,j].degree())

    M1 = <mpz_t *>malloc(dim*dim*(deg+1)*sizeof(mpz_t))
    t = 0
    for i in range(dim):
        for j in range(dim):
            for j2 in range(deg+1):
                tmp = Integer(M[i,j][j2])
                mpz_init_set(M1[t], tmp.value)
                t += 1

    V1 = <mpz_t *>malloc(rows*dim*sizeof(mpz_t))
    t = 0
    for i in range(rows):
        for j in range(dim):
            if V is None:
                mpz_init_set_ui(V1[t], 1 if i==j else 0)
            else:
                tmp = Integer(V[i,j])
                mpz_init_set(V1[t], tmp.value)
            t += 1

    m1 = <mpz_t *>malloc(n*sizeof(mpz_t))
    k1 = <long *>malloc(n*sizeof(long))
    if indices is None:
        for t in range(n):
            tmp = Integer(m[t])
            mpz_init_set(m1[t], tmp.value)
            k1[t] = k[t]
    else:
        mdict = isinstance(m, dict)
        kdict = isinstance(k, dict)
        t = 0
        for x in indices:
            tmp = Integer(m[x] if mdict else m(x))
            mpz_init_set(m1[t], tmp.value)
            k1[t] = k[x] if kdict else k(x)
            t += 1

    if kappa is None:
        kappa1 = ceil(log(log(n,2),2)) + 1
    else:
        kappa1 = kappa

    kbase1 = kbase


    # print(f'kappa = {kappa1}')
    # print(f"n = {n} rows={rows} dim={dim} deg={deg}")

    # Allocate output variables.

    A1 = <mpz_t *>malloc(rows*dim*n*sizeof(mpz_t))
    for t in range(rows*dim*n):
        mpz_init(A1[t])
    mpz_init(z)

    try:
        # Call rforest.
        sig_on_no_except()
        mproduct(z, m1, n)
        rforest(A1, V1, rows, M1, deg, dim, m1, kbase1, k1, n, z, kappa1)
        sig_off()

        # Retrieve answers. If ans is not None, we assume it is a dict of integer matrices
        # and fill in the entries rather than creating matrices from scratch.

        if indices is None:
            indices = range(n)
        tmp = Integer(0)
        tmp_mat = Matrix(ZZ, rows, dim)
        ansdict = (ans is not None)
        if not ansdict:
            ans = {}
        t = 0
        for i in range(n):
            for j in range(rows):
                for j1 in range(dim):
                    tmp.set_from_mpz(A1[t])
                    tmp_mat[j,j1] = tmp
                    t += 1
            if ansdict:
                ans[indices[i]] *= tmp_mat
            else:
                ans[indices[i]] = tmp_mat.__copy__()

    # Free memory.

    finally:
        for i in range(dim*dim*(deg+1)):
            mpz_clear(M1[i])
        free(M1)
        for i in range(rows*dim):
            mpz_clear(V1[i])
        free(V1)
        for i in range(n):
            mpz_clear(m1[i])
        free(m1)
        free(k1)
        for i in range(rows*dim*n):
            mpz_clear(A1[i])
        free(A1)
        mpz_clear(z)

    if ansdict:
        return None
    return ans

def poly_to_mat(p, f):
    Mf = companion_matrix(f)
    # print(p)
    return sum(a * Mf**i for i,a in enumerate(p))

# def mat_to_poly(m):
#     return [r[0] for r in M]

def inflate_matrix(M, var, f):
    """
    Compute an inflation of a matrix over a polynomial ring.

    The return value is a matrix over another polynomial ring with the specified variables omitted.
    It is a block matrix with blocks corresponding to monomials in the omitted variables.

    EXAMPLES::

        sage: R.<x,y> = PolynomialRing(ZZ, 2)
        sage: M = Matrix([[x+y, x*y], [x-y, 1]])
        sage: inflate_matrix(M, [y], 2)
        [ x  1  0  x]
        [ 0  x  0  0]
        [ x -1  1  0]
        [ 0  x  0  1]
        sage: inflate_matrix(M, [x,y], 2)
        [ 0  0  1  0  0  0]
        [ 0  0  1  0  0  0]
        [ 0  0  0  0  0  0]
        [ 0  0  1  1  0  0]
        [ 0  0 -1  0  1  0]
        [ 0  0  0  0  0  1]
    """
    e = len(f)-1

    R = M.base_ring()
    dim = M.dimensions()
    gens = R.gens()
    if var not in gens:
        raise ValueError("Invalid key in d")

    n = R.ngens()
    vars2 = tuple(x for x in gens if x != var)

    K = R.base_ring()
    # R1 = PolynomialRing(K, n-1, names=vars2)
    # R2 = PolynomialRing(R1, name=var)
    # Must explicitly define the coercion map from R to R2.
    # var_target = [(R2.gen() if x == var else R2(R1.gens()[vars2.index(x)])) for x in gens]
    # h = R.hom(var_target)
    mat_dict = {}
    for i, j in product(range(dim[0]), range(dim[1])):
        # a = h(M[i, j])
        a = M[i, j].list()
        if not a:
            a = [0]
        a_mat = poly_to_mat(a, f)
        # print(a_mat)
        for p, q in product(range(e), range(e)):
            mat_dict[i*e + p, j*e + q] = a_mat[p, q]

    return Matrix(mat_dict)

def deflate_matrix(M, var, f):
    """
    Undo the effect of ``inflate_matrix``.

    EXAMPLES::

        sage: R.<x,y> = PolynomialRing(ZZ, 2)
        sage: M = Matrix([[x+y, x*y], [x-y, 1]])
        sage: deflate_matrix(inflate_matrix(M, [y], 2), [y], 2) == M
        True
        sage: deflate_matrix(inflate_matrix(M, [x,y], 2), [x,y], 2)
        [x + y     0]
        [x - y     1]
    """
    e = len(f)-1

    K = M.base_ring()
    dim = M.dimensions()

    mat_dict = {}
    R = PolynomialRing(K, name=var)

    for i, j in product(range(dim[0]//e), range(dim[1]//e)):
        mat_dict[i, j] = R([M[i*e+p, j*e] for p in range(e)])

    return Matrix(mat_dict)

def remainder_forest_number_field(M, var, k, f, indices=None, m=None, kbase=0, V=None, ans=None, kappa=None):
    """
    Compute a remainder forest using one or more "generic primes".

    INPUT:

     - ``M``: a matrix of multivariate polynomials with integer coefficients.
     - ``d``: a dictionary keyed by variables in the base ring of ``M``. Exactly one
      variable must be omitted.
     - ``e``: a positive integer.
     - ``k``: a list or dict of integers, or a function (see below). This list must be monotone;
         if a dict or function is given, it must evaluate to a monotone list when applied to ``indices``.
     - ``indices``: a list or generator arbitrary values.
     - ``kbase``: an integer (defaults to 0).
     - ``m``: a lambda function on indices (see below).
     - ``V``: a matrix of polynomials. If omitted, use the identity matrix.
     - ``ans``: a dict of matrices (optional).
     - ``kappa``: a tuning parameter (optional). This controls the number of trees in the forest.

    OUTPUT:

     As for ``remainder_forest`` except that ``M`` is evaluated with the variables named in ``d``
     truncated modulo the ``e``-th power of the ideal they jointly generate, then specialized as per ``d``;
     the other variable is evaluated at successive integers as before. Also, the moduli may not be specified freely:
     if ``m`` is omitted, we impose that ``m[p] == p^e``.
     
     While ``d`` must include all but one variable, the values of ``d`` may omit keys. In these cases, the corresponding
     variable is left unevaluated.

    EXAMPLES:

        sage: P.<x,y,z> = ZZ[]
        sage: M = Matrix([[x+y+1,z],[y+z,1]])
        sage: indices = prime_range(2, 50)
        sage: k = {p: p-1 for p in indices}
        sage: V = Matrix([[0,1+y]])
        sage: d = {x: {p: p for p in indices}, y: {p: -p for p in indices}}
        sage: ans = remainder_forest_generic_prime(M, d, 2, k, indices=indices, V=V)
        sage: ans2 = {p: V.apply_map(lambda t: t.subs({x: p, y: -p})) for p in indices}
        sage: ans2 = {p: ans2[p] * prod(M.apply_map(lambda t: t.subs({x: p, y: -p, z: j})) for j in range(k[p])) for p in indices}
        sage: all((ans[p] - ans2[p]) % p^2 == 0 for p in indices)
        True

    """
    e = len(f)-1

    if not M.is_square():
        raise ValueError("Matrix must be square")
    dim = M.dimensions()[0]
    if V is None:
        rows = dim
    else:
        rows = V.dimensions()[0]
        if V.dimensions()[1] != dim:
            raise ValueError("Matrix dimension mismatch")

    R = M.base_ring()
    # if any(x not in R.gens() for x in d):
    #     raise ValueError("Invalid key in d")
    # x = [x for x in R.gens() if x not in d]
    # if len(x) != 1:
    #    raise ValueError("d must omit exactly one variable of M")

    # vars = list(d.keys())
    if V is None:
        V1 = None
    else:
        V1 = inflate_matrix(V.change_ring(R), var, f)
    M1 = inflate_matrix(M, var, f)

    # print(M1)

    if m is None:
        m = {p: p**e for p in indices}
    else:
        m = {p: m(p) for p in indices}
    
    tmp = remainder_forest(M1, m, k, kbase=kbase, indices=indices, V=V1, kappa=kappa)
    # if indices is None:
    #     indices = tmp.keys()
    if ans is None:
        ans = {i: 1 for i in indices}

    for i in indices:
        M2 = deflate_matrix(tmp[i], var, f)
        R2 = M2.base_ring()
    #     d2 = {x: d[x][i] for x in R2.gens() if i in d[x]}
    #     ans[i] *= M2.apply_map(lambda t,d2=d2: t.subs(d2))
        ans[i] *= M2

    # if ansdict:
    #     return None
    return ans
