from sage.rings.integer_ring import ZZ
from sage.misc.misc_c import prod

from LPoly_torsion import compute_all_ap

R = ZZ['x']; x = R.gen()

def ap_to_poly(p, aps):
	"""
	p: [[d1, ap1], [d2, ap2]]
	"""
	# r is a 2-element list of the form [degree, ap]
	return prod(1 + r[1]*x**r[0] + p**r[0] * x**(2*r[0]) for r in aps)

def write_result(name, E, N, kappa=7):
	"""
	Given elliptic curve E over a number field, computes all L-polynomials up to N except some bad primes
	Outputs a tuple (bad_primes, result)
	'result' is a dictionary whose keys are primes, and whose values are a list of aps
	Each element of the list is a 2-element list of the form [degree, ap]
	"""
	bad_primes, result = compute_all_ap(E, N, check_on=0, torsion_on=1, kappa=kappa)

	print(bad_primes)
	
	with open(name+'.txt', 'w') as f:
		for p in result:
			aps = ap_to_poly(p, result[p])
			f.write(f'{p}, {aps[1]}, {aps[2]}, {aps[3]}\n')

	return