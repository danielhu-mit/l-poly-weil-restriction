from sage.rings.integer_ring import ZZ
from sage.misc.misc_c import prod

from LPoly_torsion import compute_all_ap

R = ZZ['x']; x = R.gen()

def ap_to_poly(p, aps):
	"""
	Given a prime p and the corresponding values of a_p, computes the L-polynomial of the Weil restriction at p
	Parameters:
	- p, a prime number in Z
	- aps, a list of the form [[d1, ap1], [d2, ap2]]
	"""
	# r is a 2-element list of the form [deg of residue field, ap]
	return prod(1 + r[1]*x**r[0] + p**r[0] * x**(2*r[0]) for r in aps)

def write_result(name, E, N, kappa=7):
	"""
	Given elliptic curve E over a number field, computes all L-polynomials up to N except some bad primes
	Parameters:
	- name, a string to be used as the file name (no extension)
	- E, an elliptic curve whose base ring is a number field L
    - N, an integer (in our applications, N <= 2^30)
    - kappa, the parameter in remainder forest (we tested that optimal time is attained by kappa=7)
    Writes to a new file name.txt
    - Each line contains 4 comma-separated integers p, a1, a2, a3
    - a1, a2, a3 are the first 3 coefficients of the L-polynomial of the Weil restriction of E to QQ at integer prime p
	"""
	result = compute_all_ap(E, N, check_on=0, torsion_on=1, kappa=kappa)
	
	with open(name+'.txt', 'w') as f:
		for p in result:
			aps = ap_to_poly(p, result[p])
			f.write(f'{p}, {aps[1]}, {aps[2]}, {aps[3]}\n')

	return