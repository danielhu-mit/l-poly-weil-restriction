\r BSGS_torsion.gp

ap_at_p(L, t, alpha, p, E, M, f0, torsion=1, check_on=1) =
{
  /* Parameters:
    - L, the number field over which E is defined
    - t, the generator of the polynomial ring representing the generator of L
    - alpha, the actual generator of L
    - p, a prime in ZZ
    - E, an elliptic curve defined over L
    - M, the Hasse-Witt matrix corresponding to the prime p
    - f0, the constant coefficient of f in y^2 = f(x)
    - torsion, the cardinality of the torsion subgroup of E/L
    - check_on, 1 if we compare result to Pari/GP (takes significantly longer), 0 if we do not
  */
  my (
    result = List(),
    P = idealprimedec(L,p)
  );
  for (i=1, #P,
    my(
      pr = P[i],
      d = pr.f,
      /* reduce everything modulo the prime pr in O_L above p */
      M_nf = substpol(M[1,3], t, alpha),
      M_bar = nfmodpr(L, M_nf, pr),
      f0_bar = nfmodpr(L, f0, pr),
      Ep = ellinit(E, pr),
      /* compute the trace (mod p) given Hasse invariant */
      power = (p^d-1)\(p-1),
      n = (p-1)\2,
      v = (-1 / f0_bar^n) * M_bar,
      ap = nfmodprlift(L, v^power, pr),
      /* compute the actual trace */
      computed_ap = bsgs_mod_p(Ep, p, d, ap, torsion)
    );
    if (check_on==1,
      /* when check_on=1, outputs to console if computed value of a_p is wrong */
      my(true_ap = ellap(Ep));
      if(true_ap != computed_ap, print("Bad"))
    );
    listput(result, [d, computed_ap])
  );
  Vec(result)
}