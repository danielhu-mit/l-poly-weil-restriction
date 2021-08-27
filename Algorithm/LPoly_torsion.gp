\r BSGS_torsion.gp

ap_at_p(L, t, alpha, p, E, M, f0, torsion=1, check_on=1) = /* t generates the polynomial, a generates the number field */
{
  my (
    result = List(),
    P = idealprimedec(L,p)
  );
  for (i=1, #P,
    my(
      pr = P[i],
      d = pr.f,

      M_nf = substpol(M[1,3], t, alpha),
      M_bar = nfmodpr(L, M_nf, pr),
      f0_bar = nfmodpr(L, f0, pr),
      Ep = ellinit(E, pr),

      power = (p^d-1)\(p-1),
      n = (p-1)\2,
      v = (-1 / f0_bar^n) * M_bar,
      ap = nfmodprlift(L, v^power, pr),
      computed_ap = bsgs_mod_p(Ep, p, d, ap, torsion)
    );
    if (check_on==1,
      my(true_ap = ellap(Ep));
      if(true_ap != computed_ap, print("Bad"))
    );
    listput(result, [d, computed_ap])
  );
  Vec(result)
}