trace_mod(E, ell) =
{
  /* Computes the trace (mod ell) of an elliptic curve E/Fq over a finite field Fq */
  /* Requires ell = 2 or 3, and the characteristic of Fq to be not 2 or 3 */
  /* We output oo (infinity) when we are unable to compute the trace */
  /* Occurs when ell is not 2 or 3, or when the 3-division poly is irreducible */

  my(A=E.a4, B=E.a6);
  if (ell==2,
    my(t='t);
    polisirreducible(t^3+A*t+B)
  ,
  ell==3,
    my (
      p = elldivpol(E,3),
      factors = factormod(p),
      nr = matsize(factors)[1],
      g = factors[nr,1],
      n = poldegree(g)
    );
    if (n==2, 0,
    n==1 || n==3,
      my(t = polrootsmod(factors[1,1])[1]);
      if (issquare(t^3+A*t+B), 2, 1)
    ,
      oo
    )
  ,
    oo
  );
}

bsgs_with_mod(E, p, d, tr, m, irr3=0) =
{
  /* Computes the trace of an elliptic curve E/p^d given that it is equal to tr (mod m) */
  /* irr3 is 1 if the 3-div poly is irreducible, and 0 otherwise */
  
  my(
    Et=0,
    q=p^d,
    t = sqrtint(4*q),
    bounds = [q-t+1, q+t+1],
    N = (2*t+2)\m
  );

  /* preset number of baby steps */
  r = if (!irr3, sqrtint(N\2)+1, sqrtint(N\12)+1);

  my (
    compute_order(E, P, tr) =
      my(table = List());
      /* if not irr3, then trace is pinpointed mod 3 */
      if (!irr3,
        my(a = ((bounds[1]-1)\m + r - 1) * m + (q+1-tr)%m);
        if (a <= (r-1)*m + bounds[1], a += m);
        
        /* baby steps */
        my (
          mP = ellmul(E, P, m),
          bs = mP
        );
        listput(table, [ellmul(E,P,0), 0]);
        listput(table, [mP, m]);
        listput(table, [ellneg(E,mP), -m]);
        for (j=2, r+1,
          bs = elladd(E, bs, mP);
          listput(table, [bs, j*m]);
          listput(table, [ellneg(E,bs), -j*m])
        );
        
        /* giant steps */
        my (
          kP = ellmul(E,mP,2*r+1),
          gs = ellmul(E,P,a),
          ss = (2*r+1)*m
        );
        listput(table, [gs, a]);
        forstep(mult=a+ss, bounds[2]+r*m, ss,
          gs = elladd(E,gs,kP);
          listput(table, [gs, mult])
        )
      ,
      /* if irr3, then trace is not 0 mod 3 */
        my (
          tr = lift(chinese([Mod(tr, m), Mod(0, 3)])),
          m3 = m*3,
          a = ((bounds[1]-1)\m3 + r - 1) * m3 + (q+1-tr)%m3
        );
        if (a <= (r-1)*m3 + bounds[1], a += m3);

        /* baby steps */
        my (
          mP = ellmul(E,P,m),
          mP_2 = ellmul(E,mP,2),
          bs = mP_2
        );
        listput(table, [ellmul(E,P,0), 0]);
        listput(table, [mP, m]);
        listput(table, [ellneg(E,mP), -m]);
        listput(table, [mP_2, 2*m]);
        listput(table, [ellneg(E,mP_2), -2*m]);

        for (j=3, 3*r-1,
          if (!(j%3),
            bs = elladd(E,bs,mP_2)
          ,
            if (j%3 == 2, bs = elladd(E,bs,mP));
            listput(table, [bs, j*m]);
            listput(table, [ellneg(E,bs), -j*m])
          )
        );

        /* giant steps */
        my (
          kP = ellmul(E,mP,6*r),
          gs = ellmul(E,P,a),
          ss = 6*r*m
        );
        listput(table, [gs, a]);
        forstep(mult=a+ss, bounds[2]+(3*r-1)*m, ss,
          gs = elladd(E,gs,kP);
          listput(table, [gs, mult])
        )
      );
      /* search for collisions in the table by sorting */
      listsort(table);
      my (order = 0, n = #table);
      for (i=1, n-1,
        if (table[i][1] == table[i+1][1], order = gcd(order, table[i][2] - table[i+1][2]))
      );
      order
  );
  my (
    /* E_residue is our updated value of #E(Fq) (mod E_modulus) */
    /* once E_modulus or Et_modulus is greater than 2*floor(sqrt(2q)), #E(Fq) is uniquely determined */
    E_residue = (q+1-tr)%m,
    E_modulus = m,
    Et_residue = (q+1+tr)%m,
    Et_modulus = m,
    turn = 0
  );
  until (turn >= 100,
    turn++;
    my (P = 0, Q = 0);

    /* first run with original curve */
    until (P, P = random(E));
    my (P_order = compute_order(E, P, tr));
    if (!P_order, return(oo));
    E_residue = lift(chinese([Mod(0, P_order), Mod(E_residue, E_modulus)]));
    E_modulus = lcm(P_order, E_modulus);
    if (E_modulus > bounds[2]-bounds[1],
      return(q + 1 - unique_lift(E_residue, E_modulus, bounds[1], bounds[2])));
    
    /* then run with quadratic twist */
    if (!Et, Et = ellinit(elltwist(E)));

    until (Q, Q = random(Et));
    my (Q_order = compute_order(Et, Q, -tr));
    if (!Q_order, return(oo));
    Et_residue = lift(chinese([Mod(0, Q_order), Mod(Et_residue, Et_modulus)]));
    Et_modulus = lcm(Q_order, Et_modulus);
    if (Et_modulus > bounds[2]-bounds[1],
      return(unique_lift(Et_residue, Et_modulus, bounds[1], bounds[2]) - q - 1));
  );
  oo;
}

unique_lift(n, m, a, b) =
{  
  /* Assuming m > a-b and n >= 0, returns unique integer in [a, b] equal to n mod m */
  
  my(N = m*ceil(a/m)+n);
  if (N > b, N - m*ceil((N-b)/m), N);
}

bsgs_mod_p(E, p, d, ap, torsion=1) =
{  
  /* Final function used to compute trace given its value (mod p) */
  /* Handles cases p^d <= 229, d = 1, and d = 2 separately */
  /* Also incorporates torsion information of the original curve over K if relevant */
  
  my(q = p^d);
  if (q<=229,
    ellap(E)
  ,
    if (d==1,
      /* When d = 1 and p > 13, trace is uniquely determined by its value mod p */
      my(t = sqrtint(4*p));
      if (ap > t, ap-p, ap)
    ,
      my(
        q = p^d,
        tors = if (p<=torsion, 1, torsion)
      );
      if (d==2,
        /* Compute traces mod 2 and 3 if not already included in torsion information */
        my(
          tr = if (tors==1,
            my(t2 = trace_mod(E, 2), t3 = trace_mod(E, 3));
            lift(chinese([Mod(ap, p), Mod(t2, 2), Mod(t3, 3)]))
          ,
          tors==3,
            my(t2 = trace_mod(E, 2));
            lift(chinese([Mod(ap, p), Mod(t2, 2), Mod(q+1, 3)]))
          ,
          tors==2 || tors==4,
            my(t3 = trace_mod(E, 3));
            lift(chinese([Mod(ap, p), Mod(q+1, 2), Mod(t3, 3)]))
          ,
            lift(chinese([Mod(ap, p), Mod(q+1, tors)]))
          ),
          mult = if (tors >= 5, tors, 6)
        );
        if (tr > 2*p, tr-mult*p, tr)
      ,
        /* General case when d >= 3 */
        my(
          t2 = if (!(tors%2), q+1, trace_mod(E, 2)),
          t3 = if (!(tors%3), q+1, trace_mod(E, 3))
        );
        /* Handle cases when the 3-div poly is and is not irreducible separately */
        if (t3==oo,
          my(tr = lift(chinese([Mod(ap, p), Mod(t2, 2), Mod(q+1, tors)])));
          bsgs_with_mod(E, p, d, tr, lcm([2,tors])*p, irr3=1)
        ,
          my(tr = lift(chinese([Mod(ap, p), Mod(t2, 2), Mod(t3, 3), Mod(q+1, tors)])));
          bsgs_with_mod(E, p, d, tr, lcm([6,tors])*p, irr3=0)
        )
      )
    )
  );
}