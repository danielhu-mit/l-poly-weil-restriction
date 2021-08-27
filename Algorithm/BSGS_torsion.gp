trace_mod(E, ell) = {
  my(A=E.a4, B=E.a6);
  if (ell==2,
    my(t='t); /*'*/
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

bsgs_with_mod(E, p, d, tr, m, irr3=0) = {
  my(
    Et=0,
    q=p^d,
    t = sqrtint(4*q),
    bounds = [q-t+1, q+t+1],
    N = (2*t+2)\m
  );
  r = if (!irr3, sqrtint(N\2)+1, sqrtint(N\12)+1);
  my (
    compute_order(E, P, tr) = my(table = List());
      if (!irr3,
        my(a = ((bounds[1]-1)\m + r - 1) * m + (q+1-tr)%m);
        if (a <= (r-1)*m + bounds[1], a += m);
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
        my (
          tr = lift(chinese([Mod(tr, m), Mod(0, 3)])),
          m3 = m*3,
          a = ((bounds[1]-1)\m3 + r - 1) * m3 + (q+1-tr)%m3
        );
        if (a <= (r-1)*m3 + bounds[1], a += m3);
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
      listsort(table);
      my (order = 0, n = #table);
      for (i=1, n-1,
        if (table[i][1] == table[i+1][1], order = gcd(order, table[i][2] - table[i+1][2]))
      );
      order
  );
  my (
    E_residue = (q+1-tr)%m,
    E_modulus = m,
    Et_residue = (q+1+tr)%m,
    Et_modulus = m,
    turn = 0
  );
  until (turn >= 10,
    turn++;
    my (P = 0, Q = 0);

    until (P, P = random(E));
    my (P_order = compute_order(E, P, tr));
    if (!P_order, return(oo));
    E_residue = lift(chinese([Mod(0, P_order), Mod(E_residue, E_modulus)]));
    E_modulus = lcm(P_order, E_modulus);
    if (E_modulus > bounds[2]-bounds[1],
      return(q + 1 - unique_lift(E_residue, E_modulus, bounds[1], bounds[2])));
    
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

unique_lift(n, m, a, b) = {
  my(N = m *ceil(a/m)+n);
  if (N > b, N - m*ceil((N-b)/m), N);
}

bsgs_test(p, d, num_tests=1) = {
  my (
    q = p^d,
    t = sqrtint(4*q),
    bounds = [q+1-t, q+1+t],
    F = ffinit(p, d),
    a = ffgen(F, 'a), /*'*/
    good = 0,
    total_successful = 0,
    total_tested = 0,
    failures = List()
  );
  for (i=1, num_tests,
    my(E = 0);
    until(E,
      E = ellinit([random(a),random(a)],a)
    );
    my(
      true_ap = ellap(E),
      ap = true_ap%p,
      true_order = q+1-true_ap,
      factors = factor(true_order),
      torsion = List(),
      success = 1
    );
    listput(torsion, 1);
    for (i=1, matsize(factors)[1],
      for (j=1, factors[i,2],
        listput(torsion, factors[i,1]^j)
      )
    );
    for (i=1, #torsion,
      total_tested ++;
      my(my_ap = bsgs_mod_p(E, p, d, ap, torsion[i]));
      if (true_ap == my_ap,
        total_successful++
      ,
        success = 0;
        listput(failures, [E, true_ap, my_ap])
      )
    );
    if (success, good++);
  );
  [good, total_successful, total_tested, failures];
}

bsgs_mod_p(E, p, d, ap, torsion=1) = {
  my(q = p^d);
  if (q<=229,
    ellap(E)
  ,
    if (d==1,
      my(t = sqrtint(4*p));
      if (ap > t, ap-p, ap)
    ,
      my(
        q = p^d,
        tors = if (p<=torsion, 1, torsion)
      );
      if (d==2,
        /* if (t3==oo, print("Epic fail")); */
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

        my(
          t2 = if (!(tors%2), q+1, trace_mod(E, 2)),
          t3 = if (!(tors%3), q+1, trace_mod(E, 3))
        );
        if (t3==oo,
          my(tr = lift(chinese([Mod(ap, p), Mod(t2, 2), Mod(q+1, tors)])));
          bsgs_with_mod(E, p, d, tr, lcm([2,tors])*p, 1)
        ,
          my(tr = lift(chinese([Mod(ap, p), Mod(t2, 2), Mod(t3, 3), Mod(q+1, tors)])));
          bsgs_with_mod(E, p, d, tr, lcm([6,tors])*p, 0)
        )
      )
    )
  );
}