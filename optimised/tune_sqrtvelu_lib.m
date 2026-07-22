load "optimised/ops_counter.m";
load "optimised/KummerLine.m";
load "optimised/KummerPoint.m";
load "optimised/poly_ops_part1.m";
load "optimised/poly_ops_part2.m";
load "optimised/sqrtvelu_mtable.m";
load "optimised/KummerIsogeny.m";

function Fp2Cost(Mcount, Scount, Acount, m_fp, s_fp, a_fp)
    m_fp2 := 3.0*m_fp + 5.0*a_fp;
    s_fp2 := 3.0*s_fp + 4.0*a_fp;
    a_fp2 := 2.0*a_fp;
    return Mcount*m_fp2 + Scount*s_fp2 + Acount*a_fp2;
end function;

procedure SqrtVelu_Init_Forced(~self, domain, kernel, degree, bs, gs, ~params)
    R := domain`base_ring;
    KummerLine_ExtractConstants(~A, ~C, domain, ~params);

    f_double(~C2, C, ~params);
    f_add(~Aedx, A, C2, ~params);
    f_sub(~Aedz, A, C2, ~params);

    Build_Sparse_Multiples(~M, kernel, A, C, degree, bs, gs, ~params);
    Build_TI_Tree(~TI, M, bs, ~params);
    Build_T1_Tminus1(~T1, ~Tminus1, ~Aprecomp, M, A, C, bs, gs, ~params);
    Build_Abatch(~Abatchx, ~Abatchz, ~precomp, TI, T1, Tminus1, bs, gs, ~params);

    boundpart := (degree - 1) div 2 - 2*bs*gs;
    for i := 0 to boundpart - 1 do
        Xi2, Zi2 := Explode(M[2*i + 2]);
        f_sub(~tmp4, Xi2, Zi2, ~params);
        f_add(~tmp3, Xi2, Zi2, ~params);
        f_mul(~Abatchx, Abatchx, tmp4, ~params);
        f_mul(~Abatchz, Abatchz, tmp3, ~params);
    end for;

    bits := IntegerToSequence(degree, 2);
    aedxk := R!1; aedzk := R!1;
    for i := #bits to 1 by -1 do
        f_sqr(~aedxk, aedxk, ~params);
        f_sqr(~aedzk, aedzk, ~params);
        if bits[i] eq 1 then
            f_mul(~aedxk, aedxk, Aedx, ~params);
            f_mul(~aedzk, aedzk, Aedz, ~params);
        end if;
    end for;

    abz8 := Abatchz; abx8 := Abatchx;
    for i := 1 to 3 do
        f_sqr(~abz8, abz8, ~params);
        f_sqr(~abx8, abx8, ~params);
    end for;

    f_mul(~AedxFinal, aedxk, abz8, ~params);
    f_mul(~AedzFinal, aedzk, abx8, ~params);

    f_add(~newA, AedxFinal, AedzFinal, ~params);
    f_sub(~newC, AedxFinal, AedzFinal, ~params);
    f_double(~newA, newA, ~params);

    KummerLine_Init(~cod, [* R, [newA, newC] *], ~params);
    self := rec<KummerLineIsogenyVeluRecord | degree := degree, domain := domain, codomain := cod, is_sqrt := true>;
    self`kernel_multiples := <M, TI, Aprecomp, precomp, bs, gs>;
end procedure;

procedure TuneSqrtVelu(primes_list, npts, m_fp, s_fp, a_fp, base_field)
    params := rec<ParamsRecord | >;
    params`p := Characteristic(base_field);
    params`base_field := base_field;
    params`ops := rec<OpsRecord | I:=0, A:=0, M:=0, S:=0>;

    A0 := Random(base_field);
    KummerLine_Init(~L, [* base_field, [A0, base_field!1] *], ~params);
    xK := Random(base_field);
    KummerPoint_Init(~K, L, [xK, base_field!1], ~params);

    eval_pts := [];
    for t := 1 to npts do
        xp := Random(base_field);
        KummerPoint_Init(~Pt, L, [xp, base_field!1], ~params);
        Append(~eval_pts, Pt);
    end for;

    for l in primes_list do
        params`ops := rec<OpsRecord | I:=0, A:=0, M:=0, S:=0>;
        KummerLineIsogeny_Normal_Init(~phi_base, L, K, l, ~params);
        KummerLineIsogeny_Normal_PiProducts(~pi_X_b, ~pi_Z_b, phi_base, ~params);
        for t := 1 to npts do
            KummerLineIsogeny_Normal_Evaluate(~res_base, phi_base, eval_pts[t], ~params);
        end for;
        base_cost := Fp2Cost(params`ops`M, params`ops`S, params`ops`A, m_fp, s_fp, a_fp);

        bestbs := 0; bestgs := 0; bestcost := -1.0;

        for bs := 2 to 32 by 2 do
            gs := 1;
            while 2*bs*gs le (l-1) div 2 do
                if gs le 2*bs and bs le 3*gs then
                    params`ops := rec<OpsRecord | I:=0, A:=0, M:=0, S:=0>;
                    SqrtVelu_Init_Forced(~phi_test, L, K, l, bs, gs, ~params);
		    KummerLineIsogeny_SqrtVelu_PiProducts(~pi_X_t, ~pi_Z_t, phi_test, ~params);
                    for t := 1 to npts do
                        KummerLineIsogeny_SqrtVelu_Evaluate(~res_test, phi_test, eval_pts[t], ~params);
                    end for;
                    cost := Fp2Cost(params`ops`M, params`ops`S, params`ops`A, m_fp, s_fp, a_fp);

                    if bestcost lt 0.0 or cost lt bestcost then
                        bestbs := bs; bestgs := gs; bestcost := cost;
                    end if;
                end if;
                gs +:= 1;
            end while;
        end for;

        winner := (bestcost ge 0.0 and bestcost lt base_cost) select "SQRTVELU" else "NORMAL";
        printf "l=%o bestbs=%o bestgs=%o sqrtvelu_cost=%o normal_cost=%o winner=%o\n",
            l, bestbs, bestgs, bestcost, base_cost, winner;
    end for;
end procedure;
