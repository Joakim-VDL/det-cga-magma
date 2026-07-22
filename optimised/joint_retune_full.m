load "optimised/ops_counter.m";
load "optimised/KummerLine.m";
load "optimised/KummerPoint.m";
load "optimised/KummerIsogeny.m";
load "optimised/folded_sqrtvelu.m";

SWEEP_FLOOR := 100;   
BS_CAP := 12;        

procedure FullRetune(primes_list, npts, m_fp, s_fp, a_fp, base_field, MsVal, xPsVal, A0Val)
    m_fp2 := 3.0*m_fp + 5.0*a_fp;
    s_fp2 := 2.0*s_fp + 3.0*a_fp;
    a_fp2 := 2.0*a_fp;

    params := rec<ParamsRecord | >;
    params`p := Characteristic(base_field);
    params`base_field := base_field;
    params`ops := rec<OpsRecord | I:=0, A:=0, M:=0, S:=0>;

    KummerLine_Init(~L, [* base_field, [A0Val, base_field!1] *], ~params);
    KummerPoint_Init(~Ps, L, [xPsVal, base_field!1], ~params);
    xP := Random(base_field);
    KummerPoint_Init(~Ppush, L, [xP, base_field!1], ~params);

    table_lines := [];
    for l in primes_list do
        cof := MsVal mod l eq 0 select MsVal div l else 1;
        KummerPoint_Mul(~K, Ps, cof, ~params);

        params`ops := rec<OpsRecord | I:=0, A:=0, M:=0, S:=0>;
        KummerLineIsogeny_Normal_Init(~phiN, L, K, l, ~params);
        for t := 1 to npts do
            KummerLineIsogeny_Normal_Evaluate(~rN, phiN, Ppush, ~params);
        end for;
        KummerLineIsogeny_Normal_PiProducts(~pxN, ~pzN, phiN, ~params);
        normal_cost := params`ops`M*m_fp2 + params`ops`S*s_fp2 + params`ops`A*a_fp2;

        if l lt SWEEP_FLOOR then
            Append(~table_lines, Sprintf("    T[%o] := <false, 0, 0, false>;", l));
            printf "l=%o: normal=%o (below sweep floor)\n", l, normal_cost;
            continue;
        end if;

        best := <normal_cost, false, 0, 0, false>; // cost, use_sqrt, bs, gs, folded
        for bs := 2 to BS_CAP by 2 do
            gs_max := (l - 1) div (4 * bs);
            for gs := 1 to gs_max do
                // unfolded
                params`ops := rec<OpsRecord | I:=0, A:=0, M:=0, S:=0>;
                KummerLineIsogeny_SqrtVelu_Init(~phiU, L, K, l, ~params : bs_override := bs, gs_override := gs);
                for t := 1 to npts do
                    KummerLineIsogeny_SqrtVelu_Evaluate(~rU, phiU, Ppush, ~params);
                end for;
                KummerLineIsogeny_SqrtVelu_PiProducts(~pxU, ~pzU, phiU, ~params);
                cU := params`ops`M*m_fp2 + params`ops`S*s_fp2 + params`ops`A*a_fp2;
                if cU lt best[1] then best := <cU, true, bs, gs, false>; end if;

                // folded
                params`ops := rec<OpsRecord | I:=0, A:=0, M:=0, S:=0>;
                KummerLineIsogeny_SqrtVelu_Init_Folded(~phiF, L, K, l, ~params : bs_override := bs, gs_override := gs);
                for t := 1 to npts do
                    KummerLineIsogeny_SqrtVelu_Evaluate_Folded(~rF, phiF, Ppush, ~params);
                end for;
                KummerLineIsogeny_SqrtVelu_PiProducts_Folded(~pxF, ~pzF, phiF, ~params);
                cF := params`ops`M*m_fp2 + params`ops`S*s_fp2 + params`ops`A*a_fp2;
                if cF lt best[1] then best := <cF, true, bs, gs, true>; end if;
            end for;
        end for;

        Append(~table_lines, Sprintf("    T[%o] := <%o, %o, %o, %o>;",
            l, best[2], best[3], best[4], best[5]));
        printf "l=%o: normal=%o best=%o [sqrt=%o bs=%o gs=%o folded=%o] speedup_vs_normal=%o\n",
            l, normal_cost, best[1], best[2], best[3], best[4], best[5], normal_cost/best[1];
    end for;

    printf "\n// ---- paste-ready table lines ----\n";
    for line in table_lines do printf "%o\n", line; end for;
end procedure;

//256 bit
load "optimised/data_256.m";
Fp256 := GF(p);
Fp2_256<i256> := ExtensionField<Fp256, X | X^2 + 1>;
e1 := base_cycle[1];
primes_256 := Sort(SetToSequence(SequenceToSet(
    [f[1] : f in Factorization(Ms)] cat [f[1] : f in Factorization(Mt)]
)));
printf "=== 256-bit (npts=4) ===\n";
FullRetune(primes_256, 4, 135.44, 129.23, 37.99, Fp2_256, Ms,
    Fp2_256![e1[2][1], e1[2][2]], Fp2_256![e1[1][1], e1[1][2]]);

// 512 bit
load "optimised/data_512.m";
Fp512 := GF(p);
Fp2_512<i512> := ExtensionField<Fp512, X | X^2 + 1>;
e2 := base_cycle[1];
primes_512 := Sort(SetToSequence(SequenceToSet([f[1] : f in Factorization(Ms)])));
printf "\n=== 512-bit (npts=2) ===\n";
FullRetune(primes_512, 2, 338.66, 305.72, 57.79, Fp2_512, Ms,
    Fp2_512![e2[2][1], e2[2][2]], Fp2_512![e2[1][1], e2[1][2]]);
