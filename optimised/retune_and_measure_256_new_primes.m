// 223, 233, 277, 307 calculations for the tables

load "optimised/ops_counter.m";
load "optimised/KummerLine.m";
load "optimised/KummerPoint.m";
load "optimised/poly_ops_part1.m";
load "optimised/poly_ops_part2.m";
load "optimised/sqrtvelu_mtable.m";
load "optimised/sqrtvelu_tuned_tables.m";   
load "optimised/folded_sqrtvelu.m";
load "optimised/KummerIsogeny.m";

load "optimised/data_256_r7.m";  
Fp256 := GF(p);
Fp2_256<i256> := ExtensionField<Fp256, X | X^2 + 1>;
e1 := base_cycle[1];

SWEEP_FLOOR := 100;
BS_CAP := 12;

m_fp := 118.43; s_fp := 100.81; a_fp := 40.11;
m_fp2 := 3.0*m_fp + 5.0*a_fp;
s_fp2 := 2.0*s_fp + 3.0*a_fp;
a_fp2 := 2.0*a_fp;

function WeightedCost(Mcount, Scount, Acount)
    return Mcount*m_fp2 + Scount*s_fp2 + Acount*a_fp2;
end function;

params := rec<ParamsRecord | >;
params`p := Characteristic(Fp2_256);
params`base_field := Fp2_256;
params`ops := rec<OpsRecord | I:=0, A:=0, M:=0, S:=0>;

A0Val := Fp2_256![e1[1][1], e1[1][2]];
xPsVal := Fp2_256![e1[2][1], e1[2][2]];

KummerLine_Init(~L, [* Fp2_256, [A0Val, Fp2_256!1] *], ~params);
KummerPoint_Init(~Ps, L, [xPsVal, Fp2_256!1], ~params);
xP := Random(Fp2_256);
KummerPoint_Init(~Ppush, L, [xP, Fp2_256!1], ~params);

new_primes_256 := [223, 233, 277, 307];

tuned_lines := [];
cost_lines := [];

for l in new_primes_256 do
    cof := Ms mod l eq 0 select Ms div l else (Mt mod l eq 0 select Mt div l else 1);
    KummerPoint_Mul(~K, Ps, cof, ~params);

    // ---- sweep bs/gs, same procedure as joint_retune_full.m's FullRetune ----
    params`ops := rec<OpsRecord | I:=0, A:=0, M:=0, S:=0>;
    KummerLineIsogeny_Normal_Init(~phiN, L, K, l, ~params);
    for t := 1 to 4 do
        KummerLineIsogeny_Normal_Evaluate(~rN, phiN, Ppush, ~params);
    end for;
    KummerLineIsogeny_Normal_PiProducts(~pxN, ~pzN, phiN, ~params);
    normal_cost := params`ops`M*m_fp2 + params`ops`S*s_fp2 + params`ops`A*a_fp2;

    best := <normal_cost, false, 0, 0, false>; // cost, use_sqrt, bs, gs, folded
    for bs := 2 to BS_CAP by 2 do
        gs_max := (l - 1) div (4 * bs);
        for gs := 1 to gs_max do
            // unfolded
            params`ops := rec<OpsRecord | I:=0, A:=0, M:=0, S:=0>;
            KummerLineIsogeny_SqrtVelu_Init(~phiU, L, K, l, ~params : bs_override := bs, gs_override := gs);
            for t := 1 to 4 do
                KummerLineIsogeny_SqrtVelu_Evaluate(~rU, phiU, Ppush, ~params);
            end for;
            KummerLineIsogeny_SqrtVelu_PiProducts(~pxU, ~pzU, phiU, ~params);
            cU := params`ops`M*m_fp2 + params`ops`S*s_fp2 + params`ops`A*a_fp2;
            if cU lt best[1] then best := <cU, true, bs, gs, false>; end if;

            // folded
            params`ops := rec<OpsRecord | I:=0, A:=0, M:=0, S:=0>;
            KummerLineIsogeny_SqrtVelu_Init_Folded(~phiF, L, K, l, ~params : bs_override := bs, gs_override := gs);
            for t := 1 to 4 do
                KummerLineIsogeny_SqrtVelu_Evaluate_Folded(~rF, phiF, Ppush, ~params);
            end for;
            KummerLineIsogeny_SqrtVelu_PiProducts_Folded(~pxF, ~pzF, phiF, ~params);
            cF := params`ops`M*m_fp2 + params`ops`S*s_fp2 + params`ops`A*a_fp2;
            if cF lt best[1] then best := <cF, true, bs, gs, true>; end if;
        end for;
    end for;

    Append(~tuned_lines, Sprintf("    T[%o] := <%o, %o, %o, %o>;", l, best[2], best[3], best[4], best[5]));
    printf "l=%o: normal=%o best=%o [sqrt=%o bs=%o gs=%o folded=%o] speedup_vs_normal=%o\n",
        l, normal_cost, best[1], best[2], best[3], best[4], best[5], normal_cost/best[1];

    // ---- inject the winning entry into the live TunedTable256 so the ----
    // ---- cost measurement below goes through the real dispatcher,    ----
    // ---- exactly like it will once you've pasted this into the file  ----
    TunedTable256[l] := <best[2], best[3], best[4], best[5]>;

    // ---- measure mul/init/eval cost through the (now-tuned) dispatch ----
    params`ops := rec<OpsRecord | I:=0, A:=0, M:=0, S:=0>;
    KummerPoint_Mul(~res_mul, K, l, ~params);
    mul_cost := WeightedCost(params`ops`M, params`ops`S, params`ops`A);

    params`ops := rec<OpsRecord | I:=0, A:=0, M:=0, S:=0>;
    KummerLineIsogeny_Velu_Init(~phi, L, K, l, ~params);
    init_cost := WeightedCost(params`ops`M, params`ops`S, params`ops`A);

    params`ops := rec<OpsRecord | I:=0, A:=0, M:=0, S:=0>;
    KummerLineIsogeny_Velu_Evaluate(~res_eval, phi, Ppush, ~params);
    eval_cost := WeightedCost(params`ops`M, params`ops`S, params`ops`A);

    Append(~cost_lines, Sprintf("    T[%o] := <%o, %o, %o>;", l, mul_cost, init_cost, eval_cost));
end for;

printf "\n// ---- paste into sqrtvelu_tuned_tables.m, BuildTunedTable_256(), before 'return T;' ----\n";
for line in tuned_lines do printf "%o\n", line; end for;

printf "\n// ---- paste into strategy_costs_256.m, BuildRealStrategyCosts_256(), before 'return T;' ----\n";
for line in cost_lines do printf "%o\n", line; end for;
