load "optimised/ops_counter.m";
load "optimised/KummerLine.m";
load "optimised/KummerPoint.m";
load "optimised/poly_ops_part1.m";
load "optimised/poly_ops_part2.m";
load "optimised/sqrtvelu_mtable.m";
load "optimised/sqrtvelu_tuned_tables.m";
load "optimised/KummerIsogeny.m";
load "optimised/data_512.m";

Fp := GF(p);
Fp2<i> := ExtensionField<Fp, X | X^2 + 1>;

m_fp := 306.11; s_fp := 264.04; a_fp := 50.68;
m_fp2 := 3.0*m_fp + 5.0*a_fp;
s_fp2 := 2.0*s_fp + 3.0*a_fp;
a_fp2 := 2.0*a_fp;

function WeightedCost(Mcount, Scount, Acount)
    return Mcount*m_fp2 + Scount*s_fp2 + Acount*a_fp2;
end function;

params := rec<ParamsRecord | >;
params`p := p;
params`base_field := Fp2;
params`ops := rec<OpsRecord | I:=0, A:=0, M:=0, S:=0>;

A0 := Random(Fp2);
KummerLine_Init(~L, [* Fp2, [A0, Fp2!1] *], ~params);
xK := Random(Fp2);
KummerPoint_Init(~K, L, [xK, Fp2!1], ~params);
xP := Random(Fp2);
KummerPoint_Init(~P, L, [xP, Fp2!1], ~params);

primes_512 := Sort(SetToSequence(SequenceToSet(
    [f[1] : f in Factorization(Ms)]  // Mt=1 for 512-bit, no twist primes
)));

printf "// Real measured strategy costs for the 512-bit factor base.\n";
printf "function BuildRealStrategyCosts_512()\n";
printf "    T := AssociativeArray();\n";
printf "    // l -> <mul_cost, init_cost, eval_cost>\n";

for ell in primes_512 do
    params`ops := rec<OpsRecord | I:=0, A:=0, M:=0, S:=0>;
    KummerPoint_Mul(~res_mul, K, ell, ~params);
    mul_cost := WeightedCost(params`ops`M, params`ops`S, params`ops`A);

    params`ops := rec<OpsRecord | I:=0, A:=0, M:=0, S:=0>;
    KummerLineIsogeny_Velu_Init(~phi, L, K, ell, ~params);
    init_cost := WeightedCost(params`ops`M, params`ops`S, params`ops`A);

    params`ops := rec<OpsRecord | I:=0, A:=0, M:=0, S:=0>;
    KummerLineIsogeny_Velu_Evaluate(~res_eval, phi, P, ~params);
    eval_cost := WeightedCost(params`ops`M, params`ops`S, params`ops`A);

    printf "    T[%o] := <%o, %o, %o>;\n", ell, mul_cost, init_cost, eval_cost;
end for;

printf "    return T;\n";
printf "end function;\n";
