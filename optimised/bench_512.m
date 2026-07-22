load "optimised/ops_counter.m";
load "optimised/KummerLine.m";
load "optimised/KummerPoint.m";
load "optimised/KummerIsogeny.m";
load "optimised/OrientedKummerLine_512.m";
load "optimised/data_512.m";

Fp := GF(p);
Fp2<i> := ExtensionField<Fp, X | X^2 + 1>;

if #sigma eq 4 then
    a := sigma[1]; b := sigma[2]; c := sigma[3]; d := sigma[4];
    alpha_re := (Fp!(2*a + d)) / 2;
    alpha_im := (Fp!(2*b + c)) / 2;
    alpha := Fp2 ! [alpha_re, alpha_im];
else
    alpha := Fp2 ! [Fp!(trace/2), 0];
end if;
alpha_sq := alpha^2;

aff_base_cycle := [];
for entry in base_cycle do
    A_val   := Fp2 ! [entry[1][1], entry[1][2]];
    xPs_val := Fp2 ! [entry[2][1], entry[2][2]];
    xQs_val := Fp2 ! [entry[4][1], entry[4][2]]; 
    Append(~aff_base_cycle, [* A_val, xPs_val, xQs_val *]);
end for;

params := rec<ParamsRecord | >;
params`p := p;
params`r := r;
params`trace := trace;
params`Ms := Ms;
params`Mt := Mt;
params`base_field := Fp2;
params`alpha_sq := alpha_sq;
params`ops := rec<OpsRecord | I:=0, A:=0, M:=0, S:=0>;

fact_s := Factorization(Ms);
params`ells_straight := [f[1] : f in fact_s];
params`exps_straight := [f[2] : f in fact_s];
params`base_cycle := aff_base_cycle;

function exps_to_B(exps_s, lmbda)
    B := 0;
    while true do
        B +:= 1;
        key_space_size := &+([0.0] cat [Log(2, B * e + 1.0) : e in exps_s]);
        if key_space_size gt lmbda then break; end if;
    end while;
    return B;
end function;

lmbda := 256;
B := exps_to_B(params`exps_straight, lmbda);
printf "Calculated B = %o for lambda = %o\n", B, lmbda;

timings := [];
num_iters := 5;

printf "Starting benchmark (%o iterations)...\n", num_iters;

for i := 1 to num_iters do
    printf "Iteration %o...\n", i;

    keygen(~sk_alice, B, params`exps_straight);
    keygen(~sk_bob,   B, params`exps_straight);

    printf "  Step 1: Alice PK Generation\n";
    ResetStats(~params);
    t0 := Cputime();
    group_action(~pk_alice, params`base_cycle, sk_alice, B, ~params);
    t1 := Cputime(t0);
    printf "    Time: %o s\n", t1;
    PrintStats(~params);
    Append(~timings, t1);

    printf "  Step 2: Bob PK Generation\n";
    ResetStats(~params);
    t0 := Cputime();
    group_action(~pk_bob, params`base_cycle, sk_bob, B, ~params);
    t1 := Cputime(t0);
    printf "    Time: %o s\n", t1;
    PrintStats(~params);
    Append(~timings, t1);

    printf "  Step 3: Alice Shared Secret\n";
    ResetStats(~params);
    t0 := Cputime();
    group_action_pruned(~ss_alice, pk_bob, sk_alice, B, ~params);
    t1 := Cputime(t0);
    printf "    Time: %o s\n", t1;
    PrintStats(~params);
    Append(~timings, t1);

    printf "  Step 4: Bob Shared Secret\n";
    ResetStats(~params);
    t0 := Cputime();
    group_action_pruned(~ss_bob, pk_alice, sk_bob, B, ~params);
    t1 := Cputime(t0);
    printf "    Time: %o s\n", t1;
    PrintStats(~params);
    Append(~timings, t1);

    if ss_alice[1][1] eq ss_bob[1][1] then
        printf "  Shared secret verified for iteration %o.\n", i;
        printf "  Secret A coefficient: %o\n\n", ss_alice[1][1];
    else
        printf "  ERROR: Shared secrets do not match!\n";
        printf "  Alice's A: %o\n", ss_alice[1][1];
        printf "  Bob's A:   %o\n\n", ss_bob[1][1];
    end if;
end for;

function Median(S)
    if #S eq 0 then return 0.0; end if;
    Sorted := Sort(S);
    n := #Sorted;
    if n mod 2 eq 1 then
        return RealField() ! Sorted[(n+1) div 2];
    else
        return (Sorted[n div 2] + Sorted[n div 2 + 1]) / 2.0;
    end if;
end function;

med := Median(timings);
printf "Timing results for a 512-bit group action (new isogeny infrastructure)\n";
printf "The median is %o s\n", med;
