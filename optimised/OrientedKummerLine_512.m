load "optimised/ops_counter.m";
load "optimised/KummerLine.m";
load "optimised/KummerPoint.m";
load "optimised/KummerIsogeny.m";

forward OrientedKummerLine_Init, OrientedKummerLine_IsogenyAndPush,
    OrientedKummerLine_IsogenyAndPush_RetPhi, OrientedKummerLine_Conjugate,
    OrientedKummerLine_Curve, OrientedKummerLine_AC, OrientedKummerLine_a,
    OrientedKummer_to_AffineRepresentation, AffineRepresentation_to_OrientedKummer,
    OrientedKummer_to_ProjectiveRepresentation, ProjectiveRepresentation_to_OrientedKummer,
    aff_cycle_to_proj_cycle, proj_cycle_to_aff_cycle,
    SecretKey_Init, SecretKey_Reduce, SecretKey_Min, keygen,
    ComputeOptimalStrategy, EvaluateStrategyTree_CT,
    IsogenyWalk, group_action_home_base, group_action_square_free, group_action;

OrientedKummerLineRecord := recformat< K, Ps, Qs >;

procedure OrientedKummerLine_Init(~self, K, Ps, Qs, ~params)
    self := rec<OrientedKummerLineRecord | K := K, Ps := Ps, Qs := Qs>;
end procedure;

procedure OrientedKummerLine_IsogenyAndPush(~res_OK, ~pi_Z, ~pi_X, self, kernel_point, degree, ~params)
    KummerLineIsogeny_Velu_Init(~phi, self`K, kernel_point, degree, ~params);

    KummerLineIsogeny_PiProducts(~pi_X, ~pi_Z, phi, ~params);

    KummerLineIsogeny_Velu_Evaluate(~Ps_new, phi, self`Ps, ~params);
    KummerLineIsogeny_Velu_Evaluate(~Qs_new, phi, self`Qs, ~params);
    OrientedKummerLine_Init(~res_OK, phi`codomain, Ps_new, Qs_new, ~params);
    delete phi; 
end procedure;

procedure OrientedKummerLine_IsogenyAndPush_RetPhi(~res_OK, ~pi_Z, ~pi_X, ~phi, self, kernel_point, degree, ~params : push_Ps := true)
    KummerLineIsogeny_Velu_Init(~phi, self`K, kernel_point, degree, ~params);

    KummerLineIsogeny_PiProducts(~pi_X, ~pi_Z, phi, ~params);

    if push_Ps then
        KummerLineIsogeny_Velu_Evaluate(~Ps_new, phi, self`Ps, ~params);
    else
        Ps_new := self`Ps;  
    end if;
    KummerLineIsogeny_Velu_Evaluate(~Qs_new, phi, self`Qs, ~params);
    OrientedKummerLine_Init(~res_OK, phi`codomain, Ps_new, Qs_new, ~params);
end procedure;

procedure OrientedKummerLine_Conjugate(~result, self, ~params)
    OrientedKummerLine_Init(~result, self`K, self`Qs, self`Ps, ~params);
end procedure;

procedure OrientedKummerLine_Curve(~result, self, ~params)
    KummerLine_Curve(~result, self`K, ~params);
end procedure;

procedure OrientedKummerLine_AC(~A, ~C, self, ~params)
    KummerLine_ExtractConstants(~A, ~C, self`K, ~params);
end procedure;

procedure OrientedKummerLine_a(~result, self, ~params)
    KummerLine_a(~result, self`K, ~params);
end procedure;

procedure OrientedKummer_to_AffineRepresentation(~A, ~xPs, ~xQs, OK, ~params)
    OrientedKummerLine_a(~A, OK, ~params);
    KummerPoint_x(~xPs, OK`Ps, ~params);
    KummerPoint_x(~xQs, OK`Qs, ~params);
end procedure;

procedure AffineRepresentation_to_OrientedKummer(~OK, A, xPs, xQs, base_field, ~params)
    KummerLine_Init(~K_local, [* base_field, [A, 1] *], ~params);
    KummerPoint_Init(~Ps_local, K_local, xPs, ~params);
    KummerPoint_Init(~Qs_local, K_local, xQs, ~params);
    OrientedKummerLine_Init(~OK, K_local, Ps_local, Qs_local, ~params);
end procedure;

procedure OrientedKummer_to_ProjectiveRepresentation(~out, OK, ~params)
    OrientedKummerLine_AC(~AX, ~AZ, OK, ~params);
    KummerPoint_XZ(~PsX, ~PsZ, OK`Ps, ~params);
    KummerPoint_XZ(~QsX, ~QsZ, OK`Qs, ~params);
    out := [AX, AZ, PsX, PsZ, QsX, QsZ];
end procedure;

procedure ProjectiveRepresentation_to_OrientedKummer(~OK, AX, AZ, PsX, PsZ, QsX, QsZ, base_field, ~params)
    KummerLine_Init(~K_local, [* base_field, [AX, AZ] *], ~params);
    KummerPoint_Init(~Ps_local, K_local, [PsX, PsZ], ~params);
    KummerPoint_Init(~Qs_local, K_local, [QsX, QsZ], ~params);
    OrientedKummerLine_Init(~OK, K_local, Ps_local, Qs_local, ~params);
end procedure;

procedure aff_cycle_to_proj_cycle(~out_cycle, aff_cycle, ~params)
    r := #aff_cycle; out_cycle := [];
    F := params`base_field;
    for e := 1 to r do
        entry := aff_cycle[e];
        Append(~out_cycle, [entry[1], F!1, entry[2], F!1, entry[3], F!1]);
    end for;
end procedure;

procedure proj_cycle_to_aff_cycle(~out_cycle, proj_cycle, ~params)
    r := #proj_cycle; out_cycle := [];
    denoms := [];
    for e := 1 to r do
        entry := proj_cycle[e];
        Append(~denoms, entry[2]); 
        Append(~denoms, entry[4]); 
        Append(~denoms, entry[6]); 
    end for;
    BatchInversion(~inverses, denoms, ~params);
    for e := 1 to r do
        entry := proj_cycle[e]; inv_idx := (e-1)*3 + 1;
        f_mul(~A_val,   entry[1], inverses[inv_idx],   ~params);
        f_mul(~xPs_val, entry[3], inverses[inv_idx+1], ~params);
        f_mul(~xQs_val, entry[5], inverses[inv_idx+2], ~params);
        Append(~out_cycle, [* A_val, xPs_val, xQs_val *]);
    end for;
end procedure;

SecretKeyRecord := recformat< straight >;

procedure SecretKey_Init(~self, vec_straight)
    self := rec<SecretKeyRecord | straight := vec_straight>;
end procedure;

procedure SecretKey_Reduce(~sk_out, sk, exps_straight, k)
    vec_red := [Max(Min(sk`straight[i] - k*exps_straight[i], exps_straight[i]), 0) : i in [1..#sk`straight]];
    SecretKey_Init(~sk_out, vec_red);
end procedure;

procedure SecretKey_Min(~result, self, other)
    vec := [self`straight[i] - other`straight[i] : i in [1..#self`straight]];
    SecretKey_Init(~result, vec);
end procedure;

procedure keygen(~sk, B, exps_straight)
    vec := [Random(0, B * exp) : exp in exps_straight];
    SecretKey_Init(~sk, vec);
end procedure;

load "optimised/strategy_costs_512.m";

function ComputeOptimalStrategy(ells : leaf_discount := true)
    n := #ells;
    if n le 1 then return []; end if;

    C_xMUL2 := [];   
    C_xMUL1 := [];   
    C_xEVAL := [];

    for i := 1 to n do
        l := ells[i];
        if IsDefined(RealStrategyCosts512, l) then
            entry := RealStrategyCosts512[l];
            mul_cost := entry[1];
            eval_cost := entry[3];
        else
            l2 := l - 1;
            while l2 ge 2 and not IsDefined(RealStrategyCosts512, l2) do
                l2 -:= 1;
            end while;
            if l2 lt 2 then
                l2 := l + 1;
                while l2 le 10*l and not IsDefined(RealStrategyCosts512, l2) do
                    l2 +:= 1;
                end while;
                error if l2 gt 10*l,
                    "ComputeOptimalStrategy: RealStrategyCosts512 has no usable entries; regenerate strategy_costs_512.m";
            end if;
            entry := RealStrategyCosts512[l2];
            mul_cost  := entry[1] * Log(1.0*l) / Log(1.0*l2);
            eval_cost := entry[3] * Sqrt(1.0*l) / Sqrt(1.0*l2);
        end if;
        Append(~C_xMUL2, 2.0 * mul_cost);
        Append(~C_xMUL1, mul_cost);
        Append(~C_xEVAL, eval_cost + mul_cost);
    end for;

    C := [ [ 0.0 : i in [1..n] ] : len in [1..n] ];
    S := [ [ 0 : i in [1..n] ] : len in [1..n] ];

    for len := 2 to n do
        for i := 1 to n - len + 1 do
            min_cost := 1e100;
            best_b := 1;
            for b := 1 to len - 1 do
                single := leaf_discount and (len - b eq 1);
                cost_mul := 0.0;
                for k := i to i + b - 1 do
                    cost_mul +:= single select C_xMUL1[k] else C_xMUL2[k];
                end for;

                cost_eval := 0.0;
                for k := i + b to i + len - 1 do cost_eval +:= C_xEVAL[k]; end for;

                cost := C[b][i] + C[len - b][i + b] + cost_mul + cost_eval;
                if cost lt min_cost then
                    min_cost := cost;
                    best_b := b;
                end if;
            end for;
            C[len][i] := min_cost;
            S[len][i] := best_b;
        end for;
    end for;

    strategy := [];
    procedure build_strategy(~strat, len, i)
        if len le 1 then return; end if;
        k := S[len][i];
        Append(~strat, k);
        build_strategy(~strat, len - k, i + k);
        build_strategy(~strat, k, i);
    end procedure;
    build_strategy(~strategy, n, 1);

    return strategy;
end function;

procedure EvaluateStrategyTree_CT(~OK_R_out, ~OK_L_out, ~all_res_Z, ~all_res_X, OK_R_in, OK_L_in, flat_ells, flat_b, strategy, ~params : push_Ps := true, leaf_skip := true)
    pts_R := [OK_R_in`Ps];
    pts_L := [OK_L_in`Ps];
    indices := [1];
    OK_R_curr := OK_R_in; OK_L_curr := OK_L_in;
    k_strat := 1; n := #flat_ells;

    for i := 1 to n do
        idx_i := n - i + 1;      
        b := flat_b[idx_i];      

        while indices[#indices] le n - i do
            Append(~pts_R, pts_R[#pts_R]);
            Append(~pts_L, pts_L[#pts_L]);
            m := strategy[k_strat]; k_strat +:= 1;

            final_segment := leaf_skip and ((indices[#indices] + m) gt (n - i));

            for j := 1 to m do
                idx := indices[#indices] + j - 1;
                ell := flat_ells[idx];
                if (not final_segment) or (b eq 0) then
                    KummerPoint_Mul(~new_pt_R, pts_R[#pts_R], ell, ~params);
                    pts_R[#pts_R] := new_pt_R;
                end if;
                if (not final_segment) or (b eq 1) then
                    KummerPoint_Mul(~new_pt_L, pts_L[#pts_L], ell, ~params);
                    pts_L[#pts_L] := new_pt_L;
                end if;
            end for;
            Append(~indices, indices[#indices] + m);
        end while;

        kernel_R := pts_R[#pts_R]; kernel_L := pts_L[#pts_L];
        Prune(~pts_R); Prune(~pts_L);
        idx := indices[#indices]; Prune(~indices);

        error if idx ne idx_i, "EvaluateStrategyTree_CT: strategy invariant broken (popped idx <> n-i+1)";

        ell := flat_ells[idx];
        R_OK := [OK_R_curr, OK_L_curr];
        active_OK := R_OK[1 + b]; inactive_OK := R_OK[2 - b];
        active_kernel := [kernel_R, kernel_L][1 + b];

        OrientedKummerLine_IsogenyAndPush_RetPhi(~active_OK_new, ~res_Z, ~res_X, ~phi, active_OK, active_kernel, ell, ~params : push_Ps := push_Ps);

        active_pts_new := []; inactive_pts_new := [];
        for j := 1 to #pts_R do
            active_pt  := [pts_R[j], pts_L[j]][1 + b];
            inactive_pt := [pts_R[j], pts_L[j]][2 - b];
            KummerLineIsogeny_Velu_Evaluate(~new_active_pt, phi, active_pt, ~params);
            new_active_pt`parent := active_OK_new`K;
            Append(~active_pts_new, new_active_pt);
            KummerPoint_Mul(~new_inactive_pt, inactive_pt, ell, ~params);
            Append(~inactive_pts_new, new_inactive_pt);
        end for;
        delete phi;

        R_OK_next := [active_OK_new, inactive_OK];
        OK_R_curr := R_OK_next[1 + b]; OK_L_curr := R_OK_next[2 - b];

        pts_R := []; pts_L := [];
        for j := 1 to #active_pts_new do
            Append(~pts_R, [active_pts_new[j],   inactive_pts_new[j]][1 + b]);
            Append(~pts_L, [active_pts_new[j],   inactive_pts_new[j]][2 - b]);
        end for;

        all_res_Z[idx] := res_Z;
        all_res_X[idx] := res_X;
    end for;

    OK_R_out := OK_R_curr; OK_L_out := OK_L_curr;
end procedure;

procedure IsogenyWalk(~OK_right_out, ~OK_left_out, ~mult_sq_X, ~mult_sq_Z, OK_right_in, OK_left_in, ells, exps, vec, cofactor, ~params : push_Ps := false, leaf_skip := true)
    flat_ells := []; flat_b := [];
    for i := 1 to #ells do
        ell := ells[i]; e := exps[i]; s := vec[i];
        for j := 0 to e - 1 do
            Append(~flat_ells, ell);
            Append(~flat_b, (j - s + e) div e);
        end for;
    end for;
    Reverse(~flat_ells); Reverse(~flat_b);

    strategy := ComputeOptimalStrategy(flat_ells : leaf_discount := leaf_skip);
    F := params`base_field;
    all_res_Z := [F!0 : i in [1..#flat_ells]];
    all_res_X := [F!0 : i in [1..#flat_ells]];

    EvaluateStrategyTree_CT(~OK_right_out, ~OK_left_out, ~all_res_Z, ~all_res_X, OK_right_in, OK_left_in, flat_ells, flat_b, strategy, ~params : push_Ps := push_Ps, leaf_skip := leaf_skip);

    mult_sq_X := F ! cofactor;
    mult_sq_Z := F ! 1;

    for k := 1 to #flat_ells do
        ell := flat_ells[k]; b := flat_b[k];
        res_pi_Z := all_res_Z[k]; res_pi_X := all_res_X[k];
        f_sqr(~X_fac, res_pi_Z, ~params);
        f_sqr(~Z_fac, res_pi_X, ~params);
        f_mul(~Z_fac_ell, F!ell, Z_fac, ~params);
        updates_X := [X_fac,     Z_fac_ell];
        updates_Z := [Z_fac_ell, X_fac    ];
        f_mul(~mult_sq_X, mult_sq_X, updates_X[1 + b], ~params);
        f_mul(~mult_sq_Z, mult_sq_Z, updates_Z[1 + b], ~params);
    end for;
end procedure;

procedure group_action_home_base(~proj_out, ~mult_sq_X, ~mult_sq_Z, ~ALX, ~ALZ, proj_home, proj_base, vec_straight, ~params : legacy := false)
    ProjectiveRepresentation_to_OrientedKummer(~OK_home, proj_home[1], proj_home[2], proj_home[3], proj_home[4], proj_home[5], proj_home[6], params`base_field, ~params);
    ProjectiveRepresentation_to_OrientedKummer(~OK_base, proj_base[1], proj_base[2], proj_base[3], proj_base[4], proj_base[5], proj_base[6], params`base_field, ~params);

    OK_right_in := OK_home;
    OrientedKummerLine_Conjugate(~OK_left_in, OK_base, ~params);
    IsogenyWalk(~OK_right, ~OK_left, ~mult_sq_X, ~mult_sq_Z, OK_right_in, OK_left_in, params`ells_straight, params`exps_straight, vec_straight, params`Ms, ~params : push_Ps := legacy, leaf_skip := not legacy);

    OrientedKummerLine_AC(~ARX, ~ARZ, OK_right, ~params);
    OrientedKummerLine_AC(~ALX, ~ALZ, OK_left,  ~params);
    KummerPoint_XZ(~PsX, ~PsZ, OK_left`Qs,  ~params);
    KummerPoint_XZ(~QsX, ~QsZ, OK_right`Qs, ~params);
    proj_out := [ARX, ARZ, PsX, PsZ, QsX, QsZ];
end procedure;

procedure group_action_square_free(~out_cycle, proj_cycle, sk, alpha_sq, ~params : legacy := false)
    r := #proj_cycle; F := params`base_field;
    mult_sq_total_X := F!1; mult_sq_total_Z := F!1;
    ALX_last := F!0; ALZ_last := F!0;
    out_cycle := [];

    for e := 1 to r do
        home := proj_cycle[e]; base := proj_cycle[(e mod r) + 1];
        group_action_home_base(~entry_out, ~mult_sq_X, ~mult_sq_Z, ~ALX_last, ~ALZ_last, home, base, sk`straight, ~params : legacy := legacy);
        Append(~out_cycle, entry_out);
        f_mul(~mult_sq_total_X, mult_sq_total_X, mult_sq_X, ~params);
        f_mul(~mult_sq_total_Z, mult_sq_total_Z, mult_sq_Z, ~params);
    end for;

    f_mul(~u_sq_Z, alpha_sq, mult_sq_total_Z, ~params);
    u_sq_X := mult_sq_total_X;

    entry := out_cycle[r];
    ARX := entry[1]; ARZ := entry[2]; PsX := entry[3]; PsZ := entry[4];

    f_mul(~t0, u_sq_X, ALZ_last, ~params); f_mul(~t0, t0, ARX, ~params);
    f_mul(~t1, u_sq_Z, ALX_last, ~params); f_mul(~t1, t1, ARZ, ~params);
    f_sub(~r_X, t0, t1, ~params);

    f_mul(~t1b, u_sq_Z, ALZ_last, ~params); f_mul(~t1b, t1b, ARZ, ~params);
    f_add(~r_Z, t1b, t1b, ~params); f_add(~r_Z, r_Z, t1b, ~params);

    if r_Z eq F!0 then
        entry[3] := PsX; entry[4] := PsZ;
    else
        f_mul(~t2, PsX, r_Z, ~params); f_mul(~t3, r_X, PsZ, ~params);
        f_sub(~t4, t2, t3, ~params); f_mul(~new_PsX, u_sq_Z, t4, ~params);
        f_mul(~t5, u_sq_X, PsZ, ~params); f_mul(~new_PsZ, t5, r_Z, ~params);
        entry[3] := new_PsX; entry[4] := new_PsZ;
    end if;
    out_cycle[r] := entry;
end procedure;

procedure group_action(~aff_out, aff_cycle, sk, B, ~params : legacy := false)
    aff_cycle_to_proj_cycle(~proj_cycle, aff_cycle, ~params);
    for k := 0 to B - 1 do
        SecretKey_Reduce(~sk_squarefree, sk, params`exps_straight, k);
        group_action_square_free(~proj_cycle_new, proj_cycle, sk_squarefree, params`alpha_sq, ~params : legacy := legacy);
        proj_cycle := proj_cycle_new;
    end for;
    proj_cycle_to_aff_cycle(~aff_out, proj_cycle, ~params);
end procedure;

    procedure group_action_square_free_pruned(~out_cycle, proj_cycle, sk, alpha_sq, remaining, ~params)
    r := #proj_cycle; F := params`base_field;
    mult_sq_total_X := F!1; mult_sq_total_Z := F!1;
    ALX_last := F!0; ALZ_last := F!0;
    out_cycle := proj_cycle; 

    for e := 1 to remaining do
        home := proj_cycle[e]; base := proj_cycle[(e mod r) + 1];
        group_action_home_base(~entry_out, ~mult_sq_X, ~mult_sq_Z, ~ALX_last, ~ALZ_last, home, base, sk`straight, ~params);
        out_cycle[e] := entry_out;
        f_mul(~mult_sq_total_X, mult_sq_total_X, mult_sq_X, ~params);
        f_mul(~mult_sq_total_Z, mult_sq_total_Z, mult_sq_Z, ~params);
    end for;

    f_mul(~u_sq_Z, alpha_sq, mult_sq_total_Z, ~params);
    u_sq_X := mult_sq_total_X;

    entry := out_cycle[remaining];
    ARX := entry[1]; ARZ := entry[2]; PsX := entry[3]; PsZ := entry[4];

    f_mul(~t0, u_sq_X, ALZ_last, ~params); f_mul(~t0, t0, ARX, ~params);
    f_mul(~t1, u_sq_Z, ALX_last, ~params); f_mul(~t1, t1, ARZ, ~params);
    f_sub(~r_X, t0, t1, ~params);

    f_mul(~t1b, u_sq_Z, ALZ_last, ~params); f_mul(~t1b, t1b, ARZ, ~params);
    f_add(~r_Z, t1b, t1b, ~params); f_add(~r_Z, r_Z, t1b, ~params);

    if r_Z eq F!0 then
        entry[3] := PsX; entry[4] := PsZ;
    else
        f_mul(~t2, PsX, r_Z, ~params); f_mul(~t3, r_X, PsZ, ~params);
        f_sub(~t4, t2, t3, ~params); f_mul(~new_PsX, u_sq_Z, t4, ~params);
        f_mul(~t5, u_sq_X, PsZ, ~params); f_mul(~new_PsZ, t5, r_Z, ~params);
        entry[3] := new_PsX; entry[4] := new_PsZ;
    end if;
    out_cycle[remaining] := entry;
end procedure;

procedure group_action_pruned(~aff_out, aff_cycle, sk, B, ~params)
    r := #aff_cycle;
    aff_cycle_to_proj_cycle(~proj_cycle, aff_cycle, ~params);

    prune_start := B - r; 
    for k := 0 to B - 1 do
        SecretKey_Reduce(~sk_squarefree, sk, params`exps_straight, k);
        if k lt prune_start then
            group_action_square_free(~proj_cycle_new, proj_cycle, sk_squarefree, params`alpha_sq, ~params);
        else
            remaining := Min(r, B - k);
            group_action_square_free_pruned(~proj_cycle_new, proj_cycle, sk_squarefree, params`alpha_sq, remaining, ~params);
        end if;
        proj_cycle := proj_cycle_new;
    end for;

    proj_cycle_to_aff_cycle(~aff_out, proj_cycle, ~params);
end procedure;
