load "optimised/ops_counter.m";
load "optimised/KummerLine.m";
load "optimised/KummerPoint.m";
load "optimised/KummerIsogeny.m";

forward OrientedKummerLine_Init, OrientedKummerLine_IsogenyAndPush, OrientedKummerLine_IsogenyAndPush_RetPhi, OrientedKummerLine_Twist, OrientedKummerLine_Conjugate,
    OrientedKummerLine_AC,
    OrientedKummer_to_ProjectiveRepresentation, ProjectiveRepresentation_to_OrientedKummer,
    aff_cycle_to_proj_cycle, proj_cycle_to_aff_cycle,
    SecretKey_Init, SecretKey_Reduce, keygen,
    ComputeOptimalStrategy, EvaluateStrategyTree_CT, IsogenyWalk, group_action_home_base, group_action_square_free, group_action;

OrientedKummerLineRecord := recformat< K, Ps, Pt, Qs, Qt >;

procedure OrientedKummerLine_Init(~self, K, Ps, Pt, Qs, Qt, ~params)
    self := rec<OrientedKummerLineRecord | K := K, Ps := Ps, Pt := Pt, Qs := Qs, Qt := Qt>;
end procedure;

procedure OrientedKummerLine_IsogenyAndPush(~res_OK, ~pi_Z, ~pi_X, self, kernel_point, degree, ~params)
    KummerLineIsogeny_Velu_Init(~phi, self`K, kernel_point, degree, ~params);
    
    KummerLineIsogeny_PiProducts(~pi_X, ~pi_Z, phi, ~params);
    
    KummerLineIsogeny_Velu_Evaluate(~Ps_new, phi, self`Ps, ~params);
    KummerLineIsogeny_Velu_Evaluate(~Pt_new, phi, self`Pt, ~params);
    KummerLineIsogeny_Velu_Evaluate(~Qs_new, phi, self`Qs, ~params);
    KummerLineIsogeny_Velu_Evaluate(~Qt_new, phi, self`Qt, ~params);
    
    OrientedKummerLine_Init(~res_OK, phi`codomain, Ps_new, Pt_new, Qs_new, Qt_new, ~params);
end procedure;

procedure OrientedKummerLine_Twist(~result, self, ~params)
    OrientedKummerLine_Init(~result, self`K, self`Pt, self`Ps, self`Qt, self`Qs, ~params);
end procedure;

procedure OrientedKummerLine_Conjugate(~result, self, ~params)
    OrientedKummerLine_Init(~result, self`K, self`Qs, self`Qt, self`Ps, self`Pt, ~params);
end procedure;

procedure OrientedKummerLine_AC(~A, ~C, self, ~params)
    KummerLine_ExtractConstants(~A, ~C, self`K, ~params);
end procedure;

procedure proj_cycle_to_aff_cycle(~out_cycle, proj_cycle, ~params)
    r := #proj_cycle; out_cycle := [];
    denoms := [];
    for e := 1 to r do
        Append(~denoms, proj_cycle[e][2]); 
        Append(~denoms, proj_cycle[e][4]); 
        Append(~denoms, proj_cycle[e][6]); 
        Append(~denoms, proj_cycle[e][8]); 
        Append(~denoms, proj_cycle[e][10]); 
    end for;
    BatchInversion(~inverses, denoms, ~params);
    for e := 1 to r do
        entry := proj_cycle[e]; inv_idx := (e-1)*5 + 1;
        f_mul(~A_val,   entry[1], inverses[inv_idx],   ~params);
        f_mul(~xPs_val, entry[3], inverses[inv_idx+1], ~params);
        f_mul(~xPt_val, entry[5], inverses[inv_idx+2], ~params);
        f_mul(~xQs_val, entry[7], inverses[inv_idx+3], ~params);
        f_mul(~xQt_val, entry[9], inverses[inv_idx+4], ~params);
        Append(~out_cycle, [A_val, xPs_val, xPt_val, xQs_val, xQt_val]);
    end for;
end procedure;

SecretKeyRecord := recformat< straight, twist >;
procedure SecretKey_Init(~self, vec_straight, vec_twist)
    self := rec<SecretKeyRecord | straight := vec_straight, twist := vec_twist>;
end procedure;
procedure SecretKey_Reduce(~sk_out, sk, exps_straight, exps_twist, k)
    vec_s := [Max(Min(sk`straight[i] - k*exps_straight[i], exps_straight[i]), 0) : i in [1..#sk`straight]];
    vec_t := [Max(Min(sk`twist[i] - k*exps_twist[i], exps_twist[i]), 0) : i in [1..#sk`twist]];
    SecretKey_Init(~sk_out, vec_s, vec_t);
end procedure;
procedure keygen(~sk, B, exps_straight, exps_twist)
    vec_s := [Random(0, B * exp) : exp in exps_straight];
    vec_t := [Random(0, B * exp) : exp in exps_twist];
    SecretKey_Init(~sk, vec_s, vec_t);
end procedure;

procedure OrientedKummerLine_IsogenyAndPush_RetPhi(~res_OK, ~pi_Z, ~pi_X, ~phi, self, kernel_point, degree, ~params : push_Ps := true, push_Pt := true)
    KummerLineIsogeny_Velu_Init(~phi, self`K, kernel_point, degree, ~params);
    
    KummerLineIsogeny_PiProducts(~pi_X, ~pi_Z, phi, ~params);
    
    if push_Ps then
        KummerLineIsogeny_Velu_Evaluate(~Ps_new, phi, self`Ps, ~params);
    else
        Ps_new := self`Ps;  
    end if;
    if push_Pt then
        KummerLineIsogeny_Velu_Evaluate(~Pt_new, phi, self`Pt, ~params);
    else
        Pt_new := self`Pt;  
    end if;
    KummerLineIsogeny_Velu_Evaluate(~Qs_new, phi, self`Qs, ~params);
    KummerLineIsogeny_Velu_Evaluate(~Qt_new, phi, self`Qt, ~params);
    
    OrientedKummerLine_Init(~res_OK, phi`codomain, Ps_new, Pt_new, Qs_new, Qt_new, ~params);
end procedure;


load "optimised/strategy_costs_256.m";

function ComputeOptimalStrategy(ells : leaf_discount := true)
    n := #ells;
    if n le 1 then return []; end if;

    C_xMUL2 := [];  
    C_xMUL1 := [];  
    C_xEVAL := [];

    for i := 1 to n do
        l := ells[i];
        entry := RealStrategyCosts256[l];
        mul_cost := entry[1];
        eval_cost := entry[3];
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


procedure EvaluateStrategyTree_CT(~OK_R_out, ~OK_L_out, ~all_res_Z, ~all_res_X, OK_R_in, OK_L_in, flat_ells, flat_b, strategy, ~params : push_Ps := true, push_Pt := true, leaf_skip := true)
    pts_R := [OK_R_in`Ps];
    pts_L := [OK_L_in`Ps];
    indices := [1];
    
    OK_R_curr := OK_R_in;
    OK_L_curr := OK_L_in;
    
    k_strat := 1;
    n := #flat_ells;
    
    for i := 1 to n do
        idx_i := n - i + 1;      
        b := flat_b[idx_i];     
        
        while indices[#indices] le n - i do
            Append(~pts_R, pts_R[#pts_R]);
            Append(~pts_L, pts_L[#pts_L]);
            
            m := strategy[k_strat];
            k_strat +:= 1;
            
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
        
        kernel_R := pts_R[#pts_R];
        kernel_L := pts_L[#pts_L];
        Prune(~pts_R); Prune(~pts_L);
        idx := indices[#indices];
        Prune(~indices);
        
        error if idx ne idx_i, "EvaluateStrategyTree_CT: strategy invariant broken (popped idx <> n-i+1)";
        
        ell := flat_ells[idx];
        
        R_OK := [OK_R_curr, OK_L_curr];
        active_OK := R_OK[1 + b]; inactive_OK := R_OK[2 - b];
        
        R_kernel := [kernel_R, kernel_L];
        active_kernel := R_kernel[1 + b];
        
        OrientedKummerLine_IsogenyAndPush_RetPhi(~active_OK_new, ~res_Z, ~res_X, ~phi, active_OK, active_kernel, ell, ~params : push_Ps := push_Ps, push_Pt := push_Pt);
        
        active_pts_new := [];
        inactive_pts_new := [];
        for j := 1 to #pts_R do
            R_pt := [pts_R[j], pts_L[j]];
            active_pt := R_pt[1 + b]; inactive_pt := R_pt[2 - b];
            
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
            R_pt_next := [active_pts_new[j], inactive_pts_new[j]];
            Append(~pts_R, R_pt_next[1 + b]);
            Append(~pts_L, R_pt_next[2 - b]);
        end for;
        
        all_res_Z[idx] := res_Z;
        all_res_X[idx] := res_X;
    end for;
    
    OK_R_out := OK_R_curr;
    OK_L_out := OK_L_curr;
end procedure;

procedure IsogenyWalk(~OK_right_out, ~OK_left_out, ~mult_sq_X, ~mult_sq_Z, OK_right_in, OK_left_in, ells, exps, vec, cofactor, ~params : push_Ps := false, push_Pt := true, leaf_skip := true)
    flat_ells := [];
    flat_b := [];
    for i := 1 to #ells do
        ell := ells[i]; e := exps[i]; s := vec[i];
        for j := 0 to e - 1 do
            b := (j - s + e) div e;
            Append(~flat_ells, ell);
            Append(~flat_b, b);
        end for;
    end for;
    
    Reverse(~flat_ells);
    Reverse(~flat_b);
    
    strategy := ComputeOptimalStrategy(flat_ells : leaf_discount := leaf_skip);
    
    all_res_Z := [params`base_field!0 : i in [1..#flat_ells]];
    all_res_X := [params`base_field!0 : i in [1..#flat_ells]];
    
    EvaluateStrategyTree_CT(~OK_right_out, ~OK_left_out, ~all_res_Z, ~all_res_X, OK_right_in, OK_left_in, flat_ells, flat_b, strategy, ~params : push_Ps := push_Ps, push_Pt := push_Pt, leaf_skip := leaf_skip);
    
    mult_sq_X := params`base_field ! cofactor;
    mult_sq_Z := params`base_field ! 1;
    
    for k := 1 to #flat_ells do
        ell := flat_ells[k];
        b := flat_b[k];
        res_pi_Z := all_res_Z[k];
        res_pi_X := all_res_X[k];
        
        f_sqr(~X_fac, res_pi_Z, ~params);
        f_sqr(~Z_fac, res_pi_X, ~params);
        f_mul(~Z_fac_ell, ell, Z_fac, ~params);
        
        updates := [X_fac, Z_fac_ell];
        f_mul(~mult_sq_X, mult_sq_X, updates[1 + b], ~params);
        f_mul(~mult_sq_Z, mult_sq_Z, updates[2 - b], ~params);
    end for;
end procedure;


procedure group_action_home_base(~proj_out, ~mult_sq_X, ~mult_sq_Z, ~ALX, ~ALZ, proj_home, proj_base, vec_straight, vec_twist, ~params : legacy := false)
    ProjectiveRepresentation_to_OrientedKummer(~OK_home, proj_home[1], proj_home[2], proj_home[3], proj_home[4], proj_home[5], proj_home[6], proj_home[7], proj_home[8], proj_home[9], proj_home[10], params`base_field, ~params);
    ProjectiveRepresentation_to_OrientedKummer(~OK_base, proj_base[1], proj_base[2], proj_base[3], proj_base[4], proj_base[5], proj_base[6], proj_base[7], proj_base[8], proj_base[9], proj_base[10], params`base_field, ~params);
    OK_right := OK_home; OrientedKummerLine_Conjugate(~OK_left, OK_base, ~params);
    IsogenyWalk(~OK_right_new, ~OK_left_new, ~mult_sq_X_s, ~mult_sq_Z_s, OK_right, OK_left, params`ells_straight, params`exps_straight, vec_straight, params`Ms, ~params : push_Ps := legacy, push_Pt := true, leaf_skip := not legacy);
    OK_right := OK_right_new; OK_left := OK_left_new;
    OrientedKummerLine_Twist(~OK_right_new, OK_right, ~params);
    OrientedKummerLine_Twist(~OK_left_new, OK_left, ~params);
    OK_right := OK_right_new; OK_left := OK_left_new;
    IsogenyWalk(~OK_right_new, ~OK_left_new, ~mult_sq_X_t, ~mult_sq_Z_t, OK_right, OK_left, params`ells_twist, params`exps_twist, vec_twist, params`Mt, ~params : push_Ps := legacy, push_Pt := legacy, leaf_skip := not legacy);
    OK_right := OK_right_new; OK_left := OK_left_new;
    f_mul(~mult_sq_X, mult_sq_X_s, mult_sq_X_t, ~params);
    f_mul(~mult_sq_Z, mult_sq_Z_s, mult_sq_Z_t, ~params);
    OrientedKummerLine_AC(~ARX, ~ARZ, OK_right, ~params);
    OrientedKummerLine_AC(~ALX, ~ALZ, OK_left, ~params);
    KummerPoint_XZ(~PsX, ~PsZ, OK_left`Qt, ~params);
    KummerPoint_XZ(~PtX, ~PtZ, OK_left`Qs, ~params);
    KummerPoint_XZ(~QsX, ~QsZ, OK_right`Qt, ~params);
    KummerPoint_XZ(~QtX, ~QtZ, OK_right`Qs, ~params);
    proj_out := [ARX, ARZ, PsX, PsZ, PtX, PtZ, QsX, QsZ, QtX, QtZ];
end procedure;

procedure group_action_square_free(~out_cycle, proj_cycle, sk, alpha_sq, ~params : legacy := false)
    r := #proj_cycle; F := params`base_field;
    mult_sq_total_X := F!1; mult_sq_total_Z := F!1; out_cycle := [];
    ALX_last := F!0; ALZ_last := F!0;
    for e := 1 to r do
        home := proj_cycle[e]; base := proj_cycle[(e mod r) + 1];
        group_action_home_base(~entry_out, ~mult_sq_X, ~mult_sq_Z, ~ALX_last, ~ALZ_last, home, base, sk`straight, sk`twist, ~params : legacy := legacy);
        Append(~out_cycle, entry_out);
        f_mul(~mult_sq_total_X, mult_sq_total_X, mult_sq_X, ~params);
        f_mul(~mult_sq_total_Z, mult_sq_total_Z, mult_sq_Z, ~params);
    end for;
    u_sq_X := mult_sq_total_X;
    f_mul(~u_sq_Z, alpha_sq, mult_sq_total_Z, ~params);
    entry := out_cycle[r];
    ARX := entry[1]; ARZ := entry[2]; PsX := entry[3]; PsZ := entry[4]; PtX := entry[5]; PtZ := entry[6];
    f_mul(~t0, u_sq_X, ALZ_last, ~params); f_mul(~t0, t0, ARX, ~params);
    f_mul(~t1, u_sq_Z, ALX_last, ~params); f_mul(~t1, t1, ARZ, ~params);
    f_sub(~r_X, t0, t1, ~params);
    f_mul(~t1b, u_sq_Z, ALZ_last, ~params); f_mul(~t1b, t1b, ARZ, ~params);
    f_add(~r_Z, t1b, t1b, ~params); f_add(~r_Z, r_Z, t1b, ~params); // r_Z = 3*t1b
    if r_Z eq F!0 then
        entry[3] := PsX; entry[4] := PsZ;
        entry[5] := PtX; entry[6] := PtZ;
    else
        f_mul(~t2, PsX, r_Z, ~params); f_mul(~t3, r_X, PsZ, ~params);
        f_sub(~t4, t2, t3, ~params); f_mul(~new_Ps_X, u_sq_Z, t4, ~params);
        f_mul(~t5, u_sq_X, PsZ, ~params); f_mul(~new_Ps_Z, t5, r_Z, ~params);
        entry[3] := new_Ps_X; entry[4] := new_Ps_Z;
        
        f_mul(~t6, PtX, r_Z, ~params); f_mul(~t7, r_X, PtZ, ~params);
        f_sub(~t8, t6, t7, ~params); f_mul(~new_Pt_X, u_sq_Z, t8, ~params);
        f_mul(~t9, u_sq_X, PtZ, ~params); f_mul(~new_Pt_Z, t9, r_Z, ~params);
        entry[5] := new_Pt_X; entry[6] := new_Pt_Z;
    end if;
    out_cycle[r] := entry;
end procedure;

procedure group_action(~aff_out, aff_cycle, sk, B, ~params : legacy := false)
    aff_cycle_to_proj_cycle(~proj_cycle, aff_cycle, ~params);
    for k := 0 to B - 1 do
        SecretKey_Reduce(~sk_squarefree, sk, params`exps_straight, params`exps_twist, k);
        group_action_square_free(~proj_cycle_new, proj_cycle, sk_squarefree, params`alpha_sq, ~params : legacy := legacy);
        proj_cycle := proj_cycle_new;
    end for;
    proj_cycle_to_aff_cycle(~aff_out, proj_cycle, ~params);
end procedure;

procedure aff_cycle_to_proj_cycle(~out_cycle, aff_cycle, ~params)
    r := #aff_cycle; out_cycle := [];
    for e := 1 to r do
        entry := aff_cycle[e];
        F := params`base_field;
        Append(~out_cycle, [entry[1], F!1, entry[2], F!1, entry[3], F!1, entry[4], F!1, entry[5], F!1]);
    end for;
end procedure;

procedure OrientedKummer_to_ProjectiveRepresentation(~out, OK, ~params)
    OrientedKummerLine_AC(~AX, ~AZ, OK, ~params);
    KummerPoint_XZ(~PsX, ~PsZ, OK`Ps, ~params);
    KummerPoint_XZ(~PtX, ~PtZ, OK`Pt, ~params);
    KummerPoint_XZ(~QsX, ~QsZ, OK`Qs, ~params);
    KummerPoint_XZ(~QtX, ~QtZ, OK`Qt, ~params);
    out := [AX, AZ, PsX, PsZ, PtX, PtZ, QsX, QsZ, QtX, QtZ];
end procedure;

procedure ProjectiveRepresentation_to_OrientedKummer(~OK, AX, AZ, PsX, PsZ, PtX, PtZ, QsX, QsZ, QtX, QtZ, base_field, ~params)
    KummerLine_Init(~K_local, [* base_field, [AX, AZ] *], ~params);
    KummerPoint_Init(~Ps_local, K_local, [PsX, PsZ], ~params);
    KummerPoint_Init(~Pt_local, K_local, [PtX, PtZ], ~params);
    KummerPoint_Init(~Qs_local, K_local, [QsX, QsZ], ~params);
    KummerPoint_Init(~Qt_local, K_local, [QtX, QtZ], ~params);
    OrientedKummerLine_Init(~OK, K_local, Ps_local, Pt_local, Qs_local, Qt_local, ~params);
end procedure;

procedure group_action_square_free_pruned(~out_cycle, proj_cycle, sk, alpha_sq, remaining, ~params)
    r := #proj_cycle; F := params`base_field;
    mult_sq_total_X := F!1; mult_sq_total_Z := F!1;
    ALX_last := F!0; ALZ_last := F!0;
    out_cycle := proj_cycle; 

    for e := 1 to remaining do
        home := proj_cycle[e]; base := proj_cycle[(e mod r) + 1];
        group_action_home_base(~entry_out, ~mult_sq_X, ~mult_sq_Z, ~ALX_last, ~ALZ_last, home, base, sk`straight, sk`twist, ~params);
        out_cycle[e] := entry_out;
        f_mul(~mult_sq_total_X, mult_sq_total_X, mult_sq_X, ~params);
        f_mul(~mult_sq_total_Z, mult_sq_total_Z, mult_sq_Z, ~params);
    end for;

    u_sq_X := mult_sq_total_X;
    f_mul(~u_sq_Z, alpha_sq, mult_sq_total_Z, ~params);

    entry := out_cycle[remaining];
    ARX := entry[1]; ARZ := entry[2]; PsX := entry[3]; PsZ := entry[4]; PtX := entry[5]; PtZ := entry[6];

    f_mul(~t0, u_sq_X, ALZ_last, ~params); f_mul(~t0, t0, ARX, ~params);
    f_mul(~t1, u_sq_Z, ALX_last, ~params); f_mul(~t1, t1, ARZ, ~params);
    f_sub(~r_X, t0, t1, ~params);

    f_mul(~t1b, u_sq_Z, ALZ_last, ~params); f_mul(~t1b, t1b, ARZ, ~params);
    f_add(~r_Z, t1b, t1b, ~params); f_add(~r_Z, r_Z, t1b, ~params);

    if r_Z eq F!0 then
        entry[3] := PsX; entry[4] := PsZ;
        entry[5] := PtX; entry[6] := PtZ;
    else
        f_mul(~t2, PsX, r_Z, ~params); f_mul(~t3, r_X, PsZ, ~params);
        f_sub(~t4, t2, t3, ~params); f_mul(~new_Ps_X, u_sq_Z, t4, ~params);
        f_mul(~t5, u_sq_X, PsZ, ~params); f_mul(~new_Ps_Z, t5, r_Z, ~params);
        entry[3] := new_Ps_X; entry[4] := new_Ps_Z;

        f_mul(~t6, PtX, r_Z, ~params); f_mul(~t7, r_X, PtZ, ~params);
        f_sub(~t8, t6, t7, ~params); f_mul(~new_Pt_X, u_sq_Z, t8, ~params);
        f_mul(~t9, u_sq_X, PtZ, ~params); f_mul(~new_Pt_Z, t9, r_Z, ~params);
        entry[5] := new_Pt_X; entry[6] := new_Pt_Z;
    end if;
    out_cycle[remaining] := entry;
end procedure;

procedure group_action_pruned(~aff_out, aff_cycle, sk, B, ~params)
    r := #aff_cycle;
    aff_cycle_to_proj_cycle(~proj_cycle, aff_cycle, ~params);

    prune_start := B - r; 
    for k := 0 to B - 1 do
        SecretKey_Reduce(~sk_squarefree, sk, params`exps_straight, params`exps_twist, k);
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
