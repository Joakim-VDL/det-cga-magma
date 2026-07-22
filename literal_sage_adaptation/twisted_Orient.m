forward OrientedKummerLine_Init, OrientedKummerLine_IsogenyAndPush, OrientedKummerLine_Twist, OrientedKummerLine_Conjugate,
    OrientedKummerLine_Curve, OrientedKummerLine_AC, OrientedKummerLine_a, OrientedKummerLine_JInvariant,
    OrientedKummer_to_AffineRepresentation, AffineRepresentation_to_OrientedKummer,
    OrientedKummer_to_ProjectiveRepresentation, ProjectiveRepresentation_to_OrientedKummer,
    aff_cycle_to_proj_cycle, proj_cycle_to_aff_cycle, 
    SecretKey_Init, SecretKey_Reduce, SecretKey_Min, keygen,
    IsogenyWalk, group_action_home_base, group_action_square_free, group_action;


OrientedKummerLineRecord := recformat<
    K,  
    Ps, 
    Pt, 
    Qs,
    Qt 
>;

procedure OrientedKummerLine_Init(~self, K, Ps, Pt, Qs, Qt, ~params)
    self := rec<OrientedKummerLineRecord | K := K, Ps := Ps, Pt := Pt, Qs := Qs, Qt := Qt>;
end procedure;

procedure OrientedKummerLine_IsogenyAndPush(~res_OK, ~pi_Z, ~pi_X, self, kernel_point, degree, ~params : check := false, threshold := 250)
    KummerLineIsogeny_Init(~phi, self`K, kernel_point, degree, ~params : check := check, threshold := threshold);
    
    d := degree div 2;
    pi_X := 1;
    pi_Z := 1;
    KummerPoint_Multiples(~K_muls, kernel_point, ~params : limit := d); 
    for i := 1 to d do
        Ki := K_muls[i];
        KummerPoint_XZ(~X, ~Z, Ki, ~params);
        addM(~params, 2);
        pi_X *:= X;
        pi_Z *:= Z;
    end for;
    
    KummerLineIsogeny_Evaluate(~Ps_new, phi, self`Ps, ~params);
    KummerLineIsogeny_Evaluate(~Pt_new, phi, self`Pt, ~params);
    KummerLineIsogeny_Evaluate(~Qs_new, phi, self`Qs, ~params);
    KummerLineIsogeny_Evaluate(~Qt_new, phi, self`Qt, ~params);
    
    OrientedKummerLine_Init(~res_OK, phi`codomain, Ps_new, Pt_new, Qs_new, Qt_new, ~params);
    
    delete phi;
    delete K_muls;
end procedure;

procedure OrientedKummerLine_Twist(~result, self, ~params)
    OrientedKummerLine_Init(~result, self`K, self`Pt, self`Ps, self`Qt, self`Qs, ~params);
end procedure;

procedure OrientedKummerLine_Conjugate(~result, self, ~params)
    OrientedKummerLine_Init(~result, self`K, self`Qs, self`Qt, self`Ps, self`Pt, ~params);
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

procedure OrientedKummerLine_JInvariant(~result, self, ~params)
    result := KummerLine_JInvariant(self`K);
end procedure;

procedure OrientedKummer_to_AffineRepresentation(~A, ~xPs, ~xPt, ~xQs, ~xQt, OK, ~params)
    OrientedKummerLine_a(~A, OK, ~params);
    KummerPoint_x(~xPs, OK`Ps, ~params);
    KummerPoint_x(~xPt, OK`Pt, ~params);
    KummerPoint_x(~xQs, OK`Qs, ~params);
    KummerPoint_x(~xQt, OK`Qt, ~params);
end procedure;

procedure AffineRepresentation_to_OrientedKummer(~OK, A, xPs, xPt, xQs, xQt, base_field, ~params)
    KummerLine_Init(~K_local, [* base_field, [A, 1] *], ~params);
    KummerPoint_Init(~Ps_local, K_local, xPs, ~params);
    KummerPoint_Init(~Pt_local, K_local, xPt, ~params);
    KummerPoint_Init(~Qs_local, K_local, xQs, ~params);
    KummerPoint_Init(~Qt_local, K_local, xQt, ~params);
    OrientedKummerLine_Init(~OK, K_local, Ps_local, Pt_local, Qs_local, Qt_local, ~params);
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

procedure aff_cycle_to_proj_cycle(~out_cycle, aff_cycle)
    r := #aff_cycle;
    out_cycle := [];
    for e := 1 to r do
        entry := aff_cycle[e];
        Append(~out_cycle, [entry[1], 1, entry[2], 1, entry[3], 1, entry[4], 1, entry[5], 1]);
    end for;
end procedure;

procedure proj_cycle_to_aff_cycle(~out_cycle, proj_cycle, ~params)
    r := #proj_cycle;
    out_cycle := [];
    for e := 1 to r do
        entry := proj_cycle[e];
        addI(~params, 5);
        addM(~params, 5);
        Append(~out_cycle, [entry[1]/entry[2], entry[3]/entry[4], entry[5]/entry[6], entry[7]/entry[8], entry[9]/entry[10]]);
    end for;
end procedure;

SecretKeyRecord := recformat<
    straight,
    twist
>;

procedure SecretKey_Init(~self, vec_straight, vec_twist)
    self := rec<SecretKeyRecord | straight := vec_straight, twist := vec_twist>;
end procedure;

procedure SecretKey_Reduce(~sk_out, sk, exps_straight, exps_twist, k)
    vec_s := [Max(Min(sk`straight[i] - k*exps_straight[i], exps_straight[i]), 0) : i in [1..#sk`straight]];
    vec_t := [Max(Min(sk`twist[i] - k*exps_twist[i], exps_twist[i]), 0) : i in [1..#sk`twist]];
    SecretKey_Init(~sk_out, vec_s, vec_t);
end procedure;

procedure SecretKey_Min(~result, self, other)
    vec_s := [self`straight[i] - other`straight[i] : i in [1..#self`straight]];
    vec_t := [self`twist[i] - other`twist[i] : i in [1..#self`twist]];
    SecretKey_Init(~result, vec_s, vec_t);
end procedure;

procedure keygen(~sk, B, exps_straight, exps_twist)
    vec_s := [Random(0, B * exp) : exp in exps_straight];
    vec_t := [Random(0, B * exp) : exp in exps_twist];
    SecretKey_Init(~sk, vec_s, vec_t);
end procedure;

procedure IsogenyWalk(~OK_right_out, ~OK_left_out, ~mult_sq_X, ~mult_sq_Z, OK_right_in, OK_left_in, ells, exps, vec, cofactor, ~params)
    mult_sq_X := cofactor;
    mult_sq_Z := 1;
    n := #ells;
    OK_right := OK_right_in;
    OK_left := OK_left_in;
    curr_cofactor := cofactor;
    for i := 1 to n do
        ell := ells[i]; e := exps[i]; s := vec[i];
        for j := 0 to e - 1 do
            curr_cofactor div:= ell;
            b := (j - s + e) div e;
            R := [OK_right, OK_left];
            OK_right := R[1 + b]; OK_left := R[2 - b];
            KummerPoint_Mul(~kernel, OK_right`Ps, curr_cofactor, ~params);
            OrientedKummerLine_IsogenyAndPush(~OK_right, ~res_pi_Z, ~res_pi_X, OK_right, kernel, ell, ~params);
            addS(~params, 2); addM(~params, 3);
            updates := [res_pi_Z^2, ell * res_pi_X^2];
            mult_sq_X *:= updates[1 + b];
            mult_sq_Z *:= updates[2 - b];
            KummerPoint_Mul(~OK_left_Ps_new, OK_left`Ps, ell, ~params);
            OK_left`Ps := OK_left_Ps_new;
            R := [OK_right, OK_left];
            OK_right := R[1 + b]; OK_left := R[2 - b];
        end for;
    end for;
    OK_right_out := OK_right;
    OK_left_out := OK_left;
end procedure;

procedure group_action_home_base(~proj_out, ~mult_sq_X, ~mult_sq_Z, ~ALX, ~ALZ, proj_home, proj_base, vec_straight, vec_twist, ~params)
    ProjectiveRepresentation_to_OrientedKummer(~OK_home, proj_home[1], proj_home[2], proj_home[3], proj_home[4], proj_home[5], proj_home[6], proj_home[7], proj_home[8], proj_home[9], proj_home[10], params`base_field, ~params);
    ProjectiveRepresentation_to_OrientedKummer(~OK_base, proj_base[1], proj_base[2], proj_base[3], proj_base[4], proj_base[5], proj_base[6], proj_base[7], proj_base[8], proj_base[9], proj_base[10], params`base_field, ~params);
    
    OK_right := OK_home;
    OrientedKummerLine_Conjugate(~OK_left, OK_base, ~params);
    
    IsogenyWalk(~OK_right, ~OK_left, ~mult_sq_X_s, ~mult_sq_Z_s, OK_right, OK_left, params`ells_straight, params`exps_straight, vec_straight, params`Ms, ~params);
    
    OrientedKummerLine_Twist(~OK_right, OK_right, ~params);
    OrientedKummerLine_Twist(~OK_left, OK_left, ~params);
    
    IsogenyWalk(~OK_right, ~OK_left, ~mult_sq_X_t, ~mult_sq_Z_t, OK_right, OK_left, params`ells_twist, params`exps_twist, vec_twist, params`Mt, ~params);

    addM(~params, 2);
    mult_sq_X := mult_sq_X_s * mult_sq_X_t;
    mult_sq_Z := mult_sq_Z_s * mult_sq_Z_t;
    
    OrientedKummerLine_AC(~ARX, ~ARZ, OK_right, ~params);
    OrientedKummerLine_AC(~ALX, ~ALZ, OK_left, ~params);
    
    KummerPoint_XZ(~PsX, ~PsZ, OK_left`Qt, ~params);
    KummerPoint_XZ(~PtX, ~PtZ, OK_left`Qs, ~params);
    KummerPoint_XZ(~QsX, ~QsZ, OK_right`Qt, ~params);
    KummerPoint_XZ(~QtX, ~QtZ, OK_right`Qs, ~params);
    
    proj_out := [ARX, ARZ, PsX, PsZ, PtX, PtZ, QsX, QsZ, QtX, QtZ];
end procedure;

procedure group_action_square_free(~out_cycle, proj_cycle, sk, alpha_sq, ~params)
    r := #proj_cycle;
    mult_sq_total_X := 1;
    mult_sq_total_Z := 1;
    out_cycle := [[] : e in [1..r]];

    ALX_last := 0; ALZ_last := 0;
    for e := 1 to r do
        home := proj_cycle[e];
        base := proj_cycle[(e mod r) + 1];
        group_action_home_base(~out_cycle[e], ~mult_sq_X, ~mult_sq_Z, ~ALX_last, ~ALZ_last, home, base, sk`straight, sk`twist, ~params);
        mult_sq_total_X *:= mult_sq_X;
        mult_sq_total_Z *:= mult_sq_Z;
    end for;

    u_sq_X := mult_sq_total_X;
    addM(~params, 1);
    u_sq_Z := alpha_sq * mult_sq_total_Z;

    last_entry := out_cycle[r];
    ARX := last_entry[1]; ARZ := last_entry[2];
    PsX := last_entry[3]; PsZ := last_entry[4];
    PtX := last_entry[5]; PtZ := last_entry[6];

    addM(~params, 6); addA(~params, 2);
    r_X := u_sq_X * ALZ_last * ARX - u_sq_Z * ALX_last * ARZ;
    r_Z := 3 * u_sq_Z * ALZ_last * ARZ;

    addM(~params, 4); addA(~params, 1);
    out_cycle[r][3] := u_sq_Z * (PsX * r_Z - r_X * PsZ);
    out_cycle[r][4] := u_sq_X * PsZ * r_Z;

    addM(~params, 4); addA(~params, 1);
    out_cycle[r][5] := u_sq_Z * (PtX * r_Z - r_X * PtZ);
    out_cycle[r][6] := u_sq_X * PtZ * r_Z;
end procedure;

procedure group_action(~aff_out, aff_cycle, sk, B, ~params)
    aff_cycle_to_proj_cycle(~proj_cycle, aff_cycle);
    for k := 0 to B - 1 do
        SecretKey_Reduce(~sk_squarefree, sk, params`exps_straight, params`exps_twist, k);
        group_action_square_free(~proj_cycle, proj_cycle, sk_squarefree, params`alpha_sq, ~params);
    end for;
    proj_cycle_to_aff_cycle(~aff_out, proj_cycle, ~params);
end procedure;
