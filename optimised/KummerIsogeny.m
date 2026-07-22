load "optimised/ops_counter.m";
load "optimised/poly_ops_part1.m";
load "optimised/poly_ops_part2.m";
load "optimised/sqrtvelu_mtable.m";
load "optimised/sqrtvelu_tuned_tables.m";


KummerLineIsogenyVeluRecord := recformat<
    degree,
    domain,
    codomain,
    kernel_multiples,
    edwards_constants,
    is_sqrt
>;

procedure KummerLineIsogeny_Normal_Init(~self, domain, kernel, degree, ~params)
    self := rec<KummerLineIsogenyVeluRecord | degree := degree, domain := domain, is_sqrt := false>;
    d := (degree - 1) div 2;
    R := domain`base_ring;

    KummerLine_ExtractConstants(~A, ~C, domain, ~params);

    f_double(~C2, C, ~params);
    f_add(~Aedx, A, C2, ~params);
    f_double(~A24z, C2, ~params);
    f_sub(~Aedz, A, C2, ~params);

    KummerPoint_XZ(~XK, ~ZK, kernel, ~params);
    M := [kernel];
    if d ge 2 then
        KummerPoint_xDBL(~X2, ~Z2, XK, ZK, A, C, ~params);
        KummerPoint_Init(~P2, domain, [X2, Z2], ~params);
        Append(~M, P2);
        for i := 3 to d do
            Xprev := M[i-1]`X; Zprev := M[i-1]`Z;
            Xprev2 := M[i-2]`X; Zprev2 := M[i-2]`Z;
            KummerPoint_xADD(~Xi, ~Zi, Xprev, Zprev, XK, ZK, Xprev2, Zprev2, ~params);
            KummerPoint_Init(~Pi, domain, [Xi, Zi], ~params);
            Append(~M, Pi);
        end for;
    end if;

    diffs := []; sums := [];
    prodx := R!1; prodz := R!1;
    for j := 1 to d do
        f_sub(~dj, M[j]`X, M[j]`Z, ~params);
        f_add(~sj, M[j]`X, M[j]`Z, ~params);
        Append(~diffs, dj); Append(~sums, sj);
        f_mul(~prodx, prodx, dj, ~params);
        f_mul(~prodz, prodz, sj, ~params);
    end for;
    self`kernel_multiples := <diffs, sums>;

    px8 := prodx; pz8 := prodz;
    for i := 1 to 3 do
        f_sqr(~px8, px8, ~params);
        f_sqr(~pz8, pz8, ~params);
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

     f_mul(~AedzFinal, aedzk, px8, ~params);
    f_mul(~AedxFinal, aedxk, pz8, ~params);

    f_add(~newA, AedxFinal, AedzFinal, ~params);
    f_sub(~newC, AedxFinal, AedzFinal, ~params);
    f_double(~newA, newA, ~params);

    KummerLine_Init(~cod, [* R, [newA, newC] *], ~params);
    self`codomain := cod;
end procedure;

procedure KummerLineIsogeny_Normal_Evaluate(~result, self, P, ~params)
    d := (self`degree - 1) div 2;
    diffs := self`kernel_multiples[1];
    sums := self`kernel_multiples[2];
    R := self`domain`base_ring;

    KummerPoint_XZ(~XP, ~ZP, P, ~params);
    f_add(~Psum, XP, ZP, ~params);
    f_sub(~Pdif, XP, ZP, ~params);

    Qx := R!1; Qz := R!1;
    for j := 1 to d do
        f_mul(~t1, diffs[j], Psum, ~params);  
        f_mul(~t0, sums[j], Pdif, ~params);   
        f_add(~facx, t0, t1, ~params);
        f_sub(~facz, t0, t1, ~params);
        f_mul(~Qx, Qx, facx, ~params);
        f_mul(~Qz, Qz, facz, ~params);
    end for;
    f_sqr(~Qx, Qx, ~params);
    f_sqr(~Qz, Qz, ~params);
    f_mul(~newX, XP, Qx, ~params);
    f_mul(~newZ, ZP, Qz, ~params);

    KummerPoint_Init(~result, self`codomain, [newX, newZ], ~params);
end procedure;

procedure KummerLineIsogeny_SqrtVelu_Init(~self, domain, kernel, degree, ~params : bs_override := 0, gs_override := 0)
    self := rec<KummerLineIsogenyVeluRecord | degree := degree, domain := domain, is_sqrt := true>;
    R := domain`base_ring;

    bs := 0; gs := 0;
    if bs_override gt 0 and gs_override gt 0 then
        bs := bs_override; gs := gs_override;
    else
        SqrtVeluSteps(~bs, ~gs, degree);
    end if;

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
    self`codomain := cod;

    self`kernel_multiples := <M, TI, Aprecomp, precomp, bs, gs>;
end procedure;

procedure KummerLineIsogeny_SqrtVelu_Evaluate(~result, self, P, ~params)
    R := self`domain`base_ring;
    M := self`kernel_multiples[1];
    TI := self`kernel_multiples[2];
    Aprecomp := self`kernel_multiples[3];
    precomp := self`kernel_multiples[4];
    bs := self`kernel_multiples[5];
    gs := self`kernel_multiples[6];
    degree := self`degree;

    KummerPoint_XZ(~XP, ~ZP, P, ~params);
    f_add(~Psum, XP, ZP, ~params);
    f_sub(~Pdif, XP, ZP, ~params);

    biquad_precompute_point(~Pprecomp, XP, ZP, ~params);

    TP := [R | 0 : t in [1..3*gs]];
    for j := 0 to gs - 1 do
        biquad_postcompute_point(~outp, Pprecomp, Aprecomp[j+1], ~params); 
        for t := 1 to 3 do TP[3*j + t] := outp[t]; end for;
    end for;
    poly_multiprod2(~TP, gs, 0, ~params);

    flen := 2*gs + 1;
    TPinv := [R | 0 : t in [1..flen]];
    for t := 1 to flen do
        TPinv[t] := TP[flen - t + 1];
    end for;

    P_base := TI[1 .. 2*bs];
    T_tree := TI[2*bs + 1 .. #TI];

    v1 := [R | 0 : t in [1..bs]];
    poly_multieval_postcompute(~v1, bs, TP[1..flen], flen, P_base, T_tree, precomp, ~params);
    Qz := v1[1];
    for t := 2 to bs do f_mul(~Qz, Qz, v1[t], ~params); end for;

    v2 := [R | 0 : t in [1..bs]];
    poly_multieval_postcompute(~v2, bs, TPinv, flen, P_base, T_tree, precomp, ~params);
    Qx := v2[1];
    for t := 2 to bs do f_mul(~Qx, Qx, v2[t], ~params); end for;

    boundpart := (degree - 1) div 2 - 2*bs*gs;
    for i := 0 to boundpart - 1 do
        Xi2, Zi2 := Explode(M[2*i + 2]);
        f_add(~tmp2, Xi2, Zi2, ~params);
        f_sub(~tmp3, Xi2, Zi2, ~params);

        f_mul(~mxp, tmp2, Pdif, ~params);
        f_mul(~mzp, tmp3, Psum, ~params);

        f_add(~tsum, mxp, mzp, ~params);
        f_sub(~tdif, mxp, mzp, ~params);

        f_mul(~Qx, Qx, tsum, ~params);
        f_mul(~Qz, Qz, tdif, ~params);
    end for;

    f_sqr(~Qx, Qx, ~params);
    f_sqr(~Qz, Qz, ~params);
    f_mul(~newX, XP, Qx, ~params);
    f_mul(~newZ, ZP, Qz, ~params);

    KummerPoint_Init(~result, self`codomain, [newX, newZ], ~params);
end procedure;

procedure KummerLineIsogeny_Normal_PiProducts(~pi_X, ~pi_Z, self, ~params)
    d := (self`degree - 1) div 2;
    diffs := self`kernel_multiples[1];
    sums := self`kernel_multiples[2];
    R := self`domain`base_ring;

    Qx := R!1; Qz := R!1;
    for j := 1 to d do
        f_sub(~facx, diffs[j], sums[j], ~params);   
        f_add(~facz, diffs[j], sums[j], ~params);   
        f_mul(~Qx, Qx, facx, ~params);
        f_mul(~Qz, Qz, facz, ~params);
    end for;
    pi_X := Qz;   
    pi_Z := Qx;   
end procedure;

procedure KummerLineIsogeny_SqrtVelu_PiProducts(~pi_X, ~pi_Z, self, ~params)
    R := self`domain`base_ring;
    M := self`kernel_multiples[1];
    TI := self`kernel_multiples[2];
    Aprecomp := self`kernel_multiples[3];
    precomp := self`kernel_multiples[4];
    bs := self`kernel_multiples[5];
    gs := self`kernel_multiples[6];
    degree := self`degree;

    TP := [R | 0 : t in [1..3*gs]];
    for j := 0 to gs - 1 do
        Ap := Aprecomp[j+1];
        f_sub(~o1, Ap[1], Ap[5], ~params);
        f_neg(~o2, Ap[3], ~params);
        TP[3*j + 1] := o1;
        TP[3*j + 2] := o2;
        TP[3*j + 3] := Ap[1];
    end for;
    poly_multiprod2(~TP, gs, 0, ~params);

    flen := 2*gs + 1;
    TPinv := [R | 0 : t in [1..flen]];
    for t := 1 to flen do
        TPinv[t] := TP[flen - t + 1];
    end for;

    P_base := TI[1 .. 2*bs];
    T_tree := TI[2*bs + 1 .. #TI];

    v1 := [R | 0 : t in [1..bs]];
    poly_multieval_postcompute(~v1, bs, TP[1..flen], flen, P_base, T_tree, precomp, ~params);
    Qz := v1[1];
    for t := 2 to bs do f_mul(~Qz, Qz, v1[t], ~params); end for;

    v2 := [R | 0 : t in [1..bs]];
    poly_multieval_postcompute(~v2, bs, TPinv, flen, P_base, T_tree, precomp, ~params);
    Qx := v2[1];
    for t := 2 to bs do f_mul(~Qx, Qx, v2[t], ~params); end for;

    boundpart := (degree - 1) div 2 - 2*bs*gs;
    for i := 0 to boundpart - 1 do
        Xi2, Zi2 := Explode(M[2*i + 2]);
        f_double(~tz, Zi2, ~params);
        f_double(~tx, Xi2, ~params);
        f_mul(~Qx, Qx, tz, ~params);
        f_mul(~Qz, Qz, tx, ~params);
    end for;

    pi_X := Qz;
    pi_Z := Qx;
end procedure;
    
load "optimised/folded_sqrtvelu.m"; //loaded here to mitigate 'not been declared or assigned error'
procedure KummerLineIsogeny_PiProducts(~pi_X, ~pi_Z, self, ~params)
    if self`is_sqrt then
        if #self`kernel_multiples gt 6 then
            KummerLineIsogeny_SqrtVelu_PiProducts_Folded(~pi_X, ~pi_Z, self, ~params);
        else
            KummerLineIsogeny_SqrtVelu_PiProducts(~pi_X, ~pi_Z, self, ~params);
        end if;
    else
        KummerLineIsogeny_Normal_PiProducts(~pi_X, ~pi_Z, self, ~params);
    end if;
end procedure;

procedure KummerLineIsogeny_Velu_Init(~self, domain, kernel, degree, ~params)
    bitlen := Ilog(2, params`p) + 1;

    if bitlen gt 400 then
        table := TunedTable512;
    else
        table := TunedTable256;
    end if;

    if IsDefined(table, degree) then
        entry := table[degree];
        if entry[1] then
            if entry[4] then
                KummerLineIsogeny_SqrtVelu_Init_Folded(~self, domain, kernel, degree, ~params : bs_override := entry[2], gs_override := entry[3]);
            else
                KummerLineIsogeny_SqrtVelu_Init(~self, domain, kernel, degree, ~params : bs_override := entry[2], gs_override := entry[3]);
            end if;
        else
            KummerLineIsogeny_Normal_Init(~self, domain, kernel, degree, ~params);
        end if;
    else
        threshold := 127;
        if degree le threshold then
            KummerLineIsogeny_Normal_Init(~self, domain, kernel, degree, ~params);
        else
            KummerLineIsogeny_SqrtVelu_Init(~self, domain, kernel, degree, ~params);
        end if;
    end if;
end procedure;

procedure KummerLineIsogeny_Velu_Evaluate(~result, self, P, ~params)
    if self`is_sqrt then
        if #self`kernel_multiples gt 6 then
            KummerLineIsogeny_SqrtVelu_Evaluate_Folded(~result, self, P, ~params);
        else
            KummerLineIsogeny_SqrtVelu_Evaluate(~result, self, P, ~params);
        end if;
    else
        KummerLineIsogeny_Normal_Evaluate(~result, self, P, ~params);
    end if;
end procedure;
