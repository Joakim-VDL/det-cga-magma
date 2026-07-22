// ---- V/W basis tables, cached per gs (integer arithmetic, built once) ----
FoldVWCache := AssociativeArray();

function GetVW(g)
    V := [ [Integers()| 2] ];
    if g ge 1 then Append(~V, [Integers()| 0, 1]); end if;
    for j := 2 to g do
        prev := V[j];  prev2 := V[j-1];
        nxt := [Integers()| 0] cat prev;
        for k := 1 to #prev2 do nxt[k] -:= prev2[k]; end for;
        Append(~V, nxt);
    end for;
    W := [ [Integers()| 1] ];
    if g ge 2 then Append(~W, [Integers()| 0, 1]); end if;
    for j := 3 to g do
        prev := W[j-1];  prev2 := W[j-2];
        nxt := [Integers()| 0] cat prev;
        for k := 1 to #prev2 do nxt[k] -:= prev2[k]; end for;
        Append(~W, nxt);
    end for;
    return V, W;
end function;

procedure fold_mul_by_int(~r, x, n, ~params)
    neg := n lt 0; m := Abs(n);
    if m eq 1 then r := x;
    elif m eq 2 then f_double(~r, x, ~params);
    else
        bits := IntegerToSequence(m, 2); r := x;
        for b := #bits - 1 to 1 by -1 do
            f_double(~r, r, ~params);
            if bits[b] eq 1 then f_add(~r, r, x, ~params); end if;
        end for;
    end if;
    if neg then f_neg(~r, r, ~params); end if;
end procedure;

procedure fold_TP(~Scoef, ~Bcoef, TPc, g, R, ~params)
    V, W := GetVW(g);
    mid := g + 1;
    f_double(~t0, TPc[mid], ~params);
    tarr := [R|]; aarr := [R|];
    for j := 1 to g do
        f_add(~tj, TPc[mid+j], TPc[mid-j], ~params); Append(~tarr, tj);
        f_sub(~aj, TPc[mid+j], TPc[mid-j], ~params); Append(~aarr, aj);
    end for;
    Scoef := [R | 0 : t in [1..g+1]];
    Scoef[1] := t0;
    for j := 1 to g do
        Vj := V[j+1];
        for k := 1 to #Vj do
            if Vj[k] ne 0 then
                fold_mul_by_int(~tmp, tarr[j], Vj[k], ~params);
                f_add(~Scoef[k], Scoef[k], tmp, ~params);
            end if;
        end for;
    end for;
    Bcoef := [R | 0 : t in [1..g+1]];
    for j := 1 to g do
        Wj := W[j];
        for k := 1 to #Wj do
            if Wj[k] ne 0 then
                fold_mul_by_int(~tmp, aarr[j], Wj[k], ~params);
                f_add(~Bcoef[k], Bcoef[k], tmp, ~params);
            end if;
        end for;
    end for;
end procedure;

procedure fold_core(~Qz, ~Qx, TPc, gs, bs, us, ws, ds, TIy, precomp_y, R, ~params)
    fold_TP(~Scoef, ~Bcoef, TPc, gs, R, ~params);
    Py_base := TIy[1 .. 2*bs];
    Ty_tree := TIy[2*bs + 1 .. #TIy];
    flen_y := gs + 1;
    sv := [R | 0 : t in [1..bs]];
    poly_multieval_postcompute(~sv, bs, Scoef, flen_y, Py_base, Ty_tree, precomp_y, ~params);
    bv := [R | 0 : t in [1..bs]];
    poly_multieval_postcompute(~bv, bs, Bcoef, flen_y, Py_base, Ty_tree, precomp_y, ~params);
    first := true;
    for idx := 1 to bs do
        f_mul(~wsv, ws[idx], sv[idx], ~params);
        f_mul(~db, ds[idx], bv[idx], ~params);
        f_add(~pv, wsv, db, ~params);   
        f_sub(~mv, wsv, db, ~params);   
        if first then
            Qz := pv; Qx := mv; first := false;
        else
            f_mul(~Qz, Qz, pv, ~params);
            f_mul(~Qx, Qx, mv, ~params);
        end if;
    end for;
end procedure;

procedure fold_SR(~S, P, g, R, ~params)
    V, W := GetVW(g);
    f_double(~t0, P[g+1], ~params);
    S := [R | 0 : t in [1..g+1]];
    S[1] := t0;
    for j := 1 to g do
        f_add(~tj, P[g+1+j], P[g+1-j], ~params);
        Vj := V[j+1];
        for k := 1 to #Vj do
            if Vj[k] ne 0 then
                fold_mul_by_int(~tmp, tj, Vj[k], ~params);
                f_add(~S[k], S[k], tmp, ~params);
            end if;
        end for;
    end for;
end procedure;

procedure KummerLineIsogeny_SqrtVelu_Init_Folded(~self, domain, kernel, degree, ~params : bs_override := 0, gs_override := 0)
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

    us := [R|]; ws := [R|]; ds := [R|];
    TIy := [R | 0 : t in [1..2*bs + poly_tree1size(bs)]];
    for idx := 0 to bs - 1 do
        Xi, Zi := Explode(M[2*idx + 1]);
        f_sqr(~x2, Xi, ~params);
        f_sqr(~z2, Zi, ~params);
        f_add(~u, x2, z2, ~params);
        f_sub(~d, x2, z2, ~params);
        f_mul(~w, Xi, Zi, ~params);
        Append(~us, u); Append(~ws, w); Append(~ds, d);
        f_neg(~TIy[2*idx + 1], u, ~params);
        TIy[2*idx + 2] := w;
    end for;
    poly_tree1(~TIy, 2*bs, TIy, 0, bs, ~params);
    Py_base := TIy[1 .. 2*bs];
    Ty_tree := TIy[2*bs + 1 .. #TIy];
    poly_multieval_precompute(~precomp_y, bs, gs + 1, Py_base, Ty_tree, ~params);

    Build_T1_Tminus1(~T1, ~Tminus1, ~Aprecomp, M, A, C, bs, gs, ~params);

    flen := 2*gs + 1;
    fold_SR(~S1, T1[1..flen], gs, R, ~params);
    fold_SR(~Sm, Tminus1[1..flen], gs, R, ~params);
    fy := gs + 1;
    sv := [R | 0 : t in [1..bs]];
    poly_multieval_postcompute(~sv, bs, S1, fy, Py_base, Ty_tree, precomp_y, ~params);
    Abatchx := sv[1];
    for t := 2 to bs do f_mul(~Abatchx, Abatchx, sv[t], ~params); end for;
    mv := [R | 0 : t in [1..bs]];
    poly_multieval_postcompute(~mv, bs, Sm, fy, Py_base, Ty_tree, precomp_y, ~params);
    Abatchz := mv[1];
    for t := 2 to bs do f_mul(~Abatchz, Abatchz, mv[t], ~params); end for;

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

    self`kernel_multiples := <M, [R|], Aprecomp, [R|], bs, gs, us, ws, ds, TIy, precomp_y>;
end procedure;

procedure KummerLineIsogeny_SqrtVelu_Evaluate_Folded(~result, self, P, ~params)
    R := self`domain`base_ring;
    km := self`kernel_multiples;
    M := km[1]; Aprecomp := km[3]; bs := km[5]; gs := km[6];
    us := km[7]; ws := km[8]; ds := km[9]; TIy := km[10]; precomp_y := km[11];
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
    TPc := TP[1..2*gs+1];

    fold_core(~Qz, ~Qx, TPc, gs, bs, us, ws, ds, TIy, precomp_y, R, ~params);

    boundpart := (degree - 1) div 2 - 2*bs*gs;
    for i := 0 to boundpart - 1 do
        Xi2, Zi2 := Explode(M[2*i + 2]);
        f_add(~tmp2, Xi2, Zi2, ~params);
        f_sub(~tmp3, Xi2, Zi2, ~params);
        f_mul(~t0, tmp2, Pdif, ~params);
        f_mul(~t1, tmp3, Psum, ~params);
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

procedure KummerLineIsogeny_SqrtVelu_PiProducts_Folded(~pi_X, ~pi_Z, self, ~params)
    R := self`domain`base_ring;
    km := self`kernel_multiples;
    M := km[1]; Aprecomp := km[3]; bs := km[5]; gs := km[6];
    us := km[7]; ws := km[8]; ds := km[9]; TIy := km[10]; precomp_y := km[11];
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
    TPc := TP[1..2*gs+1];

    fold_core(~Qz, ~Qx, TPc, gs, bs, us, ws, ds, TIy, precomp_y, R, ~params);

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
