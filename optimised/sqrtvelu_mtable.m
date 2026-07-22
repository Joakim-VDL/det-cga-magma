procedure SqrtVeluSteps(~bs, ~gs, l)
    b := 0; g := 0;
    repeat
        b +:= 2;
        g := (l - 1) div (4 * b);
    until g lt b;
    bs := b; gs := g;
end procedure;

procedure Build_Sparse_Multiples(~M, K, A, C, n, bs, gs, ~params)
    M := AssociativeArray();

    KummerPoint_XZ(~X1, ~Z1, K, ~params);
    M[1] := <X1, Z1>;
    KummerPoint_xDBL(~X2, ~Z2, X1, Z1, A, C, ~params);
    M[2] := <X2, Z2>;

    br := (n - 1) div 2;
    boundpart := br - 2 * bs * gs; 
    
    for s := 3 to n - 1 do
        handled := false;

        if IsOdd(s) then
            i := s div 2; 
            if i lt bs then
                if s eq 3 then
                    Xb, Zb := Explode(M[2]);
                    Xd, Zd := Explode(M[1]);
                    KummerPoint_xADD(~Xnew, ~Znew, Xb, Zb, Xd, Zd, Xd, Zd, ~params);
                else
                    Xa, Za := Explode(M[s-2]);
                    Xb, Zb := Explode(M[2]);
                    Xc, Zc := Explode(M[s-4]);
                    KummerPoint_xADD(~Xnew, ~Znew, Xa, Za, Xb, Zb, Xc, Zc, ~params);
                end if;
                M[s] := <Xnew, Znew>;
                handled := true;
            end if;
        else
            i := s div 2 - 1;
            if i lt boundpart then
                if s eq 4 then
                    Xb, Zb := Explode(M[2]);
                    KummerPoint_xDBL(~Xnew, ~Znew, Xb, Zb, A, C, ~params);
                else
                    Xa, Za := Explode(M[s-2]);
                    Xb, Zb := Explode(M[2]);
                    Xc, Zc := Explode(M[s-4]);
                    KummerPoint_xADD(~Xnew, ~Znew, Xa, Za, Xb, Zb, Xc, Zc, ~params);
                end if;
                M[s] := <Xnew, Znew>;
                handled := true;
            end if;
        end if;

        if not handled and bs gt 0 then
            if s eq 2*bs then
                Xa, Za := Explode(M[bs+1]);
                Xb, Zb := Explode(M[bs-1]);
                Xc, Zc := Explode(M[2]);
                KummerPoint_xADD(~Xnew, ~Znew, Xa, Za, Xb, Zb, Xc, Zc, ~params);
                M[s] := <Xnew, Znew>;
            elif s eq 4*bs then
                X2bs, Z2bs := Explode(M[2*bs]);
                KummerPoint_xDBL(~Xnew, ~Znew, X2bs, Z2bs, A, C, ~params);
                M[s] := <Xnew, Znew>;
            elif s eq 6*bs then
                Xa, Za := Explode(M[4*bs]);
                Xb, Zb := Explode(M[2*bs]);
                Xc, Zc := Explode(M[2*bs]);
                KummerPoint_xADD(~Xnew, ~Znew, Xa, Za, Xb, Zb, Xc, Zc, ~params);
                M[s] := <Xnew, Znew>;
            elif (s mod (4*bs)) eq 2*bs then
                j := s div (4*bs);
                if j lt gs then
                    Xa, Za := Explode(M[s-4*bs]);
                    Xb, Zb := Explode(M[4*bs]);
                    Xc, Zc := Explode(M[s-8*bs]);
                    KummerPoint_xADD(~Xnew, ~Znew, Xa, Za, Xb, Zb, Xc, Zc, ~params);
                    M[s] := <Xnew, Znew>;
                end if;
            end if;
        end if;
    end for;
end procedure;
		
procedure Build_TI_Tree(~TI, M, bs, ~params)
    TIlen := 2*bs + poly_tree1size(bs);
    TI := [params`base_field | 0 : i in [1..TIlen]];

    for i := 0 to bs - 1 do
        Xi, Zi := Explode(M[2*i + 1]);
        f_neg(~TI[2*i + 1], Xi, ~params);  
        TI[2*i + 2] := Zi;                 
    end for;

    poly_tree1(~TI, 2*bs, TI, 0, bs, ~params);
end procedure;
    
procedure biquad_precompute_curve(~Aprecomp, PX, PZ, AX, AZ, ~params)
    f_add(~Pplus, PX, PZ, ~params);
    f_sqr(~Pplus, Pplus, ~params);

    f_sqr(~PxPx, PX, ~params);
    f_sqr(~PzPz, PZ, ~params);

    f_sub(~PxPz2, Pplus, PxPx, ~params);
    f_sub(~PxPz2, PxPz2, PzPz, ~params);

    Aprecomp := [params`base_field | 0 : i in [1..8]];
    f_mul(~Aprecomp[1], AZ, PxPx, ~params);
    f_mul(~Aprecomp[2], AZ, PzPz, ~params);
    f_mul(~Aprecomp[3], AZ, PxPz2, ~params);
    f_mul(~Aprecomp[4], AX, PxPz2, ~params);

    f_add(~t, Aprecomp[1], Aprecomp[2], ~params);
    f_sub(~Aprecomp[6], t, Aprecomp[3], ~params);
    f_add(~Aprecomp[7], t, Aprecomp[3], ~params);

    f_add(~Aprecomp[8], Aprecomp[4], Aprecomp[7], ~params);
    f_neg(~Aprecomp[8], Aprecomp[8], ~params);

    f_sub(~Aprecomp[5], Aprecomp[1], Aprecomp[2], ~params);
end procedure;

procedure biquad_postcompute_curve(~outplus, ~outminus, Aprecomp, ~params)
    outplus := [params`base_field | 0 : i in [1..3]];
    outminus := [params`base_field | 0 : i in [1..3]];

    outplus[1] := Aprecomp[6];
    outplus[3] := Aprecomp[6];
    outminus[1] := Aprecomp[7];
    outminus[3] := Aprecomp[7];

    f_add(~outplus[2], Aprecomp[8], Aprecomp[8], ~params);
    f_add(~outminus[2], Aprecomp[6], Aprecomp[4], ~params);
    f_double(~outminus[2], outminus[2], ~params);
end procedure;

procedure Build_T1_Tminus1(~T1, ~Tminus1, ~Aprecomp, M, A, C, bs, gs, ~params)
    Aprecomp := [];  
    T1 := [params`base_field | 0 : i in [1..3*gs]];
    Tminus1 := [params`base_field | 0 : i in [1..3*gs]];

    for j := 0 to gs - 1 do
        s := 2*bs*(2*j + 1);
        Xj, Zj := Explode(M[s]);

        biquad_precompute_curve(~Apre_j, Xj, Zj, A, C, ~params);
        Append(~Aprecomp, Apre_j);

        biquad_postcompute_curve(~outplus, ~outminus, Apre_j, ~params);
        for t := 1 to 3 do
            T1[3*j + t] := outplus[t];
            Tminus1[3*j + t] := outminus[t];
        end for;
    end for;

    poly_multiprod2_selfreciprocal(~T1, gs, 0, ~params);
    poly_multiprod2_selfreciprocal(~Tminus1, gs, 0, ~params);
end procedure;

procedure Build_Abatch(~Abatchx, ~Abatchz, ~precomp, TI, T1, Tminus1, bs, gs, ~params)
    F := params`base_field;
    flen := 2*gs + 1;

    P_base := TI[1 .. 2*bs];
    T_tree := TI[2*bs + 1 .. #TI];

    poly_multieval_precompute(~precomp, bs, flen, P_base, T_tree, ~params);

    v1 := [F | 0 : i in [1..bs]];
    poly_multieval_postcompute(~v1, bs, T1[1..flen], flen, P_base, T_tree, precomp, ~params);
    Abatchx := v1[1];
    for i := 2 to bs do f_mul(~Abatchx, Abatchx, v1[i], ~params); end for;

    v2 := [F | 0 : i in [1..bs]];
    poly_multieval_postcompute(~v2, bs, Tminus1[1..flen], flen, P_base, T_tree, precomp, ~params);
    Abatchz := v2[1];
    for i := 2 to bs do f_mul(~Abatchz, Abatchz, v2[i], ~params); end for;
end procedure;

procedure biquad_precompute_point(~precomp, QX, QZ, ~params)
    precomp := [params`base_field | 0 : i in [1..6]];
    f_sqr(~precomp[1], QX, ~params);                      
    f_sqr(~precomp[2], QZ, ~params);                      
    f_mul(~precomp[3], QX, QZ, ~params);                  
    f_add(~precomp[4], precomp[3], precomp[3], ~params);  
    f_sub(~precomp[5], precomp[1], precomp[2], ~params);  
    f_sub(~t, QX, QZ, ~params);
    f_sqr(~precomp[6], t, ~params);                       
end procedure;

procedure biquad_postcompute_point(~out, precomp, Aprecomp, ~params)
    out := [params`base_field | 0 : i in [1..3]];

    f_mul(~out[3], Aprecomp[1], precomp[2], ~params);
    f_mul(~v, Aprecomp[3], precomp[3], ~params);
    f_sub(~out[3], out[3], v, ~params);
    f_mul(~v, Aprecomp[2], precomp[1], ~params);
    f_add(~out[3], out[3], v, ~params);

    f_mul(~out[2], Aprecomp[8], precomp[4], ~params);
    f_mul(~v, Aprecomp[3], precomp[6], ~params);
    f_sub(~out[2], out[2], v, ~params);

    f_mul(~out[1], Aprecomp[5], precomp[5], ~params);
    f_add(~out[1], out[1], out[3], ~params);
end procedure;