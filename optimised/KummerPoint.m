load "optimised/ops_counter.m";

forward KummerPoint_Init, KummerPoint_Eq, KummerPoint_IsZero, KummerPoint_BaseRing, KummerPoint_Parent, KummerPoint_XZ, KummerPoint_x, KummerPoint_CurvePoint, KummerPoint_xDBL, KummerPoint_xADD, KummerPoint_xDBLADD, KummerPoint_Double, KummerPoint_DoubleIter, KummerPoint_Add, KummerPoint_Mul, KummerPoint_Ladder3Pt, KummerPoint_Multiples, KummerLine_Zero;

KummerPointRecord := recformat<
    parent,
    base_ring,
    X,
    Z
>;

procedure KummerPoint_Init(~self, parent, coords, ~params)
    R := parent`base_ring;
    self := rec<KummerPointRecord | parent := parent, base_ring := R>;

    if Type(coords) eq MonStgElt and coords eq "None" then
        self`X := R!1; self`Z := R!0;
    elif Type(coords) eq PtEll then
        KummerLine_a(~a, parent, ~params);
        self`X := coords[1]; self`Z := coords[3];
    elif Type(coords) in {FldFinElt, FldRatElt, RngIntElt} then
        self`X := coords; self`Z := R!1;
    else
        self`X := R!coords[1]; self`Z := R!coords[2];
    end if;
end procedure;

procedure KummerLine_Zero(~result, self, ~params)
    KummerPoint_Init(~result, self, "None", ~params);
end procedure;

procedure KummerPoint_XZ(~X, ~Z, self, ~params)
    X := self`X;
    Z := self`Z;
end procedure;

procedure KummerPoint_x(~result, self, ~params)
    if self`Z eq 0 then error "Identity point"; end if;
    if self`Z eq 1 then result := self`X; return; end if;
    f_inv(~invZ, self`Z, ~params);
    f_mul(~result, self`X, invZ, ~params);
end procedure;

procedure KummerPoint_xDBL(~X2, ~Z2, X, Z, A, C, ~params)
    f_sub(~t0, X, Z, ~params);
    f_add(~t1, X, Z, ~params);
    f_sqr(~t0, t0, ~params);
    f_sqr(~t1, t1, ~params);
    f_mul(~Z2, C, t0, ~params);
    f_double(~Z2, Z2, ~params);
    f_double(~Z2, Z2, ~params);
    f_mul(~X2, Z2, t1, ~params);
    f_sub(~t1, t1, t0, ~params);
    f_double(~t0, C, ~params);
    f_add(~t0, t0, A, ~params);
    f_mul(~t0, t0, t1, ~params);
    f_add(~Z2, Z2, t0, ~params);
    f_mul(~Z2, Z2, t1, ~params);
end procedure;

procedure KummerPoint_xADD(~XQP, ~ZQP, XP, ZP, XQ, ZQ, xPQ, zPQ, ~params)
    f_sub(~t0, XP, ZP, ~params);
    f_add(~t1, XP, ZP, ~params);
    f_sub(~t2, XQ, ZQ, ~params);
    f_add(~t3, XQ, ZQ, ~params);
    f_mul(~t0, t0, t3, ~params);
    f_mul(~t1, t1, t2, ~params);
    f_sub(~t2, t0, t1, ~params);
    f_add(~t3, t0, t1, ~params);
    f_sqr(~t2, t2, ~params);
    f_sqr(~t3, t3, ~params);
    f_mul(~XQP, zPQ, t3, ~params);
    f_mul(~ZQP, xPQ, t2, ~params);
end procedure;

procedure KummerPoint_xDBLADD(~X2P, ~Z2P, ~XQP, ~ZQP, XP, ZP, XQ, ZQ, xPQ, zPQ, A24, C24, ~params)
    f_add(~t0, XP, ZP, ~params);
    f_sub(~t1, XP, ZP, ~params);
    f_sqr(~X2P, t0, ~params);
    f_sub(~t2, XQ, ZQ, ~params);
    f_add(~XQP, XQ, ZQ, ~params);
    f_mul(~t0, t0, t2, ~params);
    f_sqr(~Z2P, t1, ~params);
    f_mul(~t1, t1, XQP, ~params);
    f_sub(~t2, X2P, Z2P, ~params);
    f_mul(~Z2P, Z2P, C24, ~params);
    f_mul(~X2P, X2P, Z2P, ~params);
    f_mul(~XQP, A24, t2, ~params);
    f_sub(~ZQP, t0, t1, ~params);
    f_add(~Z2P, XQP, Z2P, ~params);
    f_add(~XQP, t0, t1, ~params);
    f_mul(~Z2P, Z2P, t2, ~params);
    f_sqr(~ZQP, ZQP, ~params);
    f_sqr(~XQP, XQP, ~params);
    f_mul(~ZQP, ZQP, xPQ, ~params);
    f_mul(~XQP, XQP, zPQ, ~params);
end procedure;

procedure KummerPoint_Double(~result, self, ~params)
    KummerPoint_XZ(~X, ~Z, self, ~params);
    KummerLine_ExtractConstants(~A, ~C, self`parent, ~params);
    KummerPoint_xDBL(~X2, ~Z2, X, Z, A, C, ~params);
    KummerPoint_Init(~result, self`parent, [X2, Z2], ~params);
end procedure;

procedure KummerPoint_Add(~result, self, Q, PQ, ~params)
    KummerPoint_XZ(~XP, ~ZP, self, ~params);
    KummerPoint_XZ(~XQ, ~ZQ, Q, ~params);
    KummerPoint_XZ(~XPQ, ~ZPQ, PQ, ~params);
    KummerPoint_xADD(~X_new, ~Z_new, XP, ZP, XQ, ZQ, XPQ, ZPQ, ~params);
    KummerPoint_Init(~result, self`parent, [X_new, Z_new], ~params);
end procedure;

procedure KummerPoint_Mul_Ladder(~result, self, m, ~params)
    if m eq 0 then KummerLine_Zero(~result, self`parent, ~params); return; end if;
    m_val := Abs(m); R := self`base_ring;
    KummerPoint_XZ(~XP, ~ZP, self, ~params);
    KummerLine_ExtractConstants(~A, ~C, self`parent, ~params);
    f_double(~A24, C, ~params);
    f_double(~C24, A24, ~params);
    f_add(~A24, A24, A, ~params);
    bits := IntegerToSequence(m_val, 2);
    X0 := R!1; Z0 := R!0; X1 := XP; Z1 := ZP;
    for i := #bits to 1 by -1 do
        if bits[i] eq 0 then
            KummerPoint_xDBLADD(~X0, ~Z0, ~X1, ~Z1, X0, Z0, X1, Z1, XP, ZP, A24, C24, ~params);
        else
            KummerPoint_xDBLADD(~X1, ~Z1, ~X0, ~Z0, X1, Z1, X0, Z0, XP, ZP, A24, C24, ~params);
        end if;
    end for;
    KummerPoint_Init(~result, self`parent, [X0, Z0], ~params);
end procedure;

procedure KummerPoint_Multiples(~res, self, ~params : limit := 0)
    res := [self];
    KummerPoint_Double(~R, self, ~params);
    Q := self;
    while true do
        if limit gt 0 and #res ge limit then return; end if;
        Append(~res, R);
        KummerPoint_Add(~S, R, self, Q, ~params);
        Q := R; R := S;
    end while;
end procedure;
    
    
function BuildDACTable()
    T := AssociativeArray();
    T[3] := [Integers()|];
    T[5] := [0];
    T[7] := [1,0];
    T[11] := [0,1,1];
    T[13] := [0,1,0];
    T[17] := [0,0,1,1];
    T[19] := [0,1,1,0];
    T[23] := [0,0,0,1,1];
    T[29] := [0,1,0,1,1];
    T[31] := [0,0,1,0,1];
    T[37] := [0,1,0,1,1,1];
    T[41] := [0,1,1,0,1,1];
    T[43] := [0,0,1,0,1,1];
    T[47] := [1,0,1,0,1,0];
    T[53] := [0,1,1,1,0,1,1];
    T[59] := [0,1,0,0,0,1,1];
    T[61] := [1,0,0,1,0,1,1];
    T[67] := [1,0,1,1,0,1,0];
    T[71] := [0,1,1,0,1,1,0];
    T[73] := [0,1,1,0,0,1,0];
    T[79] := [0,1,0,1,1,0,1];
    T[83] := [0,0,1,0,0,1,1,1];
    T[89] := [0,1,0,1,0,1,0];
    T[97] := [0,1,0,1,0,1,1,1];
    T[101] := [0,1,0,0,1,1,1,0];
    T[103] := [0,1,0,1,1,1,0,1];
    T[107] := [0,0,0,1,0,1,0,1];
    T[109] := [0,1,1,0,1,0,1,1];
    T[113] := [1,0,0,1,1,0,1,1,1];
    T[127] := [0,1,0,1,1,1,1,0,1];
    T[131] := [0,1,0,1,0,1,1,0];
    T[137] := [0,1,0,1,1,0,1,1,1];
    T[139] := [0,1,1,0,1,0,1,1,1];
    T[149] := [0,1,0,1,0,0,1,1,1];
    T[151] := [0,0,1,0,0,0,1,0,1];
    T[157] := [0,0,0,1,0,1,0,0,1];
    T[163] := [0,1,0,0,1,1,0,1,1];
    T[167] := [0,0,1,1,0,1,0,1,1];
    T[173] := [0,0,1,0,0,1,1,0,1];
    T[179] := [0,0,1,0,1,1,0,0,1];
    T[181] := [0,0,1,1,0,0,1,0,1];
    T[191] := [0,1,0,0,1,0,1,1,0];
    T[193] := [0,0,1,0,1,0,1,1,0];
    T[197] := [1,0,1,0,0,1,0,1,1,1];
    T[199] := [0,1,0,1,0,1,0,1,1];
    T[211] := [0,1,1,0,0,1,0,1,1,1];
    T[223] := [0,0,0,1,0,1,0,0,1,1];
    T[227] := [1,0,0,1,0,1,1,0,1,1];
    T[229] := [1,0,0,1,0,0,1,0,1,1];
    T[233] := [0,1,0,1,0,1,0,1,0];
    T[239] := [0,0,1,0,0,1,0,0,1,1];
    T[241] := [0,1,1,0,0,1,1,0,1,1];
    T[251] := [0,0,1,1,0,0,1,0,1,1];
    T[257] := [1,0,1,1,0,1,0,1,1,0];
    T[263] := [0,0,1,0,0,1,1,0,0,1];
    T[269] := [1,0,1,0,0,1,1,0,1,0];
    T[271] := [1,0,1,0,1,0,0,1,1,0];
    T[277] := [0,0,1,0,1,1,0,1,1,0];
    T[281] := [0,1,0,0,1,0,0,1,1,0];
    T[283] := [0,1,0,1,0,1,1,0,1,1];
    T[293] := [0,0,1,0,1,0,1,0,1,1];
    T[307] := [0,0,1,0,1,0,0,1,0,1];
    T[311] := [0,1,0,1,0,0,1,1,0,1];
    T[313] := [0,1,0,0,1,1,0,1,0,1];
    T[317] := [0,0,1,1,0,1,0,1,0,1];
    T[331] := [0,1,0,0,1,1,0,0,1,1,1];
    T[337] := [0,1,0,1,1,0,1,0,1,0];
    T[347] := [0,1,0,0,1,1,1,0,0,1,1];
    T[349] := [0,1,0,0,1,1,0,0,0,1,1];
    T[353] := [0,0,0,1,1,0,0,1,0,0,1];
    T[359] := [0,1,0,1,0,1,1,0,1,1,1];
    T[367] := [0,1,0,1,0,1,1,1,0,1,1];
    T[373] := [0,1,1,1,0,1,0,1,0,1,1];
    T[379] := [0,1,0,0,0,1,0,1,0,1,1];
    T[383] := [0,1,0,1,1,1,0,1,1,0,1];
    return T;
end function;

DACTable := BuildDACTable();

procedure KummerPoint_Mul_DAC(~R, P, chain, ~params)
    L := P`parent;
    KummerLine_ExtractConstants(~A, ~C, L, ~params);

    KummerPoint_XZ(~Xa, ~Za, P, ~params);                         
    KummerPoint_xDBL(~Xb, ~Zb, Xa, Za, A, C, ~params);        
    KummerPoint_xADD(~Xc, ~Zc, Xb, Zb, Xa, Za, Xa, Za, ~params);   

    for bit in chain do
        if bit eq 0 then
            KummerPoint_xADD(~Xn, ~Zn, Xc, Zc, Xb, Zb, Xa, Za, ~params);
            Xa := Xc; Za := Zc;
        else
            KummerPoint_xADD(~Xn, ~Zn, Xc, Zc, Xa, Za, Xb, Zb, ~params);
            Xb := Xc; Zb := Zc;
        end if;
        Xc := Xn; Zc := Zn;
    end for;

    KummerPoint_Init(~R, L, [Xc, Zc], ~params);
end procedure;

procedure KummerPoint_Mul(~R, P, n, ~params)
    if IsDefined(DACTable, n) then
        KummerPoint_Mul_DAC(~R, P, DACTable[n], ~params);
    else
        KummerPoint_Mul_Ladder(~R, P, n, ~params);
    end if;
end procedure;
