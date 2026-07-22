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
        if aInvariants(Curve(coords)) ne [0, a, 0, 1, 0] then
            error "not a point on the correct Montgomery curve";
        end if;
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

function KummerPoint_Eq(self, other)
    if not KummerLine_Eq(self`parent, other`parent) then
        return false;
    end if;
    return self`X * other`Z eq other`X * self`Z;
end function;

function KummerPoint_IsZero(self)
    return self`Z eq 0;
end function;

function KummerPoint_BaseRing(self)
    return self`base_ring;
end function;

function KummerPoint_Parent(self)
    return self`parent;
end function;

procedure KummerPoint_XZ(~X, ~Z, self, ~params)
    X := self`X;
    Z := self`Z;
end procedure;

procedure KummerPoint_x(~result, self, ~params)
    if self`Z eq 0 then
        error "The identity point has no valid x-coordinate";
    end if;
    if self`Z eq 1 then
        result := self`base_ring!self`X;
        return;
    end if;
    addI(~params, 1);
    result := self`X / self`Z;
end procedure;

procedure KummerPoint_CurvePoint(~result, self, ~params)
    L := self`parent;
    KummerLine_Curve(~E, L, ~params);
    KummerLine_a(~A, L, ~params);

    KummerPoint_x(~x, self, ~params);
    addS(~params, 1); addM(~params, 2); addA(~params, 2);
    y2 := x * (x^2 + A * x + 1);
    
    is_sq, y := IsSquare(y2);
    if not is_sq then
        error "x-coordinate is not on the curve";
    end if;
    
    result := E![x, y, 1];
end procedure;

procedure KummerPoint_xDBL(~X2, ~Z2, X, Z, A, C, ~params)
    addA(~params, 2);
    t0 := X - Z;
    t1 := X + Z;
    addS(~params, 2);
    t0 := t0 * t0;
    t1 := t1 * t1;
    addM(~params, 1);
    Z2 := C * t0;
    addA(~params, 2);
    Z2 := Z2 + Z2;
    Z2 := Z2 + Z2;
    addM(~params, 1);
    X2 := Z2 * t1;
    addA(~params, 1);
    t1 := t1 - t0;
    addA(~params, 2);
    t0 := C + C;
    t0 := t0 + A;
    addM(~params, 1);
    t0 := t0 * t1;
    addA(~params, 1);
    Z2 := Z2 + t0;
    addM(~params, 1);
    Z2 := Z2 * t1;
end procedure;

procedure KummerPoint_xADD(~XQP, ~ZQP, XP, ZP, XQ, ZQ, xPQ, zPQ, ~params)
    addA(~params, 4);
    t0 := XP + ZP;
    t1 := XP - ZP;
    XQ_temp := XQ - ZQ;
    ZQ_temp := XQ + ZQ;
    addM(~params, 2);
    t0 := t0 * XQ_temp;
    t1 := t1 * ZQ_temp;
    addA(~params, 2); addS(~params, 2);
    ZP_new := (t0 - t1)^2;
    XP_new := (t0 + t1)^2;
    addM(~params, 2);
    ZQP := xPQ * ZP_new;
    XQP := XP_new * zPQ;
end procedure;

procedure KummerPoint_xDBLADD(~X2P, ~Z2P, ~XQP, ~ZQP, XP, ZP, XQ, ZQ, xPQ, zPQ, A24, C24, ~params)
    // Sage-aligned DBLADD: 8M + 4S + 8A
    addA(~params, 8);
    addS(~params, 4);
    addM(~params, 8);

    t0 := XP + ZP;
    t1 := XP - ZP;
    X2P := t0 * t0;
    t2 := XQ - ZQ;
    XQP := XQ + ZQ;
    t0 *:= t2;
    Z2P := t1 * t1;
    t1 *:= XQP;
    t2 := X2P - Z2P;
    Z2P *:= C24;
    X2P *:= Z2P;
    XQP := A24 * t2;
    ZQP := t0 - t1;
    Z2P := XQP + Z2P;
    XQP := t0 + t1;
    Z2P *:= t2;
    ZQP *:= ZQP;
    XQP *:= XQP;
    ZQP *:= xPQ;
    XQP *:= zPQ;
end procedure;

procedure KummerPoint_Double(~result, self, ~params)
    if KummerPoint_IsZero(self) then
        result := self;
        return;
    end if;
    KummerPoint_XZ(~X, ~Z, self, ~params);
    KummerLine_ExtractConstants(~A, ~C, self`parent, ~params);
    KummerPoint_xDBL(~X2, ~Z2, X, Z, A, C, ~params);
    KummerPoint_Init(~result, self`parent, [X2, Z2], ~params);
end procedure;

procedure KummerPoint_DoubleIter(~result, self, n, ~params)
    if KummerPoint_IsZero(self) then
        result := self;
        return;
    end if;
    KummerPoint_XZ(~X, ~Z, self, ~params);
    KummerLine_ExtractConstants(~A, ~C, self`parent, ~params);
    for i := 1 to n do
        KummerPoint_xDBL(~X, ~Z, X, Z, A, C, ~params);
    end for;
    KummerPoint_Init(~result, self`parent, [X, Z], ~params);
end procedure;


procedure KummerPoint_Add(~result, self, Q, PQ, ~params)
    if KummerPoint_IsZero(self) then result := Q; return; end if;
    if KummerPoint_IsZero(Q) then result := self; return; end if;

    KummerPoint_XZ(~XP, ~ZP, self, ~params);
    KummerPoint_XZ(~XQ, ~ZQ, Q, ~params);
    KummerPoint_XZ(~XPQ, ~ZPQ, PQ, ~params);

    KummerPoint_xADD(~X_new, ~Z_new, XP, ZP, XQ, ZQ, XPQ, ZPQ, ~params);
    KummerPoint_Init(~result, self`parent, [X_new, Z_new], ~params);
end procedure;

procedure KummerPoint_Mul(~result, self, m, ~params)
    if m eq 0 then KummerLine_Zero(~result, self`parent, ~params); return; end if;
    m_val := Abs(m);

    R := self`base_ring;
    KummerPoint_XZ(~XP, ~ZP, self, ~params);
    
    KummerLine_ExtractConstants(~A, ~C, self`parent, ~params);
    addA(~params, 3);
    A24 := C + C;
    C24 := A24 + A24;
    A24 := A24 + A;

    bits := IntegerToSequence(m_val, 2);
    X0 := R!1; Z0 := R!0;
    X1 := XP; Z1 := ZP;

    for i := #bits to 1 by -1 do
        bit := bits[i];
        if bit eq 0 then
            KummerPoint_xDBLADD(~X0, ~Z0, ~X1, ~Z1, X0, Z0, X1, Z1, XP, ZP, A24, C24, ~params);
        else
            KummerPoint_xDBLADD(~X1, ~Z1, ~X0, ~Z0, X1, Z1, X0, Z0, XP, ZP, A24, C24, ~params);
        end if;
    end for;

    KummerPoint_Init(~result, self`parent, [X0, Z0], ~params);
end procedure;

procedure KummerPoint_Ladder3Pt(~result, self, xP, xPQ, m, ~params)
    if m eq 0 then result := xP; return; end if;
    m_val := Abs(m);

    R := self`base_ring;
    KummerLine_ExtractConstants(~A, ~C, self`parent, ~params);
    addA(~params, 3);
    A24 := C + C;
    C24 := A24 + A24;
    A24 := A24 + A;

    KummerPoint_XZ(~XQ, ~ZQ, self, ~params);
    KummerPoint_XZ(~XP, ~ZP, xP, ~params);
    KummerPoint_XZ(~XPQ, ~ZPQ, xPQ, ~params);

    bits := IntegerToSequence(m_val, 2);
    for i := #bits to 1 by -1 do
        bit := bits[i];
        if bit eq 1 then
            KummerPoint_xDBLADD(~XQ, ~ZQ, ~XP, ~ZP, XQ, ZQ, XP, ZP, XPQ, ZPQ, A24, C24, ~params);
        else
            KummerPoint_xDBLADD(~XQ, ~ZQ, ~XPQ, ~ZPQ, XQ, ZQ, XPQ, ZPQ, XP, ZP, A24, C24, ~params);
        end if;
    end for;
    KummerPoint_Init(~result, self`parent, [XP, ZP], ~params);
end procedure;

procedure KummerPoint_Multiples(~res, self, ~params : limit := 0)
    res := [self];
    KummerPoint_Double(~R, self, ~params);
    if KummerPoint_IsZero(R) then return; end if;

    Q := self;
    while not KummerPoint_IsZero(R) do
        if limit gt 0 and #res ge limit then
            return;
        end if;
        Append(~res, R);
        KummerPoint_Add(~S, R, self, Q, ~params);
        Q := R;
        R := S;
    end while;
end procedure;
