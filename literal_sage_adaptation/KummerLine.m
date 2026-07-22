forward KummerLine_Init, KummerLine_BaseRing, KummerLine_ExtractConstants, KummerLine_a, KummerLine_MontgomeryCurve, KummerLine_Curve, KummerLine_ShortWeierstrassCurve, KummerLine_JInvariant, KummerLine_Eq;

KummerLineRecord := recformat<
    base_ring,
    A,      
    C,      
    curve  
>;

procedure KummerLine_Init(~self, args, ~params)
    self := rec<KummerLineRecord | >;
    self`curve := "None";

    if #args eq 1 then
        curve := args[1];
        if Type(curve) ne CrvEll then
            error "not an elliptic curve";
        end if;
        ainvs := aInvariants(curve);
        if ainvs[1] ne 0 or ainvs[3] ne 0 or ainvs[4] ne 1 or ainvs[5] ne 0 then
             error "Must use Montgomery model";
        end if;
        A := ainvs[2];
        C := 1;
        self`curve := curve;
        self`base_ring := BaseRing(curve);
    elif #args eq 2 then
        base_ring := args[1];
        curve_constants := args[2];
        if Type(curve_constants) in {RngIntElt, FldFinElt, FldRatElt} then
            A := curve_constants;
            C := 1;
        elif Type(curve_constants) eq SeqEnum and #curve_constants eq 1 then
            A := curve_constants[1];
            C := 1;
        elif Type(curve_constants) eq SeqEnum and #curve_constants eq 2 then
            A := curve_constants[1];
            C := curve_constants[2];
        else
            error "The Montgomery coefficient must either be a single scalar a, or a tuple [A, C] representing a = A/C.";
        end if;
        self`base_ring := base_ring;
    else
        error "A Kummer Line must be constructed from either a Montgomery curve, or a base field and tuple representing the coefficient A/C = [A, C]";
    end if;

    self`A := self`base_ring!A;
    self`C := self`base_ring!C;

    addS(~params, 1); addA(~params, 1);
    if (self`A^2 - 4 * self`C^2) eq 0 then
        error "Constants do not define a Montgomery curve";
    end if;
end procedure;

procedure KummerLine_BaseRing(~result, self, ~params)
    result := self`base_ring;
end procedure;

procedure KummerLine_ExtractConstants(~A, ~C, self, ~params)
    A := self`A;
    C := self`C;
end procedure;

procedure KummerLine_a(~result, self, ~params)
    addI(~params, 1);
    result := self`A / self`C;
end procedure;

procedure KummerLine_MontgomeryCurve(~result, self, ~params)
    KummerLine_BaseRing(~F, self, ~params);
    KummerLine_a(~a, self, ~params);
    result := EllipticCurve([F | 0, a, 0, 1, 0]);
end procedure;

procedure KummerLine_Curve(~result, self, ~params)
    if Type(self`curve) eq MonStgElt and self`curve eq "None" then
        KummerLine_MontgomeryCurve(~self`curve, self, ~params);
    end if;
    result := self`curve;
end procedure;

function KummerLine_ShortWeierstrassCurve(self)
    F := self`base_ring;
    A := self`A / self`C;
    A_sqr := A * A;
    A_cube := A * A_sqr;
    a := 1 - A_sqr / 3;
    b := (2 * A_cube - 9 * A) / 27;
    return EllipticCurve([F | a, b]);
end function;

function KummerLine_JInvariant(self)
    j_num := 256 * (self`A^2 - 3 * self`C^2) ^ 3;
    j_den := self`C^4 * (self`A^2 - 4 * self`C^2);
    return j_num / j_den;
end function;

function KummerLine_Eq(self, other)
    if self`base_ring ne other`base_ring then
        return false;
    end if;
    return self`A * other`C eq other`A * self`C;
end function;
