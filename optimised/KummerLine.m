load "optimised/ops_counter.m";

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
        ainvs := aInvariants(curve);
        A := ainvs[2]; C := 1;
        self`curve := curve;
        self`base_ring := BaseRing(curve);
    elif #args eq 2 then
        base_ring := args[1];
        curve_constants := args[2];
        if Type(curve_constants) in {RngIntElt, FldFinElt, FldRatElt} then
            A := curve_constants; C := 1;
        else
            A := curve_constants[1]; C := curve_constants[2];
        end if;
        self`base_ring := base_ring;
    end if;

    self`A := self`base_ring!A;
    self`C := self`base_ring!C;

    // A^2 - 4*C^2
    f_sqr(~sqA, self`A, ~params);
    f_sqr(~sqC, self`C, ~params);
    f_double(~sqC, sqC, ~params); f_double(~sqC, sqC, ~params);
    f_sub(~disc, sqA, sqC, ~params);
end procedure;

procedure KummerLine_ExtractConstants(~A, ~C, self, ~params)
    A := self`A;
    C := self`C;
end procedure;

procedure KummerLine_a(~result, self, ~params)
    f_inv(~invC, self`C, ~params);
    f_mul(~result, self`A, invC, ~params);
end procedure;

procedure KummerLine_MontgomeryCurve(~result, self, ~params)
    KummerLine_a(~a, self, ~params);
    result := EllipticCurve([self`base_ring | 0, a, 0, 1, 0]);
end procedure;

procedure KummerLine_Curve(~result, self, ~params)
    if Type(self`curve) eq MonStgElt and self`curve eq "None" then
        KummerLine_MontgomeryCurve(~self`curve, self, ~params);
    end if;
    result := self`curve;
end procedure;

function KummerLine_Eq(self, other)
    return self`A * other`C eq other`A * self`C;
end function;
