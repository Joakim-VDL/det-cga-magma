forward KummerLineIsogeny_Generic_ValidateInput;
forward KummerLineIsogeny_Velu_PrecomputeEdwardsMultiples, KummerLineIsogeny_Velu_ComputeCodomainConstants, KummerLineIsogeny_Velu_ComputeCodomainConstantsEven;
forward KummerLineIsogeny_Velu_Init, KummerLineIsogeny_Velu_Evaluate;
forward AtomicPolyMul, AtomicPolyMod, ProductTree_Init, ProductTree_Remainders, ProductTree_Resultant;
forward KummerLineIsogeny_VeluSqrt_Fs, KummerLineIsogeny_VeluSqrt_hIPrecomputation, KummerLineIsogeny_VeluSqrt_EJPrecomputation;
forward KummerLineIsogeny_VeluSqrt_hKPrecomputation, KummerLineIsogeny_VeluSqrt_hKCodomain, KummerLineIsogeny_VeluSqrt_hKImage;
forward KummerLineIsogeny_VeluSqrt_Init, KummerLineIsogeny_VeluSqrt_Evaluate;
forward Evaluate_FactoredKummerIsogeny, Recursive_SparseIsogeny, FactoredKummerIsogeny;
forward KummerLineIsogeny_Init, KummerLineIsogeny_Evaluate;

KummerLineIsogenyGenericRecord := recformat<
    degree,
    domain,
    codomain
>;

procedure KummerLineIsogeny_Generic_ValidateInput(domain, kernel, degree, ~params : check := true)
    if check then
        KummerPoint_Mul(~res, kernel, degree, ~params);
        if not KummerPoint_IsZero(res) then
            error "Input point does not have correct order";
        end if;
    end if;
end procedure;

procedure AtomicPolyMul(~res, f, g, ~params)
    if f eq 0 or g eq 0 then res := Parent(f)!0; return; end if;
    
    cf := Coefficients(f); cg := Coefficients(g);
    df := Degree(f); dg := Degree(g);
    R := Parent(cf[1]);
    
    res_c := [R| 0 : i in [1..df + dg + 1]];
    for i := 1 to df + 1 do
        for j := 1 to dg + 1 do
            res_c[i+j-1] +:= cf[i] * cg[j];
            addM(~params, 1);
            addA(~params, 1);
        end for;
    end for;
    res := PolynomialRing(R)!res_c;
end procedure;

procedure AtomicPolyMod(~res, f, g, ~params)
    df := Degree(f); dg := Degree(g);
    if df lt dg then res := f; return; end if;
    
    
    R := Parent(Coefficients(f)[1]);
    curr_f := Coefficients(f);
    for i := df - dg + 1 to 1 by -1 do
        factor := curr_f[i + dg];
        for j := 1 to dg do
            curr_f[i + j - 1] -:= factor * Coefficients(g)[j];
            addM(~params, 1);
            addA(~params, 1);
        end for;
        curr_f[i + dg] := 0;
    end for;
    
    while #curr_f gt 0 and curr_f[#curr_f] eq 0 do
        Prune(~curr_f);
    end while;
    res := PolynomialRing(R)!curr_f;
end procedure;

KummerLineIsogenyVeluRecord := recformat<
    degree,
    domain,
    codomain,
    kernel,
    edwards_multiples
>;

procedure KummerLineIsogeny_Velu_PrecomputeEdwardsMultiples(~E_muls, kernel, d, ~params)
    KummerPoint_Multiples(~K_muls, kernel, ~params : limit := d);
    E_muls := [];
    for i := 1 to d do
        Ki := K_muls[i];
        KummerPoint_XZ(~KX, ~KZ, Ki, ~params);
        addA(~params, 2);
        YE := KX - KZ;
        ZE := KX + KZ;
        Append(~E_muls, [YE, ZE]);
    end for;
    delete K_muls;
end procedure;

procedure KummerLineIsogeny_Velu_ComputeCodomainConstants(~A_new, ~C_new, self, ~params)
    KummerLine_ExtractConstants(~A, ~C, self`domain, ~params);
    addA(~params, 2);
    Ded := C + C;
    Aed := A + Ded;
    Ded := A - Ded;

    prod_Y := 1;
    prod_Z := 1;
    for pair in self`edwards_multiples do
        addM(~params, 2);
        prod_Y *:= pair[1];
        prod_Z *:= pair[2];
    end for;

    addS(~params, 6);
    prod_Y := prod_Y^8; prod_Z := prod_Z^8;

    bits := IntegerToSequence(self`degree, 2);
    for i := #bits - 1 to 1 by -1 do
        addS(~params, 2); 
        if bits[i] eq 1 then
            addM(~params, 2); 
        end if;
    end for;

    addM(~params, 2);
    Aed := Aed^self`degree * prod_Z;
    Ded := Ded^self`degree * prod_Y;

    addA(~params, 3);
    A_new := Aed + Ded;
    C_new := Aed - Ded;
    A_new := A_new + A_new;
end procedure;

procedure KummerLineIsogeny_Velu_ComputeCodomainConstantsEven(~A, ~C, self, ~params)
    KummerPoint_XZ(~XK, ~ZK, self`kernel, ~params);
    addS(~params, 2);
    C := ZK * ZK;
    A := XK * XK;
    addA(~params, 3);
    A := A + A;
    A := C - A;
    A := A + A;
end procedure;

procedure KummerLineIsogeny_Velu_Init(~self, domain, kernel, degree, ~params : check := true)
    KummerLineIsogeny_Generic_ValidateInput(domain, kernel, degree, ~params : check := check);
    self := rec<KummerLineIsogenyVeluRecord | degree := degree, kernel := kernel, domain := domain>;

    if degree eq 2 then
        KummerPoint_XZ(~XK, ~ZK, kernel, ~params);
        if XK eq 0 then error "XK cannot be zero"; end if;
        KummerLineIsogeny_Velu_ComputeCodomainConstantsEven(~A_cod, ~C_cod, self, ~params);
    else
        d := (degree - 1) div 2;
        KummerLineIsogeny_Velu_PrecomputeEdwardsMultiples(~em_local, kernel, d, ~params);
        self`edwards_multiples := em_local;
        KummerLineIsogeny_Velu_ComputeCodomainConstants(~A_cod, ~C_cod, self, ~params);
    end if;

    KummerLine_Init(~cod_local, [* domain`base_ring, [A_cod, C_cod] *], ~params);
    self`codomain := cod_local;
end procedure;

procedure KummerLineIsogeny_Velu_Evaluate(~result, self, P, ~params)
    if self`degree eq 2 then
        KummerPoint_XZ(~XK, ~ZK, self`kernel, ~params);
        KummerPoint_XZ(~XP, ~ZP, P, ~params);
        addA(~params, 6);
        T0 := XK + ZK; T1 := XK - ZK;
        T2 := XP + ZP; T3 := ZP - XP;
        addM(~params, 4);
        T4 := T3 * T0; T5 := T2 * T1;
        T6 := T4 - T5; T7 := T4 + T5;
        T8 := XP * T6; T9 := ZP * T7;
        KummerPoint_Init(~result, self`codomain, [T8, T9], ~params);
    else
        KummerPoint_XZ(~XP, ~ZP, P, ~params);
        addA(~params, 2);
        Psum := XP + ZP; Pdiff := XP - ZP;
        X_new := 1; Z_new := 1;
        for pair in self`edwards_multiples do
            addM(~params, 2);
            diff_EZ := Pdiff * pair[2];
            sum_EY := pair[1] * Psum;
            addA(~params, 2);
            addM(~params, 2);
            X_new *:= diff_EZ + sum_EY;
            Z_new *:= diff_EZ - sum_EY;
        end for;
        addS(~params, 2); addM(~params, 2);
        X_new := X_new^2 * XP;
        Z_new := Z_new^2 * ZP;
        KummerPoint_Init(~result, self`codomain, [X_new, Z_new], ~params);
    end if;
end procedure;

ProductTreeRecord := recformat<leaves, levels>;

procedure ProductTree_Init(~tree, leaves, ~params)
    tree := rec<ProductTreeRecord | leaves := leaves, levels := []>;
    tree`levels := [leaves];
    curr := leaves;
    while #curr gt 1 do
        next_lvl := [];
        for i := 1 to #curr div 2 do
            AtomicPolyMul(~prod, curr[2*i-1], curr[2*i], ~params);
            Append(~next_lvl, prod);
        end for;
        if #curr mod 2 eq 1 then
            Append(~next_lvl, curr[#curr]);
        end if;
        Append(~tree`levels, next_lvl);
        curr := next_lvl;
    end while;
end procedure;

procedure ProductTree_Remainders(~rems, tree, poly, ~params)
    rems := [poly];
    for l := #tree`levels to 1 by -1 do
        next_rems := [];
        lvl := tree`levels[l];
        for i := 1 to #rems do
            idx1 := 2*i-1; idx2 := 2*i;
            if idx1 le #lvl then 
                AtomicPolyMod(~r, rems[i], lvl[idx1], ~params);
                Append(~next_rems, r); 
            end if;
            if idx2 le #lvl then 
                AtomicPolyMod(~r, rems[i], lvl[idx2], ~params);
                Append(~next_rems, r); 
            end if;
        end for;
        rems := next_rems;
    end for;
end procedure;

procedure ProductTree_Resultant(~result, hI_tree, poly, ~params)
    ProductTree_Remainders(~rems, hI_tree, poly, ~params);
    r := Parent(poly)!1;
    for rem in rems do
        AtomicPolyMul(~r, r, rem, ~params);
    end for;
    s := ( (#hI_tree`leaves mod 2 eq 1) and (Degree(poly) eq 1) ) select -1 else 1;
    result := s * ConstantCoefficient(r);
end procedure;

KummerLineIsogenyVeluSqrtRecord := recformat<
    degree, domain, codomain, kernel, a, R, Z, one, Ra,
    hI_tree, EJ_parts, hK_data
>;

function KummerLineIsogeny_VeluSqrt_Fs(self, X)
    X := self`R ! X;
    Z := self`Z;
    z1 := Z + X; z2 := Z - X;
    XZ := X * Z;
    z3 := XZ + self`one; z4 := XZ - self`one;
    z5 := self`Ra * XZ;
    z6 := -(z3 * z1 + z5 + z5);
    return [z2 * z2, z6 + z6, z4 * z4];
end function;

procedure KummerLineIsogeny_VeluSqrt_hIPrecomputation(~tree, self, ker, b, c, ~params)
    KummerPoint_Mul(~Q, ker, b + b, ~params);
    KummerPoint_Double(~step, Q, ~params);
    Kdiff := Q;
    leaves := [];
    for i := 0 to c - 1 do
        KummerPoint_x(~xQ, Q, ~params);
        Append(~leaves, self`Z - xQ);
        if i lt c - 1 then
            temp := Q;
            KummerPoint_Add(~Q, Q, step, Kdiff, ~params);
            Kdiff := temp;
        end if;
    end for;
    ProductTree_Init(~tree, leaves, ~params);
end procedure;

procedure KummerLineIsogeny_VeluSqrt_EJPrecomputation(~EJ_parts, self, ker, b, ~params)
    Q := ker;
    KummerPoint_Double(~step, Q, ~params);
    Kdiff := Q;
    EJ_parts := [];
    for i := 0 to b - 1 do
        KummerPoint_x(~xQ, Q, ~params);
        addA(~params, 8); addM(~params, 3); addS(~params, 2);
        Append(~EJ_parts, KummerLineIsogeny_VeluSqrt_Fs(self, xQ));
        if i lt b - 1 then
            temp := Q;
            KummerPoint_Add(~Q, Q, step, Kdiff, ~params);
            Kdiff := temp;
        end if;
    end for;
end procedure;

procedure KummerLineIsogeny_VeluSqrt_hKPrecomputation(~hK, self, ker, stop, ~params)
    hK := [];
    KummerPoint_Double(~Q, ker, ~params);
    step := Q;
    KummerPoint_Double(~next_point, Q, ~params);
    for i := 2 to stop - 1 by 2 do
        KummerPoint_XZ(~QX, ~QZ, Q, ~params);
        Append(~hK, [QX, QZ]);
        if i lt stop - 1 then
            temp := next_point;
            KummerPoint_Add(~next_point, next_point, step, Q, ~params);
            Q := temp;
        end if;
    end for;
end procedure;

procedure KummerLineIsogeny_VeluSqrt_hKCodomain(~h1, ~h2, self, ~params)
    h1 := 1; h2 := 1;
    for pair in self`hK_data do
        addA(~params, 2); addM(~params, 2);
        h1 *:= pair[2] - pair[1];
        h2 *:= -(pair[2] + pair[1]);
    end for;
end procedure;

procedure KummerLineIsogeny_VeluSqrt_hKImage(~h1, ~h2, self, alpha, ~params)
    h1 := 1; h2 := 1;
    for pair in self`hK_data do
        addM(~params, 4); addA(~params, 2);
        h1 *:= pair[2] - alpha * pair[1];
        h2 *:= alpha * pair[2] - pair[1];
    end for;
end procedure;

procedure KummerLineIsogeny_VeluSqrt_Init(~self, domain, kernel, degree, ~params : check := true)
    KummerLineIsogeny_Generic_ValidateInput(domain, kernel, degree, ~params : check := check);
    self := rec<KummerLineIsogenyVeluSqrtRecord | degree := degree, kernel := kernel, domain := domain>;
    KummerLine_a(~a_local, domain, ~params);
    self`a := a_local;
    k := domain`base_ring;
    self`R := PolynomialRing(k);
    self`Z := self`R.1;
    self`one := self`R ! 1;
    self`Ra := self`R ! self`a;

    b := Floor(SquareRoot(degree - 1)) div 2;
    if b eq 0 then b := 1; end if;
    c := (degree - 1) div (4 * b);
    if c eq 0 then c := 1; end if;
    stop := degree - 4 * b * c;

    KummerLineIsogeny_VeluSqrt_hIPrecomputation(~hi_local, self, kernel, b, c, ~params);
    self`hI_tree := hi_local;
    KummerLineIsogeny_VeluSqrt_EJPrecomputation(~ej_local, self, kernel, b, ~params);
    self`EJ_parts := ej_local;
    KummerLineIsogeny_VeluSqrt_hKPrecomputation(~hk_local, self, kernel, stop, ~params);
    self`hK_data := hk_local;

    E0J := self`R!1; E1J := self`R!1;
    for p in self`EJ_parts do
        AtomicPolyMul(~E0J, E0J, p[1] + p[2] + p[3], ~params);
        AtomicPolyMul(~E1J, E1J, p[1] - p[2] + p[3], ~params);
    end for;

    ProductTree_Resultant(~R0, self`hI_tree, E0J, ~params);
    ProductTree_Resultant(~R1, self`hI_tree, E1J, ~params);
    KummerLineIsogeny_VeluSqrt_hKCodomain(~M0, ~M1, self, ~params);

    addM(~params, 2);
    num := R0 * M0; den := R1 * M1;
    addS(~params, 6);
    num := num^8; den := den^8;
    
    bits := IntegerToSequence(degree, 2);
    for i := #bits - 1 to 1 by -1 do
        addS(~params, 2); 
        if bits[i] eq 1 then
            addM(~params, 2); 
        end if;
    end for;

    addA(~params, 2); addM(~params, 2);
    num *:= (self`a - 2)^degree;
    den *:= (self`a + 2)^degree;

    addA(~params, 2); addM(~params, 1);
    A_new := (num + den) * 2;
    C_new := den - num;
    KummerLine_Init(~cod_local, [* k, [A_new, C_new] *], ~params);
    self`codomain := cod_local;
end procedure;

procedure KummerLineIsogeny_VeluSqrt_Evaluate(~result, self, P, ~params)
    if KummerPoint_IsZero(P) then KummerLine_Zero(~result, self`codomain, ~params); return; end if;
    KummerPoint_x(~alpha, P, ~params);
    alphaR := self`R ! alpha;
    
    EJ1 := self`R!1;
    for p in self`EJ_parts do
        AtomicPolyMul(~EJ1, EJ1, (p[1] * alphaR + p[2]) * alphaR + p[3], ~params);
    end for;
    
    coeffs := Coefficients(EJ1);
    EJ0 := self`R ! Reverse(coeffs);

    ProductTree_Resultant(~R0, self`hI_tree, EJ0, ~params);
    ProductTree_Resultant(~R1, self`hI_tree, EJ1, ~params);
    KummerLineIsogeny_VeluSqrt_hKImage(~M0, ~M1, self, alpha, ~params);

    addM(~params, 3); addS(~params, 2);
    X_new := (R0 * M0)^2 * alpha;
    Z_new := (R1 * M1)^2;
    KummerPoint_Init(~result, self`codomain, [X_new, Z_new], ~params);
end procedure;

procedure Evaluate_FactoredKummerIsogeny(~P_out, phi_list, P_in, ~params)
    P_out := P_in;
    for phi in phi_list do
        if Names(Format(phi)) eq Names(KummerLineIsogenyVeluRecord) then
            KummerLineIsogeny_Velu_Evaluate(~P_out, phi, P_out, ~params);
        else
            KummerLineIsogeny_VeluSqrt_Evaluate(~P_out, phi, P_out, ~params);
        end if;
    end for;
end procedure;

procedure Recursive_SparseIsogeny(~phi_list_out, Q, l, k, split, threshold, ~params)
    l_int := Integers() ! l;
    if k eq 1 then
        if l_int gt threshold then
            KummerLineIsogeny_VeluSqrt_Init(~phi, Q`parent, Q, l_int, ~params : check := false);
            phi_list_out := [phi];
        else
            KummerLineIsogeny_Velu_Init(~phi, Q`parent, Q, l_int, ~params : check := false);
            phi_list_out := [phi];
        end if;
        return;
    end if;

    k1 := Max(1, Min(k - 1, Round(k * split)));
    KummerPoint_Mul(~Q1, Q, l_int^k1, ~params);
    Recursive_SparseIsogeny(~L, Q1, l, k - k1, split, threshold, ~params);
    Evaluate_FactoredKummerIsogeny(~Q2, L, Q, ~params);
    Recursive_SparseIsogeny(~R, Q2, l, k1, split, threshold, ~params);
    phi_list_out := L cat R;
end procedure;

procedure FactoredKummerIsogeny(~phi_list, K, P, order, threshold, ~params)
    cofactor := order;
    phi_list := [];
    fact := Factorization(order);
    P_curr := P;
    for f in fact do
        l := f[1]; e := f[2];
        if l lt 2 * threshold then
            D := l^e;
            cofactor div:= D;
            KummerPoint_Mul(~Q, P_curr, cofactor, ~params);
            Recursive_SparseIsogeny(~psi_list, Q, l, e, 0.8, threshold, ~params);
            if cofactor ne 1 then
                Evaluate_FactoredKummerIsogeny(~P_curr, psi_list, P_curr, ~params);
            end if;
            phi_list cat:= psi_list;
            delete Q;
        else
            for i := 1 to e do
                cofactor div:= l;
                KummerPoint_Mul(~Q, P_curr, cofactor, ~params);
                KummerLineIsogeny_VeluSqrt_Init(~psi, Q`parent, Q, l, ~params);
                if cofactor ne 1 then
                    KummerLineIsogeny_VeluSqrt_Evaluate(~P_curr, psi, P_curr, ~params);
                end if;
                Append(~phi_list, psi);
                delete Q;
            end for;
        end if;
    end for;
end procedure;

KummerLineIsogenyCompositeRecord := recformat<phis, degree, domain, codomain>;

procedure KummerLineIsogeny_Init(~self, domain, kernel, degree, ~params : check := true, threshold := 1500)
    KummerLineIsogeny_Generic_ValidateInput(domain, kernel, degree, ~params : check := check);
    self := rec<KummerLineIsogenyCompositeRecord | phis := []>;
    FactoredKummerIsogeny(~phis_local, domain, kernel, degree, threshold, ~params);
    self`phis := phis_local;
    
    deg := 1;
    for phi in self`phis do
        deg *:= phi`degree;
    end for;
    self`degree := deg;
    self`domain := self`phis[1]`domain;
    self`codomain := self`phis[#self`phis]`codomain;
end procedure;

procedure KummerLineIsogeny_Evaluate(~result, self, P, ~params)
    Evaluate_FactoredKummerIsogeny(~result, self`phis, P, ~params);
end procedure;
