OpsRecord := recformat<I, A, M, S>;

ParamsRecord := recformat<
    base_field, p, r, trace, Ms, Mt,
    ells_straight, exps_straight,
    ells_twist, exps_twist,
    alpha_sq, base_cycle,
    ops,
    strategy_cache
>;

procedure addI(~params, n)  
    params`ops`I +:= Round(n);  
end procedure;

procedure addA(~params, n)  
    params`ops`A +:= Round(n);  
end procedure;

procedure addM(~params, n)  
    params`ops`M +:= Round(n);  
end procedure;

procedure addS(~params, n)  
    params`ops`S +:= Round(n);
end procedure;

procedure ResetStats(~params)
    params`ops`I := 0; params`ops`A := 0;
    params`ops`M := 0; params`ops`S := 0;
end procedure;

procedure PrintStats(~params)
    printf "  Ops (Fp2): I=%o, A=%o, M=%o, S=%o\n",
        params`ops`I, params`ops`A, params`ops`M, params`ops`S;
end procedure;



procedure f_mul(~res, a, b, ~params)
    addM(~params, 1);
    res := a * b;
end procedure;

procedure f_sqr(~res, a, ~params)
    addS(~params, 1);
    res := a^2;
end procedure;

procedure f_add(~res, a, b, ~params)
    addA(~params, 1);
    res := a + b;
end procedure;

procedure f_sub(~res, a, b, ~params)
    addA(~params, 1);
    res := a - b;
end procedure;

procedure f_double(~res, a, ~params)
    addA(~params, 1);
    res := 2*a;
end procedure;

procedure f_neg(~res, a, ~params)
    addA(~params, 1);
    res := -a;
end procedure;

procedure f_inv(~res, a, ~params)
    addI(~params, 1);
    res := a^-1;
end procedure;

procedure BatchInversion(~res, S, ~params)
    n := #S;
    if n eq 0 then res := []; return; end if;
    
    prod := [Universe(S) | S[1]];
    for i := 2 to n do
        Append(~prod, prod[i-1] * S[i]);
        addM(~params, 1);
    end for;
    
    addI(~params, 1);
    inv := 1 / prod[n];
    
    res := [Universe(S) | 1 : i in [1..n]];
    for i := n to 2 by -1 do
        res[i] := inv * prod[i-1];
        inv *:= S[i];
        addM(~params, 2);
    end for;
    res[1] := inv;
end procedure;

procedure f_batch_inv(~res, S, ~params)
    BatchInversion(~res, S, ~params);
end procedure;
