/*
 * Field Operation Counter using params record
 */

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
    printf "  Ops: I=%o, A=%o, M=%o, S=%o\n",
        params`ops`I, params`ops`A, params`ops`M, params`ops`S;
end procedure;
