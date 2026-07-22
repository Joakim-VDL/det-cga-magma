procedure poly_mul(~c, a, b, ~params)
    alen := #a; blen := #b;
    F := params`base_field;

    if alen lt blen then
        poly_mul(~c, b, a, ~params);
        return;
    end if;
    if blen eq 0 then c := []; return; end if;
    if blen eq 1 then
        c := [];
        for i := 1 to alen do
            f_mul(~ci, a[i], b[1], ~params);
            Append(~c, ci);
        end for;
        return;
    end if;

    if alen eq 2 then
        f_mul(~c0, a[1], b[1], ~params);
        f_mul(~c2, a[2], b[2], ~params);
        f_add(~a01, a[1], a[2], ~params);
        f_add(~b01, b[1], b[2], ~params);
        f_mul(~c1, a01, b01, ~params);
        f_sub(~c1, c1, c0, ~params);
        f_sub(~c1, c1, c2, ~params);
        c := [c0, c1, c2];
        return;
    end if;

    if blen eq 2 then
        if alen eq 3 then
            f_mul(~c0, a[1], b[1], ~params);
            f_mul(~c2, a[2], b[2], ~params);
            f_add(~b01, b[1], b[2], ~params);
            f_add(~a01, a[1], a[2], ~params);
            f_mul(~c1, a01, b01, ~params);
            f_sub(~c1, c1, c0, ~params);
            f_sub(~c1, c1, c2, ~params);
            f_mul(~c3, a[3], b[2], ~params);
            f_mul(~a2b0, a[3], b[1], ~params);
            f_add(~c2, c2, a2b0, ~params);
            c := [c0, c1, c2, c3];
            return;
        end if;
        if alen eq 4 then
            f_mul(~c0, a[1], b[1], ~params);
            f_mul(~c2, a[2], b[2], ~params);
            f_add(~b01, b[1], b[2], ~params);
            f_add(~a01, a[1], a[2], ~params);
            f_mul(~c1, a01, b01, ~params);
            f_sub(~c1, c1, c0, ~params);
            f_sub(~c1, c1, c2, ~params);
            f_mul(~mid, a[3], b[1], ~params);
            f_mul(~c4, a[4], b[2], ~params);
            f_add(~a23, a[3], a[4], ~params);
            f_mul(~c3, a23, b01, ~params);
            f_sub(~c3, c3, mid, ~params);
            f_sub(~c3, c3, c4, ~params);
            f_add(~c2, c2, mid, ~params);
            c := [c0, c1, c2, c3, c4];
            return;
        end if;
    end if;

    if blen eq 3 and alen eq 3 then
        f_sub(~a10, a[2], a[1], ~params);
        f_sub(~b01, b[1], b[2], ~params);
        f_mul(~c1, a10, b01, ~params);
        f_sub(~a20, a[3], a[1], ~params);
        f_sub(~b02, b[1], b[3], ~params);
        f_mul(~c2, a20, b02, ~params);
        f_sub(~a21, a[3], a[2], ~params);
        f_sub(~b12, b[2], b[3], ~params);
        f_mul(~c3, a21, b12, ~params);
        f_mul(~c0, a[1], b[1], ~params);
        f_mul(~c4, a[3], b[3], ~params);
        f_mul(~a1b1, a[2], b[2], ~params);
        f_add(~t, a1b1, c0, ~params);
        f_add(~c1, c1, t, ~params);
        f_add(~t, a1b1, c4, ~params);
        f_add(~c3, c3, t, ~params);
        f_add(~t, t, c0, ~params);  
        f_add(~c2, c2, t, ~params);
        c := [c0, c1, c2, c3, c4];
        return;
    end if;

    kara := (alen + 1) div 2;
    a1len := alen - kara;

    if blen le kara then
        poly_mul(~c, a[1..kara], b, ~params);          
        poly_mul(~c1, a[kara+1..alen], b, ~params);
        total_len := alen + blen - 1;
        for idx := #c+1 to total_len do Append(~c, F!0); end for;
        for i := 0 to blen-2 do
            f_add(~c[kara+i+1], c[kara+i+1], c1[i+1], ~params);
        end for;
        for i := blen-1 to a1len+blen-2 do
            c[kara+i+1] := c1[i+1];    
        end for;
        return;
    end if;

    b1len := blen - kara;

    a01 := [F!0 : t in [1..kara]];
    for i := 0 to a1len-1 do
        f_add(~a01[i+1], a[i+1], a[i+kara+1], ~params);
    end for;
    for i := a1len to kara-1 do
        a01[i+1] := a[i+1];
    end for;

    b01 := [F!0 : t in [1..kara]];
    for i := 0 to b1len-1 do
        f_add(~b01[i+1], b[i+1], b[i+kara+1], ~params);
    end for;
    for i := b1len to kara-1 do
        b01[i+1] := b[i+1];
    end for;

    c1len := a1len + b1len - 1;
    total_len := alen + blen - 1;
    c := [F!0 : t in [1..total_len]];

    poly_mul(~c0core, a[1..kara], b[1..kara], ~params); 
    for i := 0 to 2*kara-2 do
        c[i+1] := c0core[i+1];
    end for;

    poly_mul(~c01, a01, b01, ~params);                     
    poly_mul(~c1, a[kara+1..alen], b[kara+1..blen], ~params); 

    if c1len lt kara then
        f_sub(~c[kara+kara-1+1], c01[kara-1+1], c[kara-1+1], ~params);
        for i := 0 to c1len-1 do
            f_sub(~mix, c[kara+i+1], c1[i+1], ~params);
            f_sub(~c[i+2*kara+1], c01[i+kara+1], mix, ~params);
            f_sub(~c[i+kara+1], mix, c[i+1], ~params);
            f_add(~c[i+kara+1], c[i+kara+1], c01[i+1], ~params);
        end for;
        for i := c1len to kara-2 do
            f_sub(~c[i+2*kara+1], c01[i+kara+1], c[i+kara+1], ~params);
            f_sub(~c[i+kara+1], c[i+kara+1], c[i+1], ~params);
            f_add(~c[i+kara+1], c[i+kara+1], c01[i+1], ~params);
        end for;
        return;
    end if;

    for i := 0 to c1len-kara-1 do
        f_sub(~mix, c[kara+i+1], c1[i+1], ~params);
        f_sub(~c[i+kara+1], mix, c[i+1], ~params);
        f_add(~c[i+kara+1], c[i+kara+1], c01[i+1], ~params);
        f_sub(~c[i+2*kara+1], c01[i+kara+1], mix, ~params);
        f_sub(~c[i+2*kara+1], c[i+2*kara+1], c1[i+kara+1], ~params);
    end for;
    for i := c1len-kara to kara-2 do
        f_sub(~mix, c[kara+i+1], c1[i+1], ~params);
        f_sub(~c[i+kara+1], mix, c[i+1], ~params);
        f_add(~c[i+kara+1], c[i+kara+1], c01[i+1], ~params);
        f_sub(~c[i+2*kara+1], c01[i+kara+1], mix, ~params);
    end for;
    f_sub(~c[kara+kara-1+1], c01[kara-1+1], c[kara-1+1], ~params);
    f_sub(~c[kara+kara-1+1], c[kara+kara-1+1], c1[kara-1+1], ~params);
    for i := kara-1 to c1len-1 do
        c[i+2*kara+1] := c1[i+1];    
    end for;
end procedure;

procedure poly_mul_low(~c, clen, a, b, ~params)
    alen := #a; blen := #b;
    F := params`base_field;

    if alen eq 0 or blen eq 0 or clen eq 0 then
        c := []; return;
    end if;

    if clen eq alen + blen - 1 then
        poly_mul(~c, a, b, ~params);
        return;
    end if;

    if clen * 4 ge 3 * (alen + blen - 1) then
        poly_mul(~ab, a, b, ~params);
        c := ab[1..clen];
        return;
    end if;

    if alen lt blen then
        poly_mul_low(~c, clen, b, a, ~params);
        return;
    end if;

    if alen gt clen then
        a := a[1..clen];
        alen := clen;
    end if;
    if blen gt clen then
        b := b[1..clen];
        blen := clen;
    end if;

    if blen eq 1 then
        c := [];
        for i := 1 to clen do
            f_mul(~ci, a[i], b[1], ~params);
            Append(~c, ci);
        end for;
        return;
    end if;

    if clen eq 2 then
        f_mul(~c0, a[1], b[1], ~params);
        f_mul(~c1, a[1], b[2], ~params);
        f_mul(~t, a[2], b[1], ~params);
        f_add(~c1, c1, t, ~params);
        c := [c0, c1];
        return;
    end if;

    if blen eq 2 then
        if clen eq 3 then
            f_mul(~c0, a[1], b[1], ~params);
            f_mul(~c2, a[2], b[2], ~params);
            f_add(~b01, b[1], b[2], ~params);
            f_add(~a01, a[1], a[2], ~params);
            f_mul(~c1, a01, b01, ~params);
            f_sub(~c1, c1, c0, ~params);
            f_sub(~c1, c1, c2, ~params);
            f_mul(~a2b0, a[3], b[1], ~params);
            f_add(~c2, c2, a2b0, ~params);
            c := [c0, c1, c2];
            return;
        end if;
    end if;

    a1len := alen div 2;
    a0len := alen - a1len;
    a0 := [a[2*i - 1] : i in [1..a0len]];
    a1 := [a[2*i] : i in [1..a1len]];

    b1len := blen div 2;
    b0len := blen - b1len;
    b0 := [b[2*i - 1] : i in [1..b0len]];
    b1 := [b[2*i] : i in [1..b1len]];

    a01 := [F!0 : t in [1..a0len]];
    for i := 1 to a1len do
        f_add(~a01[i], a0[i], a1[i], ~params);
    end for;
    if a1len lt a0len then
        a01[a0len] := a0[a0len];
    end if;

    b01 := [F!0 : t in [1..b0len]];
    for i := 1 to b1len do
        f_add(~b01[i], b0[i], b1[i], ~params);
    end for;
    if b1len lt b0len then
        b01[b0len] := b0[b0len];
    end if;

    c0len := a0len + b0len - 1;
    if c0len gt (clen + 1) div 2 then
        c0len := (clen + 1) div 2;
    end if;
    poly_mul_low(~c0, c0len, a0, b0, ~params);

    c01len := a0len + b0len - 1;
    if c01len gt clen div 2 then
        c01len := clen div 2;
    end if;
    poly_mul_low(~c01, c01len, a01, b01, ~params);

    c1len := a1len + b1len - 1;
    if c1len gt clen div 2 then
        c1len := clen div 2;
    end if;
    poly_mul_low(~c1, c1len, a1, b1, ~params);

    for i := 1 to c01len do
        f_sub(~c01[i], c01[i], c0[i], ~params);
    end for;

    for i := 1 to c1len do
        f_sub(~c01[i], c01[i], c1[i], ~params);
    end for;

    c := [F!0 : t in [1..clen]];
    for i := 1 to c0len do
        c[2*i - 1] := c0[i];
    end for;
    for i := 1 to c01len do
        c[2*i] := c01[i];
    end for;
    for i := 1 to c1len - 1 do
        f_add(~c[2*i + 1], c[2*i + 1], c1[i], ~params);
    end for;
    if 2 * c1len lt clen then
        f_add(~c[2 * c1len + 1], c[2 * c1len + 1], c1[c1len], ~params);
    end if;
end procedure;

procedure poly_mul_high(~c, cstart, a, b, ~params)
    alen := #a; blen := #b;
    F := params`base_field;

    if alen lt blen then
        poly_mul_high(~c, cstart, b, a, ~params);
        return;
    end if;

    if blen le 0 or cstart ge alen + blen - 1 then
        c := [];
        return;
    end if;

    if cstart eq 0 then
        poly_mul(~c, a, b, ~params);
        return;
    end if;

    if cstart eq alen + blen - 2 then
        f_mul(~c0, a[alen], b[blen], ~params);
        c := [c0];
        return;
    end if;

    if blen eq 1 then
        c := [];
        for i := cstart + 1 to alen do
            f_mul(~ci, a[i], b[1], ~params);
            Append(~c, ci);
        end for;
        return;
    end if;

    if cstart eq alen + blen - 3 then
        f_mul(~c0_1, a[alen-1], b[blen], ~params);
        f_mul(~c0_2, a[alen], b[blen-1], ~params);
        f_add(~c0, c0_1, c0_2, ~params);
        f_mul(~c1, a[alen], b[blen], ~params);
        c := [c0, c1];
        return;
    end if;

    arev := [a[alen - i] : i in [0..alen-1]];
    brev := [b[blen - i] : i in [0..blen-1]];
    
    out_len := alen + blen - 1 - cstart;
    poly_mul_low(~crev, out_len, arev, brev, ~params);
    
    c := [crev[out_len - i] : i in [0..out_len-1]];
end procedure;
    

procedure poly_mul_mid(~c, cstart, clen, a, alen, b, blen, ~params)
    assert #a ge alen;
    assert #b ge blen;
    F := params`base_field;

    if alen eq 0 or blen eq 0 or clen eq 0 then
        c := [];
        return;
    end if;

    if clen eq 1 then
        c0 := F!0;
        local_alen := alen;
        if local_alen gt cstart then
            local_alen := cstart + 1;
        end if;
        i := 0;
        if blen le cstart then
            i := cstart - blen + 1;
        end if;
        for idx := i to local_alen - 1 do
            f_mul(~t, a[idx+1], b[cstart - idx + 1], ~params);
            f_add(~c0, c0, t, ~params);
        end for;
        c := [c0];
        return;
    end if;

    if blen eq 1 then
        c := [];
        for i := 0 to clen - 1 do
            f_mul(~ci, a[cstart + i + 1], b[1], ~params);
            Append(~c, ci);
        end for;
        return;
    end if;

    if cstart gt 0 and cstart + clen le alen and (blen mod 2 eq 1) then
	new_alen := alen - 1;
    	new_blen := blen - 1;
        poly_mul_mid(~c, cstart - 1, clen, a[1..new_alen], new_alen, b[2..blen], new_blen, ~params);
        for i := 0 to clen - 1 do
            f_mul(~t, a[cstart + i + 1], b[1], ~params);
            f_add(~c[i+1], c[i+1], t, ~params);
        end for;
        return;
    end if;

    if clen eq 2 then
        if cstart eq 1 and alen ge 3 and blen eq 2 then
            f_sub(~delta, b[1], b[2], ~params);
            f_mul(~delta, delta, a[2], ~params);
            f_add(~c0, a[1], a[2], ~params);
            f_mul(~c0, c0, b[2], ~params);
            f_add(~c0, c0, delta, ~params);
            f_add(~c1, a[2], a[3], ~params);
            f_mul(~c1, c1, b[1], ~params);
            f_sub(~c1, c1, delta, ~params);
            c := [c0, c1];
            return;
        end if;
        if cstart eq 3 and alen ge 5 and blen eq 4 then
            f_sub(~b01, b[1], b[2], ~params);
            f_sub(~b23, b[3], b[4], ~params);
            f_mul(~a1b23, a[2], b23, ~params);
            f_mul(~a3b01, a[4], b01, ~params);
            f_add(~delta, a1b23, a3b01, ~params);
            f_add(~a01, a[1], a[2], ~params);
            f_add(~a12, a[2], a[3], ~params);
            f_add(~a23, a[3], a[4], ~params);
            f_add(~a34, a[4], a[5], ~params);
            f_mul(~a01, a01, b[4], ~params);
            f_mul(~a12, a12, b[3], ~params);
            f_mul(~a23, a23, b[2], ~params);
            f_mul(~a34, a34, b[1], ~params);
            f_add(~c0, a01, a23, ~params);
            f_add(~c1, a12, a34, ~params);
            f_add(~c0, c0, delta, ~params);
            f_sub(~c1, c1, delta, ~params);
            c := [c0, c1];
            return;
        end if;
    end if;

    if clen eq 3 and cstart eq 1 and blen eq 2 and alen ge 4 then
        f_sub(~b01, b[1], b[2], ~params);
        f_mul(~delta0, a[2], b01, ~params);
        f_mul(~delta1, a[3], b01, ~params);
        f_add(~c0, a[1], a[2], ~params);
        f_add(~c1, a[2], a[3], ~params);
        f_add(~c2, a[3], a[4], ~params);
        f_mul(~c0, c0, b[2], ~params);
        f_mul(~c1, c1, b[2], ~params);
        f_mul(~c2, c2, b[1], ~params);
        f_add(~c0, c0, delta0, ~params);
        f_add(~c1, c1, delta1, ~params);
        f_sub(~c2, c2, delta1, ~params);
        c := [c0, c1, c2];
        return;
    end if;

    if clen eq 4 and cstart eq 5 and blen eq 6 and alen ge 9 then
        a01 := [];
        for i := 0 to 5 do
            f_add(~tmp, a[i+1], a[i+3+1], ~params);
            Append(~a01, tmp);
        end for;

        b01 := [];
        for i := 0 to 2 do
            f_sub(~tmp, b[i+1], b[i+3+1], ~params);
            Append(~b01, tmp);
        end for;

        poly_mul_mid(~c_part1, 2, 3, a01[1..5], 5, b[4..6], 3, ~params);
        poly_mul_mid(~c_part2, 2, 1, a01[4..6], 3, b[1..3], 3, ~params);
        poly_mul_mid(~delta, 2, 3, a[4..8], 5, b01, 3, ~params);

        c := [F!0 : t in [1..4]];
        c[1] := c_part1[1];
        c[2] := c_part1[2];
        c[3] := c_part1[3];
        c[4] := c_part2[1];

        f_add(~c[1], c[1], delta[1], ~params);
        f_add(~c[2], c[2], delta[2], ~params);
        f_add(~c[3], c[3], delta[3], ~params);
        f_sub(~c[4], c[4], delta[1], ~params);
        return;
    end if;

    if clen eq 5 and cstart eq 3 and blen eq 4 and alen ge 8 then
        a01 := [F!0 : t in [1..6]];
        f_add(~a01[1], a[1], a[3], ~params);
        f_add(~a01[2], a[2], a[4], ~params);
        f_add(~a01[3], a[3], a[5], ~params);
        f_add(~a01[4], a[4], a[6], ~params);
        f_add(~a01[5], a[5], a[7], ~params);
        f_add(~a01[6], a[6], a[8], ~params);

        b01 := [F!0 : t in [1..2]];
        f_sub(~b01[1], b[1], b[3], ~params);
        f_sub(~b01[2], b[2], b[4], ~params);

        poly_mul_mid(~c_part1, 1, 3, a01[1..4], 4, b[3..4], 2, ~params);
        poly_mul_mid(~c_part2, 1, 2, a01[4..6], 3, b[1..2], 2, ~params);
        poly_mul_mid(~delta, 1, 3, a[3..6], 4, b01, 2, ~params);

        c := [F!0 : t in [1..5]];
        c[1] := c_part1[1];
        c[2] := c_part1[2];
        c[3] := c_part1[3];
        c[4] := c_part2[1];
        c[5] := c_part2[2];

        f_add(~c[1], c[1], delta[1], ~params);
        f_add(~c[2], c[2], delta[2], ~params);
        f_add(~c[3], c[3], delta[3], ~params);
        f_sub(~c[4], c[4], delta[2], ~params);
        f_sub(~c[5], c[5], delta[3], ~params);
        return;
    end if;

    if (clen mod 2 eq 1) and cstart eq clen and blen eq clen + 1 and alen ge cstart + clen then
        split := (clen + 1) div 2;

        a01 := [];
        for i := 0 to 3*split - 3 do
            f_add(~tmp, a[i+1], a[i+split+1], ~params);
            Append(~a01, tmp);
        end for;

        b01 := [];
        for i := 0 to split - 1 do
            f_sub(~tmp, b[i+1], b[i+split+1], ~params);
            Append(~b01, tmp);
        end for;

        poly_mul_mid(~c_part1, split - 1, split, a01[1..clen], clen, b[split+1..2*split], split, ~params);
        poly_mul_mid(~c_part2, split - 1, split - 1, a01[split+1..split+clen-1], clen - 1, b[1..split], split, ~params);
        poly_mul_mid(~delta, split - 1, split, a[split+1..split+clen], clen, b01, split, ~params);

        c := [F!0 : t in [1..clen]];
        for i := 1 to split do
            c[i] := c_part1[i];
        end for;
        for i := 1 to split - 1 do
            c[split + i] := c_part2[i];
        end for;

        for i := 1 to split do
            f_add(~c[i], c[i], delta[i], ~params);
        end for;
        for i := 1 to split - 1 do
            f_sub(~c[split + i], c[split + i], delta[i], ~params);
        end for;
        return;
    end if;

    if (clen mod 2 eq 0) and cstart eq clen - 1 and blen eq clen and alen ge cstart + clen then
        split := clen div 2;

        a01 := [];
        for i := 0 to 3*split - 2 do
            f_add(~tmp, a[i+1], a[i+split+1], ~params);
            Append(~a01, tmp);
        end for;

        b01 := [];
        for i := 0 to split - 1 do
            f_sub(~tmp, b[i+1], b[i+split+1], ~params);
            Append(~b01, tmp);
        end for;

        poly_mul_mid(~c_part1, split - 1, split, a01[1..2*split-1], 2*split - 1, b[split+1..2*split], split, ~params);
        
        poly_mul_mid(~c_part2, split - 1, split, a01[split+1..3*split-1], 2*split - 1, b[1..split], split, ~params);
        
        poly_mul_mid(~delta, split - 1, split, a[split+1..3*split-1], 2*split - 1, b01, split, ~params);

        c := [F!0 : t in [1..clen]];
        for i := 1 to split do
            c[i] := c_part1[i];
            c[split + i] := c_part2[i];
        end for;

        for i := 1 to split do
            f_add(~c[i], c[i], delta[i], ~params);
            f_sub(~c[split + i], c[split + i], delta[i], ~params);
        end for;
        return;
    end if;

    if cstart + cstart + clen lt alen + blen then
        poly_mul_low(~ab, cstart + clen, a, b, ~params);
        c := [ab[cstart + i + 1] : i in [0..clen-1]];
        return;
    end if;

    poly_mul_high(~ab, cstart, a, b, ~params);
    c := [ab[i + 1] : i in [0..clen-1]];
    return;
end procedure;

procedure poly_mul_selfreciprocal(~c, a, alen, b, blen, ~params)
    c := [ params`base_field | 0 : i in [1 .. alen + blen - 1] ];
    F := params`base_field;

    if alen eq 0 or blen eq 0 then return; end if;

    if alen eq 1 and blen eq 1 then
        f_mul(~c[1], a[1], b[1], ~params);
        return;
    end if;

    if alen eq 2 and blen eq 2 then
        f_mul(~c[1], a[1], b[1], ~params);
        f_add(~c[2], c[1], c[1], ~params); 
        c[3] := c[1];
        return;
    end if;

    if alen eq 3 and blen eq 3 then
        f_mul(~c[1], a[1], b[1], ~params);
        f_mul(~c[3], a[2], b[2], ~params);
        
        a01 := F!0; f_add(~a01, a[1], a[2], ~params);
        b01 := F!0; f_add(~b01, b[1], b[2], ~params);
        
        f_mul(~c[2], a01, b01, ~params);
        f_add(~c[3], c[3], c[1], ~params); 
        f_sub(~c[2], c[2], c[3], ~params); 
        f_add(~c[3], c[3], c[1], ~params); 
        
        c[4] := c[2];
        c[5] := c[1];
        return;
    end if;

    if alen eq 4 and blen eq 4 then
        f_mul(~c[1], a[1], b[1], ~params);
        f_mul(~c[4], a[2], b[2], ~params);
        
        a01 := F!0; f_add(~a01, a[1], a[2], ~params);
        b01 := F!0; f_add(~b01, b[1], b[2], ~params);
        
        f_mul(~c[3], a01, b01, ~params);
        f_sub(~c[3], c[3], c[1], ~params);
        f_sub(~c[2], c[3], c[4], ~params);
        f_add(~c[4], c[4], c[1], ~params);
        f_add(~c[4], c[4], c[4], ~params);
        
        c[5] := c[3];
        c[6] := c[2];
        c[7] := c[1];
        return;
    end if;

    if alen eq 5 and blen eq 5 then
        a10 := F!0; f_sub(~a10, a[2], a[1], ~params);
        b01 := F!0; f_sub(~b01, b[1], b[2], ~params);
        f_mul(~c[2], a10, b01, ~params);
        
        a20 := F!0; f_sub(~a20, a[3], a[1], ~params);
        b02 := F!0; f_sub(~b02, b[1], b[3], ~params);
        f_mul(~c[3], a20, b02, ~params);
        
        a21 := F!0; f_sub(~a21, a[3], a[2], ~params);
        b12 := F!0; f_sub(~b12, b[2], b[3], ~params);
        f_mul(~c[4], a21, b12, ~params);
        
        f_mul(~c[1], a[1], b[1], ~params);
        a1b1 := F!0; f_mul(~a1b1, a[2], b[2], ~params);
        a2b2 := F!0; f_mul(~a2b2, a[3], b[3], ~params);
        
        t := F!0; f_add(~t, a1b1, c[1], ~params);
        f_add(~c[2], c[2], t, ~params);
        f_add(~c[4], c[4], c[2], ~params);
        f_add(~c[5], t, a2b2, ~params);
        f_add(~c[5], c[5], t, ~params);
        f_add(~c[3], c[3], t, ~params);
        f_add(~c[3], c[3], a2b2, ~params);
        f_add(~c[4], c[4], a1b1, ~params);
        f_add(~c[4], c[4], a2b2, ~params);
        
        c[6] := c[4];
        c[7] := c[3];
        c[8] := c[2];
        c[9] := c[1];
        return;
    end if;

    if alen eq blen and (alen mod 2 eq 1) then
        len0 := (alen+1) div 2;
        len1 := alen div 2;
        
        a0 := [a[2*i-1] : i in [1..len0]];
        b0 := [b[2*i-1] : i in [1..len0]];
        c0 := [F!0 : i in [1..2*len0-1]];
        poly_mul_selfreciprocal(~c0, a0, len0, b0, len0, ~params);

        a1 := [a[2*i] : i in [1..len1]];
        b1 := [b[2*i] : i in [1..len1]];
        c1 := [F!0 : i in [1..2*len1-1]];
        poly_mul_selfreciprocal(~c1, a1, len1, b1, len1, ~params);

        for i := 1 to len1 do
            f_add(~a0[i], a0[i], a1[i], ~params);
            f_add(~b0[i], b0[i], b1[i], ~params);
            if i+1 le len0 then
                f_add(~a0[i+1], a0[i+1], a1[i], ~params);
                f_add(~b0[i+1], b0[i+1], b1[i], ~params);
            end if;
        end for;
        
        c01 := [F!0 : i in [1..2*len0-1]];
        poly_mul_selfreciprocal(~c01, a0, len0, b0, len0, ~params);

        for i := 1 to 2*len0-1 do
            f_sub(~c01[i], c01[i], c0[i], ~params);
        end for;
        for i := 1 to 2*len1-1 do
            f_sub(~c01[i], c01[i], c1[i], ~params);
            if i+1 le 2*len0-1 then f_sub(~c01[i+1], c01[i+1], c1[i], ~params); end if;
            if i+1 le 2*len0-1 then f_sub(~c01[i+1], c01[i+1], c1[i], ~params); end if;
            if i+2 le 2*len0-1 then f_sub(~c01[i+2], c01[i+2], c1[i], ~params); end if;
        end for;
        
        for i := 2 to 2*len0-1 do
            f_sub(~c01[i], c01[i], c01[i-1], ~params);
        end for;

        for i := 1 to 2*len0-1 do c[2*i-1] := c0[i]; end for;
        for i := 1 to 2*len0-2 do c[2*i] := c01[i]; end for;
        for i := 1 to 2*len1-1 do f_add(~c[2*i+1], c[2*i+1], c1[i], ~params); end for;
        return;
    end if;

    if alen eq blen and (alen mod 2 eq 0) then
        half := alen div 2;
        c0 := [F!0 : i in [1..2*half-1]];
        c1 := [F!0 : i in [1..2*half-1]];
        
        poly_mul(~c0, a[1..half], b[1..half], ~params);
        poly_mul(~c1, a[1..half], b[half+1..alen], ~params);

        c := [F!0 : i in [1..2*alen-1]];
        for i := 1 to alen-1 do
            f_add(~c[i], c[i], c0[i], ~params);
            f_add(~c[2*alen-i], c[2*alen-i], c0[i], ~params);

            f_add(~c[half+i], c[half+i], c1[i], ~params);
            f_add(~c[alen+half-i], c[alen+half-i], c1[i], ~params);
        end for;
        return;
    end if;

    clen := alen + blen - 1;
    poly_mul_low(~c, clen div 2 + 1, a, b, ~params);
    
    for i := (clen div 2) + 1 to clen do
        c[i] := c[clen-i+1];
    end for;
end procedure;