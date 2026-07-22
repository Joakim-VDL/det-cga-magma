procedure poly_pseudoreciprocal(~d, ~r, rlen, m, mdeg, ~params)
    r := [ params`base_field | 0 : j in [1 .. rlen] ];
    if mdeg eq 0 then
        r := [params`base_field | 0 : i in [1..rlen-1]] cat [params`base_field!1];
        d := m[1]; 
        return;
    end if;

    if rlen eq 1 then
        r := [params`base_field | 1];
        d := m[mdeg+1];
        return;
    end if;

    if rlen eq 2 then
        r[2] := m[mdeg+1];
        f_neg(~r[1], m[mdeg], ~params);
        f_sqr(~d, m[mdeg+1], ~params);
        return;
    end if;

    if mdeg ge rlen then
        offset := mdeg - (rlen - 1);
        m := m[offset+1 .. #m]; 
        mdeg := rlen - 1;
    end if;

    top := (rlen + 1) div 2;
    bot := rlen - top;
    
    s := [params`base_field | 0 : i in [1..top]];
    
    poly_pseudoreciprocal(~d, ~s, top, m, mdeg, ~params);

    eps := [params`base_field | 0 : i in [1..mdeg]];
    poly_mul_low(~eps, mdeg, m, s, ~params);

    epss := [params`base_field | 0 : i in [1..bot]];
    poly_mul_high(~epss, mdeg + top - bot - 1, eps, s, ~params);

    for i := 1 to bot do
        f_neg(~r[i], epss[i], ~params);
    end for;
    
    for i := 1 to top do
        f_mul(~r[i+bot], s[i], d, ~params);
    end for;

    f_sqr(~d, d, ~params);
end procedure;

function poly_tree1size(n)
    if n le 1 then return 0; end if;
    if n eq 2 then return 3; end if;
    if n eq 3 then return 7; end if;
    
    m := n div 2;
    left := poly_tree1size(m);
    right := poly_tree1size(n - m);
    return left + right + n + 1;
end function;

procedure poly_tree1(~T, offset, P, P_offset, n, ~params)
    if n le 1 then return; end if;

    if n eq 2 then
        poly_mul(~tmp, P[P_offset + 1 .. P_offset + 2], P[P_offset + 3 .. P_offset + 4], ~params);
        for i := 1 to 3 do T[offset + i] := tmp[i]; end for;
        return;
    end if;

    if n eq 3 then
        poly_mul(~tmp1, P[P_offset + 1 .. P_offset + 2], P[P_offset + 3 .. P_offset + 4], ~params);
        for i := 1 to 3 do T[offset + i] := tmp1[i]; end for;
        poly_mul(~tmp2, T[offset + 1 .. offset + 3], P[P_offset + 5 .. P_offset + 6], ~params);
        for i := 1 to 4 do T[offset + 3 + i] := tmp2[i]; end for;
        return;
    end if;

    m := n div 2;
    left := poly_tree1size(m);
    right := poly_tree1size(n - m);
    poly_tree1(~T, offset, P, P_offset, m, ~params);
    poly_tree1(~T, offset + left, P, P_offset + 2 * m, n - m, ~params);

    left_root := T[offset + left - (m + 1) + 1 .. offset + left];
    right_root := T[offset + left + right - (n - m + 1) + 1 .. offset + left + right];

    poly_mul(~tmp, left_root, right_root, ~params);
    for i := 1 to n + 1 do T[offset + left + right + i] := tmp[i]; end for;
end procedure;

ProjRecord := recformat<x, z>;

function poly_eval_precomputesize(flen)
    if flen le 2 then return 0; end if;
    return flen;
end function;

procedure poly_eval_precompute(~precomp, flen, P, ~params)
    if flen le 2 then return; end if;

    pxpow := [params`base_field | 0 : i in [1..flen]];
    pzpow := [params`base_field | 0 : i in [1..flen]];

    pxpow[1] := P`x;
    pzpow[1] := P`z;

    for i := 2 to flen - 1 do
        f_mul(~pxpow[i], pxpow[i-1], P`x, ~params);
        f_mul(~pzpow[i], pzpow[i-1], P`z, ~params);
    end for;

    precomp := [params`base_field | 0 : i in [1..flen]];
    precomp[1] := pzpow[flen-1];
    precomp[flen] := pxpow[flen-1];
    
    for i := 2 to flen - 1 do
        f_mul(~precomp[i], pxpow[i-1], pzpow[flen-i], ~params);
    end for;
end procedure;

procedure poly_eval_postcompute(~v, f, flen, P, precomp, ~params)
    assert flen gt 0;
    
    if flen eq 1 then
        v := f[1]; 
        return;
    end if;

    if flen eq 2 then
        f_mul(~v, f[1], P`z, ~params); 
        f_mul(~tmp, f[2], P`x, ~params); 
        f_add(~v, v, tmp, ~params);
        return;
    end if;

    f_mul(~v, f[1], precomp[1], ~params);
    for i := 2 to flen do
        f_mul(~tmp, f[i], precomp[i], ~params);
        f_add(~v, v, tmp, ~params);
    end for;
end procedure;

function poly_pseudoremainder_precomputesize(glen, flen)
    assert flen ge glen;
    if flen eq glen then return 0; end if;
    vlen := flen - glen;
    return vlen + 1;
end function;

procedure poly_pseudoremainder_precompute(~precomp, glen, flen, m, ~params)
    assert flen ge glen;
    if flen eq glen then return; end if;
    vlen := flen - glen;
    
    poly_pseudoreciprocal(~d, ~s, vlen, m, glen, ~params);
    precomp := [d] cat s;
end procedure;

procedure poly_pseudoremainder_postcompute(~g, glen, f, flen, m, precomp, ~params)
    assert flen ge glen;

    if flen eq glen then
        g := f[1..glen];
        return;
    end if;

    vlen := flen - glen;
    d := precomp[1];
    v := precomp[2..#precomp];

    poly_mul_high(~vf, flen - 1, v, f, ~params);

    poly_mul_low(~qm, glen, vf, m, ~params);

    g := [params`base_field | 0 : i in [1..glen]];
    for i := 1 to glen do
        f_mul(~term, f[i], d, ~params);
        f_sub(~g[i], term, qm[i], ~params);
    end for;
end procedure;

function poly_multieval_unscaled_precomputesize(n, flen)
    if n le 0 then return 0; end if;
    if n eq 1 then
        return poly_eval_precomputesize(flen);
    end if;
    
    m := n div 2;
    if flen le n then
        return poly_multieval_unscaled_precomputesize(m, flen) + 
               poly_multieval_unscaled_precomputesize(n - m, flen);
    end if;
    
    if n eq 2 then
        return poly_pseudoremainder_precomputesize(n, flen) + 
               poly_multieval_unscaled_precomputesize(1, n) + 
               poly_multieval_unscaled_precomputesize(1, n);
    end if;
    
    if n eq 3 then
        return poly_pseudoremainder_precomputesize(n, flen) + 
               poly_multieval_unscaled_precomputesize(2, n) + 
               poly_multieval_unscaled_precomputesize(1, n);
    end if;
    
    return poly_pseudoremainder_precomputesize(n, flen) + 
           poly_multieval_unscaled_precomputesize(m, n) + 
           poly_multieval_unscaled_precomputesize(n - m, n);
end function;


procedure poly_multieval_unscaled_precompute(~precomp, n, flen, P, T, ~params, ~idx)
    if n le 0 then return; end if;

    if n eq 1 then
        Pp := rec<ProjRecord | x := -P[1], z := P[2]>;
        poly_eval_precompute(~sub_precomp, flen, Pp, ~params);
        for i := 1 to #sub_precomp do precomp[idx + i] := sub_precomp[i]; end for;
        idx +:= #sub_precomp;
        return;
    end if;

    m := n div 2;
    left := poly_tree1size(m);

    if flen le n then
        poly_multieval_unscaled_precompute(~precomp, m, flen, P, T, ~params, ~idx);
        poly_multieval_unscaled_precompute(~precomp, n - m, flen, P[2*m+1..#P], T[left+1..#T], ~params, ~idx);
        return;
    end if;

    if n eq 2 then
        poly_pseudoremainder_precompute(~rem_precomp, n, flen, T, ~params);
        for i := 1 to #rem_precomp do precomp[idx + i] := rem_precomp[i]; end for;
        idx +:= #rem_precomp;
        
        poly_multieval_unscaled_precompute(~precomp, 1, n, P, [], ~params, ~idx);
        poly_multieval_unscaled_precompute(~precomp, 1, n, P[3..#P], [], ~params, ~idx);
        return;
    end if;

    if n eq 3 then
        poly_pseudoremainder_precompute(~rem_precomp, n, flen, T[4..#T], ~params);
        for i := 1 to #rem_precomp do precomp[idx + i] := rem_precomp[i]; end for;
        idx +:= #rem_precomp;
        
        poly_multieval_unscaled_precompute(~precomp, 2, n, P, T, ~params, ~idx);
        poly_multieval_unscaled_precompute(~precomp, 1, n, P[5..#P], [], ~params, ~idx);
        return;
    end if;

    right := poly_tree1size(n - m);
    poly_pseudoremainder_precompute(~rem_precomp, n, flen, T[left+right+1..#T], ~params);
    for i := 1 to #rem_precomp do precomp[idx + i] := rem_precomp[i]; end for;
    idx +:= #rem_precomp;
    
    poly_multieval_unscaled_precompute(~precomp, m, n, P, T, ~params, ~idx);
    poly_multieval_unscaled_precompute(~precomp, n - m, n, P[2*m+1..#P], T[left+1..#T], ~params, ~idx);
end procedure;

procedure poly_multieval_unscaled_postcompute(~v, n, f, flen, P, T, precomp, ~params, ~idx)
    if n le 0 then return; end if;

    if n eq 1 then
        Pp := rec<ProjRecord | x := -P[1], z := P[2]>;
        poly_eval_postcompute(~v[1], f, flen, Pp, precomp[idx+1..idx+flen], ~params);
        idx +:= flen; 
        return;
    end if;

    m := n div 2;
    left := poly_tree1size(m);

    if flen le n then
        poly_multieval_unscaled_postcompute(~v, m, f, flen, P, T, precomp, ~params, ~idx);
        poly_multieval_unscaled_postcompute(~v_slice, n - m, f, flen, P[2*m+1..#P], T[left+1..#T], precomp, ~params, ~idx);
        for i := 1 to n - m do v[m + i] := v_slice[i]; end for;
        return;
    end if;

    g := [params`base_field | 0 : i in [1..n]];

    if n eq 2 then
        poly_pseudoremainder_postcompute(~g, n, f, flen, T, precomp[idx+1..idx+poly_pseudoremainder_precomputesize(n, flen)], ~params);
        idx +:= poly_pseudoremainder_precomputesize(n, flen);
        
        poly_multieval_unscaled_postcompute(~v1, 1, g, n, P, [], precomp, ~params, ~idx);
        v[1] := v1[1];
        poly_multieval_unscaled_postcompute(~v2, 1, g, n, P[3..#P], [], precomp, ~params, ~idx);
        v[2] := v2[1];
        return;
    end if;

    if n eq 3 then
        poly_pseudoremainder_postcompute(~g, n, f, flen, T[4..#T], precomp[idx+1..idx+poly_pseudoremainder_precomputesize(n, flen)], ~params);
        idx +:= poly_pseudoremainder_precomputesize(n, flen);

        poly_multieval_unscaled_postcompute(~v_sub, 2, g, n, P, T, precomp, ~params, ~idx);
        for i := 1 to 2 do v[i] := v_sub[i]; end for;
        poly_multieval_unscaled_postcompute(~v_last, 1, g, n, P[5..#P], [], precomp, ~params, ~idx);
        v[3] := v_last[1];
        return;
    end if;

    right := poly_tree1size(n - m);
    poly_pseudoremainder_postcompute(~g, n, f, flen, T[left+right+1..#T], precomp[idx+1..idx+poly_pseudoremainder_precomputesize(n, flen)], ~params);
    idx +:= poly_pseudoremainder_precomputesize(n, flen);
    
    poly_multieval_unscaled_postcompute(~v_left, m, g, n, P, T, precomp, ~params, ~idx);
    poly_multieval_unscaled_postcompute(~v_right, n - m, g, n, P[2*m+1..#P], T[left+1..#T], precomp, ~params, ~idx);
    
    for i := 1 to m do v[i] := v_left[i]; end for;
    for i := 1 to n - m do v[m + i] := v_right[i]; end for;
end procedure;


procedure poly_multieval_scaled(~v, n, r, P, T, offset, ~params)
    if n le 0 then return; end if;
    if n eq 1 then
        v[1] := r[1];
        return;
    end if;

    if n eq 2 then
        g_left := [params`base_field | 0];
        poly_mul_mid(~g_left, 1, 1, r, 2, P[3..4], 2, ~params);
        v_left := [params`base_field | 0];
        poly_multieval_scaled(~v_left, 1, g_left, P, T, 0, ~params);
        
        g_right := [params`base_field | 0];
        poly_mul_mid(~g_right, 1, 1, r, 2, P[1..2], 2, ~params);
        v_right := [params`base_field | 0];
        poly_multieval_scaled(~v_right, 1, g_right, P[3..#P], T, 0, ~params);
        
        v[1] := v_left[1];
        v[2] := v_right[1];
        return;
    end if;

    if n eq 3 then
        g_left := [params`base_field | 0 : i in [1..2]];
        poly_mul_mid(~g_left, 1, 2, r, 3, P[5..6], 2, ~params);
        v_left := [params`base_field | 0 : i in [1..2]];
        poly_multieval_scaled(~v_left, 2, g_left, P, T, offset, ~params);
        
        g_right := [params`base_field | 0];
        poly_mul_mid(~g_right, 2, 1, r, 3, T[offset + 1 .. offset + 3], 3, ~params);
        v_right := [params`base_field | 0];
        poly_multieval_scaled(~v_right, 1, g_right, P[5..#P], T, 0, ~params);
        
        v[1] := v_left[1];
        v[2] := v_left[2];
        v[3] := v_right[1];
        return;
    end if;

    m := n div 2;
    left := poly_tree1size(m);
    right := poly_tree1size(n - m);

    g_left := [params`base_field | 0 : i in [1..m]];
    right_root_start := offset + left + right - (n - m + 1) + 1;
    right_root_slice := T[right_root_start .. right_root_start + (n - m)];
    poly_mul_mid(~g_left, n - m, m, r, n, right_root_slice, n - m + 1, ~params);
    
    v_left := [params`base_field | 0 : i in [1..m]];
    poly_multieval_scaled(~v_left, m, g_left, P, T, offset, ~params);

    g_right := [params`base_field | 0 : i in [1..n - m]];
    left_root_start := offset + left - (m + 1) + 1;
    left_root_slice := T[left_root_start .. left_root_start + m];
    poly_mul_mid(~g_right, m, n - m, r, n, left_root_slice, m + 1, ~params);
    
    v_right := [params`base_field | 0 : i in [1..n - m]];
    poly_multieval_scaled(~v_right, n - m, g_right, P[2*m + 1 .. #P], T, offset + left, ~params);

    for i := 1 to m do v[i] := v_left[i]; end for;
    for i := 1 to n - m do v[m + i] := v_right[i]; end for;
end procedure;
function poly_multieval_chooseunscaled(n, flen)
    if n le 1 then return true; end if;
    if flen le 1 then return true; end if;
    return false;
end function;

function poly_multieval_precomputesize(n, flen)
    if poly_multieval_chooseunscaled(n, flen) then
        return poly_multieval_unscaled_precomputesize(n, flen);
    end if;
    if flen lt n then flen := n; end if;
    return flen;
end function;

procedure poly_multieval_precompute(~precomp, n, flen, P, T, ~params)
    if poly_multieval_chooseunscaled(n, flen) then
	idx := 0;
        poly_multieval_unscaled_precompute(~precomp, n, flen, P, T, ~params, ~idx);
        return;
    end if;
    
    if flen lt n then flen := n; end if;
    m := n div 2;
    left := poly_tree1size(m);
    right := poly_tree1size(n - m);
    
    slice_start := left + right + 1;
    slice_end := slice_start + n; 
    root_poly := T[slice_start .. slice_end];

    denom_seq := [params`base_field | 0]; 
    poly_pseudoreciprocal(~denom_seq, ~precomp, flen, root_poly, n, ~params);
end procedure;

procedure poly_multieval_postcompute(~v, n, f, flen, P, T, precomp, ~params)
    if poly_multieval_chooseunscaled(n, flen) then
        idx:= 0;
        poly_multieval_unscaled_postcompute(~v, n, f, flen, P, T, precomp, ~params, ~idx);
        return;
    end if;

    f_local := f;
    if flen lt n then
        f_local := [params`base_field | 0 : i in [1..n]];
        for i := 1 to flen do f_local[i] := f[i]; end for;
        flen := n;
    end if;

    rootinv := precomp[1..flen]; 
    frootinv := [params`base_field | 0 : i in [1..n]];
    
    poly_mul_mid(~frootinv, flen - 1, n, f_local, flen, rootinv, flen, ~params);
    
    poly_multieval_scaled(~v, n, frootinv, P, T, 0, ~params);
end procedure;

procedure poly_multiprod2(~T, n, offset, ~params)
    if n le 1 then return; end if;

    m := n div 2;

    poly_multiprod2(~T, m, offset, ~params);
    poly_multiprod2(~T, n - m, offset + 3*m, ~params);

    poly1 := T[offset + 1 .. offset + 2*m + 1];
    poly2 := T[offset + 3*m + 1 .. offset + 3*m + 2*(n - m) + 1];

    poly_mul(~X, poly1, poly2, ~params);

    for i := 1 to 2*n + 1 do
        T[offset + i] := X[i];
    end for;
end procedure;
procedure poly_multiprod2_selfreciprocal(~T, n, offset, ~params)
    if n le 1 then return; end if;

    m := n div 2;
    
    poly_multiprod2_selfreciprocal(~T, m, offset, ~params);
    poly_multiprod2_selfreciprocal(~T, n - m, offset + 3*m, ~params);

    left := T[offset+1 .. offset + 2*m + 1];
    right := T[offset + 3*m + 1 .. offset + 3*m + 2*(n-m) + 1];

    poly_mul_selfreciprocal(~X, left, #left, right, #right, ~params);

    for i := 1 to #X do
        T[offset + i] := X[i];
    end for;
end procedure;