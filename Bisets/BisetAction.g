#D_8 and its subgroups
D := SmallGroup(8, 3);;
V1 := Subgroup(D,[D.1, D.3]);;
V2 := Subgroup(D, [D.2,D.3]);;
C4 := Subgroup(D, [D.1 * D.2 * D.3]);;
Q1 := Subgroup(D, [D.1]);;
Q2 := Subgroup(D, [D.1 * D.3]);;
Q3 := Subgroup(D, [D.3]);;
Q4 := Subgroup(D, [D.2]);;
Q5 := Subgroup(D, [D.2 * D.3]);;
phi15 := IsomorphismGroups(Q1, Q5);;
phi51 := IsomorphismGroups(Q5, Q1);;

#Elements of D_8
rs := [1, "r^2", "rs", "r^3s", "s", "r^2s", "r^3", "r"];;
listD := List(D);;

#Finds right cosets of the twisted diagonal subgroup (P, phi) in G x H
RCD := function(G, H, P, phi)
    local cosetReps, listP, listP_phi, unionCosets, g_twd_h, g, h, twd;
    cosetReps := [];
    listP := List(P);
    if phi = 1 then
        phi := IdentityMapping(P);
    fi;
    listP_phi := List(listP, p -> [p, p^phi]);
    unionCosets := [];
    g_twd_h := [];
    for g in G do
        for h in H do
            for twd in listP_phi do
                Add(g_twd_h, [twd[1] * g, twd[2]] * h);
            od;
            if not IsSubset(unionCosets, g_twd_h) then
                Add(cosetReps, [g, h]);
                Append(unionCosets, g_twd_h);
            fi;
            g_twd_h := [];
        od;
    od;
    return cosetReps;
end;;

#Chosing a and b that act on the (S,S)-biset
a := D.1;;
b := D.3;;

BisetAction := function(S, twd, phi, a, b)
    local P, x, cosetReps, tw, h;
    P := Source(phi);
    x := twd[1] * a^-1;
    cosetReps := RCD(S, S, P, phi);
    for tw in cosetReps do
        for h in P do
            if x = h * tw[1] then
                return [tw[1], phi(h^-1) * twd[2] * b];
            fi;
        od;
    od;
end;;

#a and b act on the representatives of cosets of (Q1, phi15) in D x D
for twd in RCD(D, D, Q1, phi15) do
    ba := BisetAction(D, twd, phi15, a, b);
    Print("a * ", twd, " * b = ", ba, "\n");
    Print(rs[Position(listD, a)], " * ", "[", rs[Position(listD, twd[1])], ", ", rs[Position(listD, twd[2])], "] * ", rs[Position(listD, b)], " = ", 
        "[", rs[Position(listD, ba[1])], ", ", rs[Position(listD, ba[2])], "]\n\n");
od;



BisetProduct := function(S, twd1, twd2)
    local p, q, phiP, phiQ, comp, twd, tw, cosetReps, h, x;
    p := twd1[1];
    phiP := twd1[2];
    q := twd2[1];
    phiQ := twd2[2];
    if Image(phiP) = Source(phiQ) then
        comp := CompositionMapping(phiQ, phiP);
        twd := [p * q, comp];
        cosetReps := RCD(S, S, Source(comp), comp);
        for tw in cosetReps do
            for h in Source(comp) do
                if twd[1] = tw[1] * h  then
                    Print(twd1, " * ", twd2, " = ", twd, "\n");
                    return [h, (h^-1)^comp];
                fi;
            od;
        od;
        #Print(twd1, " * " twd2, " = ", );
    else
        Print(twd1, " * ", twd2, " = ", "undefined\n");
    fi;
end;;