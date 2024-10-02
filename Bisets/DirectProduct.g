
D := SmallGroup(8, 3);;
1_D := Subgroup(D, [Identity(D)]);;
DxD := DirectProduct(D, D);;
emb1 := Embedding(DxD, 1);;
emb2 := Embedding(DxD, 2);;
gensImage1 := List(GeneratorsOfGroup(D), x -> Image(emb1, x));;
gensImage2 := List(GeneratorsOfGroup(D), x -> Image(emb2, x));;
gensDiag := List([1..Length(gensImage2)], y -> gensImage1[y] * gensImage2[y]);;
1xD := Group(gensDiag);





G := DirectProduct(P, Q);
embP := Embedding(G, 1);
embQ := Embedding(G, 2);
gensImageP := List(GeneratorsOfGroup(P), x -> Image(embP, x));
gensImageQ := List(GeneratorsOfGroup(P), x -> Image(embQ,x^iso));
gensDiag := List([1..Length(gensImageP)], y -> gensImageP[y] * gensImageQ[y]);
diag := Group(gensDiag);


RC := function(G, H)
    local cosetReps, listH, unionCosets, g, h;
    cosetReps := [];
    listH := List(H);
    unionCosets := [];
    for g in G do
        if not IsSubset(unionCosets, g * listH) then
            Add(cosetReps, g);
            Append(unionCosets, g * listH);
        fi;
    od;
    return cosetReps;
end;;

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


for twd in RCD(D, D, Q1, phi15) do
    ba := BisetAction(D, twd, phi15, a, b);
    Print("a * ", twd, " * b = ", ba, "\n");
    Print(rs[Position(listD, a)], " * ", "[", rs[Position(listD, twd[1])], ", ", rs[Position(listD, twd[2])], "] * ", rs[Position(listD, b)], " = ", 
        "[", rs[Position(listD, ba[1])], ", ", rs[Position(listD, ba[2])], "]\n\n");
od;




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
                Add(g_twd_h, [g * twd[1], h * twd[2]]);
            od;
            if not IsSubset(unionCosets, g_twd_h) then
                Add(cosetReps, [g, h]);
                Append(unionCosets, g_twd_h);
            fi;
            g_twd_h := [];
        od;
    od;

    return List(cosetReps, rep -> [rep[1] * rep[1]^-1, rep[1]^phi * rep[2]]);
end;;











for size in [1..20] do
    for index in [1..NumberSmallGroups(size)] do
        G := SmallGroup(size, index);
        ccG := Filtered(List(ConjugacyClassesSubgroups(G), Representative), h -> IsNormal(G, h));
        Print(StructureDescription(G), ": \n");
        qG := List(ccG, h -> StructureDescription(G / h));
        Print("\tQuotients: "); Print(qG); Print("\n");
        qqG := List(ccG, h -> StructureDescription(Group(RC(G, h))));
        Print("\t  RC test: "); Print(qqG);
        Print("\n\n");
    od;
od;

DxD := [D, D];





