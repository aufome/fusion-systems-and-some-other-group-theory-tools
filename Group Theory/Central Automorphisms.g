
CentralAutomorphisms := function(G)

    local autG, zG;

    autG := AutomorphismGroup(G);
    zG := Center(G);

    return Filtered(autG, alpha -> ForAll(G, g -> g^-1 * Image(alpha, g) in zG));

end;;


PrintCentralAuts := function(isocFamilies) 

    local isocFamily, G, index;
    index := 0;
    for isocFamily in isocFamilies do
        index := index + 1;
        Print("Family (", index, "):\n");
        #if IsAbelian(isocFamily[1]) then
        #    Print("Members of family (i) are abelian...\n");
        #    continue;
        #fi;
        for G in isocFamily do
            if IsAbelian(G) then
                continue;
            fi;
            Print("G = ", StructureDescription(G), ", and AutC(G) = ", StructureDescription(Group(CentralAutomorphisms(G))), "\n");
        od;
        Print("\n");
    od;

end;;