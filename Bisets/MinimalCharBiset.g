# This file has a function named MinimalCharacteristicBiset having a fusion system as an input.
# For a given abstract saturated fusion system F on a finite p-group S, this functinon returns
# the minimal characteristic biset appears as disjoint union of orbits of the form [n, P, phi].
# The bracket notation means that it is an (S, S) orbit that contains a point with stabilizer (P, phi)
# where P is a subgroup of S, phi is an F-isomorphism from P to S, and n is the number of copies of these orbits.
# To create a fusion system that is coherent with the input of this function, FusionSystem can be used.

# Returns the list of conjugator isomorphisms from P to Q given by G.
FindConjugatorIsomorphisms := function(G, P, Q)
	local maps, g, c_g;
	
	maps := [];

	for g in Elements(G) do
		
		if P^g = Q then
			c_g := ConjugatorIsomorphism(P, g);
			if not (c_g in maps) then
			Append(maps, [c_g]);
			fi;
		fi;
	od;
	return maps;
end;;

# Produces the fusion system of the group S given by G. We view fusion systems as a collection of monomorphisms.
# Returns a list of monomorphisms (F-isomorphisms) of the fusion system.
# F-isomorphisms in "maps[index]" subject to being sorted by the size of their source.
# Note that, for each conjugacy class that contains an isomorphic copy of S, this function returns a fusion system.
# Each fusion system is contained in a single list.
FusionSystem := function (S, G)
	local maps, ccG, reps, SinG, fs, allsubgroups, pairsOfSubgroups, ccS, i;

	maps := [];
	ccG := ConjugacyClassesSubgroups(G);
	
	if not IsSubgroup(G, S) then
		reps := Filtered(List(ccG, Representative), i -> Size(i) = Size(S));
		reps := Filtered(reps, i -> IdGroup(i) = IdGroup(S));
		
		for SinG in reps do
			fs := FusionSystem(SinG, G);
			Append(maps, fs);
		od;
		return maps;
	else
		SinG := S;
	fi;

	pairsOfSubgroups := [];


	allsubgroups := AllSubgroups(SinG);
	
	for i in [Size(SinG), Size(SinG) - 1..1] do
		Append(pairsOfSubgroups, Tuples(Filtered(allsubgroups, H->Size(H)=i),2));
	od;


	for i in [1..Size(pairsOfSubgroups)] do
		Append(maps, FindConjugatorIsomorphisms(G, pairsOfSubgroups[i][1], pairsOfSubgroups[i][2]));

	return [maps];
end;;

# Finds all F-conjugacy classes of a given fusion system.
# Returns the list of F-conjugacy classes. Note that an F-conjugacy class is a list whose members subgroups of S that are F-isomorphic to each other.
FConjugacyClasses := function(fs)
	local maps, fclasses, notFound, ti, H, f;

	if IsMapping(fs[1]) then
		maps := fs;
	else
		maps := fs[1];
	fi;

	fclasses := [];

	for f in maps do
		notFound := true;	
		for ti in [1..Size(fclasses)] do
			for H in fclasses[ti] do
				if H = Source(f) then
					fclasses[ti] := Union(fclasses[ti],[Image(f)]);
					notFound := false;
				fi;
				if H = Image(f) then
					fclasses[ti] := Union(fclasses[ti],[Source(f)]);
					notFound := false;
				fi;
			od;
		od;
		if notFound then
			Append(fclasses,[Union([Source(f)],[Image(f)])]);
		fi;
	od;
			
	return fclasses;
end;;

# Sorts through F-isomorphisms which are F-automorphisms.
FAutomorphismGroup := function (P, fs)
	local maps;

	if IsMapping(fs[1]) then
		maps := fs;
	else
		maps := fs[1];
	fi;

	return Group(Filtered(maps, x -> Source(x) = P and P = Image(x)));
end;;

#For a given fusion system F, this function returns a list of subgroups that are fully F-centralized.
#These subgroups are seperated by their F-classes.
FullyFCentralizedSubgroups := function (fs)
	local maps, S, fullycentralized, fclasses, i, pos;

	if IsMapping(fs[1]) then
		maps := fs;
	else
		maps := fs[1];
	fi;

	S := Source(maps[1]);
	fullycentralized := [];
	fclasses := FConjugacyClasses(maps);

	for i in [1..Size(fclasses)] do
		pos := PositionMaximum(fclasses[i],x->Size(Centralizer(S,x)));
		
		Append(fullycentralized,[Filtered(fclasses[i],x->Size(Centralizer(S,fclasses[i][pos])) = Size(Centralizer(S,x)))]);
	od;

	return fullycentralized;
end;;

# Finds the representatives of Aut_F(P)/Inn(P).
# If the "reps" option set to false, the function returns the quotient group.
FOuterAutomorphismGroup := function (P, fs)
	local maps, fautP, innP, copyinnP;

	if IsMapping(fs[1]) then
		maps := fs;
	else
		maps := fs[1];
	fi;

	fautP := FAutomorphismGroup(P,maps);
	StructureDescription(fautP);
	innP := InnerAutomorphismsAutomorphismGroup(AutomorphismGroup(P));
	copyinnP := Image(IsomorphicSubgroups(fautP,innP:findall:=false)[1]);

	if (ValueOption("reps") = false) then
		if IsNormal(fautP, copyinnP) then
			return fautP / copyinnP;
		else
			return fail;
		fi;
	else
		return RightTransversal(fautP, copyinnP);
	fi;
end;;

# Returns a list F-centric subgroups, which are seperated by their F-classes.
# Using two facts: i. Centric subgroups are fully centralized. ii. Being centric is a property that all members of an F-class enjoy.
FCentricSubgroups := function (fs)
	local maps, fullyFcentralizeds, centrics, S;

	if IsMapping(fs[1]) then
		maps := fs;
	else
		maps := fs[1];
	fi;

	S := Source(maps[1]);
	fullyFcentralizeds := FullyFCentralizedSubgroups(maps);
	centrics := Filtered(fullyFcentralizeds, x-> Centralizer(S, x[1]) = Center(x[1]) );

	return centrics;
end;;

# Checks whether a given group contains strongly p-embedded subgroup.
# Using Proposition A.7 in "Fusion Systems in Algebra and Topology", AKO.
# Returns "true" or "false".
ContainsStronglyPEmbedded := function(G,p)
	local S, H_S, H, elements;

	elements := Elements(G);
	S := SylowSubgroup(G,p);

	if IsNormal(G,S) then return false; fi;
	H_S := Filtered(elements, x -> not IsTrivial(Intersection(S, S^x)));
	H := Group(H_S);
	if H = G then return false; fi;
	#Print(StructureDescription(H)," is strongly ", p, "-embedded subgroup of ", StructureDescription(G), ".\n");
	return true;
end;;

# Returns a list of F-essential subgroups, which are seperated by their F-classes.
# Centrics whose F-outer automorphism groups contain a strongly p-embedded subgroup are essentials.
# Being F-essential is a shared property by all subgroups in an F-class. 
FEssentialSubgroups := function(fs)
	local maps, centrics, essentials, p;

	if IsMapping(fs[1]) then
		maps := fs;
	else
		maps := fs[1];
	fi;

	p := PrimePGroup(Source(maps[1]));
	centrics := FCentricSubgroups(maps);
	essentials := Filtered(centrics, x -> ContainsStronglyPEmbedded(FOuterAutomorphismGroup(x[1], maps:reps:=false), p));

	return essentials;
end;;


FIsomorphisms := function(P, fs)
	local maps;

	if IsMapping(fs[1]) then
		maps := fs;
	else
		maps := fs[1];
	fi;

	return Filtered(maps, x -> Source(x) = P);
end;;

TwistedDiagonalSubgroup := function(SxS, P, f)
	local Q, emb1st, emb2nd, gensImageP, gensImageQ, gensDiagonal;
	
	Q := Image(f);
	emb1st := Embedding(SxS, 1);
	emb2nd := Embedding(SxS, 2);
	gensImageP := List(GeneratorsOfGroup(P), x -> Image(emb1st, x));
	gensImageQ := List(GeneratorsOfGroup(P), x -> Image(emb2nd, x^f));
	gensDiagonal := List([1..Length(gensImageP)], x -> gensImageP[x] * gensImageQ[x]);

	return Subgroup(SxS,gensDiagonal);
end;;


NumberOfFixedPoints := function (S,Q,P) 
	local t, elemS, i;
	
	elemS := Elements(S);;
	t := [];
	for i in [1..Size(elemS)] do
		if IsSubgroup(Q,P^elemS[i]) then
			Append(t, [elemS[i]]);;
		fi;
	od;
	return Size(t)/Size(Q);
end;;


MinimalCharacteristicBiset := function (FS)

    local fs, biset, S, SxS, OuterS, essentials, E, EC, outerE, twistedDiagEf, twistedDiagEid,
            f, transitiveOrbit, numberOfFixedPointsEid, numberOfFixedPointsEf, 
            nonessentials, twistedDiagLid, twistedDiagLf, id, numberOfFixedPointsLid, numberOfFixedPointsLf, L;

    if IsMapping(FS[1]) then
        fs := FS;
    else
        fs := FS[1];
    fi;

    biset := [];
    S := Source(fs[1]);
    SxS := DirectProduct(S,S);
    OuterS := FOuterAutomorphismGroup(S, fs);
    Append(biset, List(OuterS, x -> [1,S,x]));


    essentials := FEssentialSubgroups(fs);

    for EC in essentials do
        for E in EC do
            outerE := FOuterAutomorphismGroup(E, fs);
            id := IdentityMapping(E);
            twistedDiagEid := TwistedDiagonalSubgroup(SxS, E, id);
            for f in Elements(outerE)do
                twistedDiagEf := TwistedDiagonalSubgroup(SxS,E,f);
                numberOfFixedPointsEf := 0;
                numberOfFixedPointsEid := 0;
                for transitiveOrbit in biset do
                    numberOfFixedPointsEf := numberOfFixedPointsEf + transitiveOrbit[1] * NumberOfFixedPoints(SxS, TwistedDiagonalSubgroup(SxS, transitiveOrbit[2], transitiveOrbit[3]), twistedDiagEf);
                    numberOfFixedPointsEid := numberOfFixedPointsEid + transitiveOrbit[1] * NumberOfFixedPoints(SxS, TwistedDiagonalSubgroup(SxS, transitiveOrbit[2], transitiveOrbit[3]), twistedDiagEid);
                od;
                if numberOfFixedPointsEf = 0 then 
                    #Print("Number of fixed points: ",NumberOfFixedPoints(SxS,twistedDiagEf,twistedDiagEf),"\n");
                    Append(biset, [[(numberOfFixedPointsEid - numberOfFixedPointsEf)/NumberOfFixedPoints(SxS, twistedDiagEf, twistedDiagEf),E, f]]); 
                fi;
            od;
        od;
    od;

    nonessentials := Difference(AllSubgroups(S), Union(essentials));
    nonessentials := Difference(nonessentials, [S, Source(fs[Size(fs)])]);

    SortBy(nonessentials, x -> -Order(x));
    
    for L in nonessentials do
        id := IdentityMapping(L);
        twistedDiagLid := TwistedDiagonalSubgroup(SxS, L, id);
        for f in FIsomorphisms(L, fs)do
            twistedDiagLf := TwistedDiagonalSubgroup(SxS,L,f);
            numberOfFixedPointsLf := 0;
            numberOfFixedPointsLid := 0;
            for transitiveOrbit in biset do
                numberOfFixedPointsLf := numberOfFixedPointsLf + transitiveOrbit[1] * NumberOfFixedPoints(SxS, TwistedDiagonalSubgroup(SxS, transitiveOrbit[2], transitiveOrbit[3]), twistedDiagLf);
                numberOfFixedPointsLid := numberOfFixedPointsLid + transitiveOrbit[1] * NumberOfFixedPoints(SxS, TwistedDiagonalSubgroup(SxS, transitiveOrbit[2], transitiveOrbit[3]), twistedDiagLid);
            od;
            #Print("L: ", StructureDescription(L),"\n numberOfFixedPointsEf: ", numberOfFixedPointsLf, "\n numberOfFixedPointsEE: ", numberOfFixedPointsLid, "\n");
            if numberOfFixedPointsLid > numberOfFixedPointsLf then 
                #Print("Number of fixed points: ",NumberOfFixedPoints(SxS,twistedDiagLf,twistedDiagLf),"\n"); 
                Append(biset, [[(numberOfFixedPointsLid - numberOfFixedPointsLf)/NumberOfFixedPoints(SxS, twistedDiagLf, twistedDiagLf), L, f]]);
            fi;
            
        od;
    od;
    #Print(nonessentials,"\n");
    List(biset,x->StructureDescription(x[2]));
    return biset;
end;;


UniversalFusionSystem := function (S)

	local allsubgroups, pairsOfSubgroups, maps, i, f;

	allsubgroups := AllSubgroups(S);
	pairsOfSubgroups := [];
	maps := [];

	for i in [Size(S),Size(S)-1..1] do
		Append(pairsOfSubgroups, Tuples(Filtered(allsubgroups, H->Size(H)=i),2));
	od;

	for i in [1..Size(pairsOfSubgroups)] do
		Append(maps, AllIsomorphisms(pairsOfSubgroups[i][1],pairsOfSubgroups[i][2]));
	od;
	return maps;
end;;

BisetToFS := function (biset)

local S, SxS, universalFS, fs, orbit, orbitReps, f;
S := biset[1][2];
SxS := DirectProduct(S,S);
universalFS := UniversalFusionSystem(S);
fs := [];
orbitReps := List(biset, x -> TwistedDiagonalSubgroup(SxS, x[2], x[3]));

for f in universalFS do
	for orbit in orbitReps do
		if NumberOfFixedPoints(SxS, orbit, TwistedDiagonalSubgroup(SxS, Source(f), f)) > 0 then
			Append(fs, [f]);
			break;
		fi;
		
	od;
od;

return fs;
end;;
