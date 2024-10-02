
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


AreIsomFS := function (fs1 ,fs2)

	local f1, f2, A, B, f, gg, gensA, fTOg, f1TOf2, I, a, ii;

	if IsMapping(fs1[1]) then
		f1 := fs1;
	else
		f1 := fs1[1];
	fi;

	if IsMapping(fs2[1]) then
		f2 := fs2;
	else
		f2 := fs2[1];
	fi;

	if Size(f1) <> Size(f2) then return false; fi;
	if IdGroup(Source(f1[1])) <> IdGroup(Source(f2[1])) then return false; fi;

	f1TOf2 := true;
	fTOg := false;
	I := AllIsomorphisms(Source(f1[1]), Source(f2[1]));
	if not IsEmpty(I) then
		for  ii in I do
			f1TOf2 := true;
		
			for f in f1 do
				A := Source(f);
				gensA := GeneratorsOfGroup(A);
				
				for gg in f2 do
					B := Source(gg);
					
					if not(Size(A) = Size(B)) then fTOg := false; continue; fi;
						
					fTOg := true;
					for a in gensA do
						if not (a^ii in B) then fTOg := false; break; fi;
							
						if (a^f)^ii <> (a^ii)^gg then
							fTOg := false;
								break;
						fi;
					od;
					
					if fTOg then break; fi;
				od;
			
				f1TOf2 := fTOg and f1TOf2;
				if not f1TOf2 then break; fi;
			od;
			
			if f1TOf2 then break; fi;
	od;
	fi;

	return f1TOf2 and fTOg;
end;;

OuterAutomorphismGroup := function(G)

	local innG, autG;

	autG := AutomorphismGroup(G);
	innG := InnerAutomorphismsAutomorphismGroup(autG);

	return autG / innG;
end;;

InverseIsom := function(f)

	local S, gensS, g, gensImage;

	S := Source(f);
	gensS := GeneratorsOfGroup(S);
	gensImage := [];

	for g in gensS do
		Add(gensImage, g^f);
	od;

	return GroupHomomorphismByImages(Image(f), Source(f), gensImage, gensS);
end;;


ConstructFS := function (AutS, more...)

	local maps, S, autE, bucket, fs, subsS, trivialSubS, P, alpha, f, subsE, E, sourcef, g, e, fInMaps, i, j, k, comp, esscomb;

	maps := ShallowCopy(Elements(AutS));
	S := Source(maps[1]);
	bucket := [];


	fs := [];

	subsS := AllSubgroups(S);
	Remove(subsS);
	trivialSubS := Remove(subsS, 1);

	for P in subsS do
		for alpha in maps do
			f := RestrictedMapping(alpha, P);
			if not (f in bucket) then
				Add(bucket, f);
			fi;
		od;
	od;
	Append(maps, Reversed(bucket));

	bucket := [];

	esscomb := Flat(more);
	if not IsEmpty(esscomb) then    
		for autE in esscomb do
			subsE := AllSubgroups(Source(autE.1));
			Remove(subsE,1);
			for alpha in autE do             
				for E in subsE do
					f := RestrictedMapping(alpha, E);
					for g in maps do
						fInMaps := true;
						for e in GeneratorsOfGroup(E) do
							if Source(f) <> Source(g) then 
								fInMaps:= false; 
								continue; 
							fi; 
							if e^g <> e^f then
								fInMaps := false;
								break;
							fi;
						od;
						if fInMaps then 
							break;
						fi;
					od;
					if not fInMaps then 
						Add(maps, f);
						Add(bucket, f);
					fi;
				od;
			od;
		od;
	fi;

	
	for i in [1..Size(bucket) - 1] do

		for k in [1..Size(maps)] do
			if Source(maps[k]) = Image(bucket[i]) then
				comp := CompositionMapping(maps[k], bucket[i]);
				if not comp in maps then
					Add(maps, comp);
					Add(maps, InverseIsom(comp));
				fi;
			fi;

		od;

		for j in [i + 1..Size(bucket)] do
			if Source(bucket[j]) = Image(bucket[i]) then
				comp := CompositionMapping(bucket[j], bucket[i]);
				if not comp in maps then
					Add(maps, comp);
					Add(maps, InverseIsom(comp));
				fi;
			fi;
		od;
	od; 
	Add(maps, IdentityMapping(trivialSubS));


	return maps;
end;;




PotentialCentrics := function (S)

	local potentialCentrics, P;

	potentialCentrics := [ ];
	for P in AllSubgroups(S) do
		if (Centralizer(S, P) = Center(P)) and (P <> S) then
			Add(potentialCentrics, P);
			StructureDescription(P);
		fi;
	od;

	return potentialCentrics;
end;;



AllSaturatedFusionSystems := function(S)

	local index, indexx, fs, AutS, InnS, FAutS, subAutS, fautS, prime, potentialCentrics,
	potentialCentricsClasses, essentialClass, class, hasClass, 
	syl_AutS, fusionSystems, P, Q, alpha, ccAutS,
	essentials, C, autC, autSubC, innC, cl,
	essentialAutGroups,
	i, j, indices, f;

	if not IsPGroup(S) then return fail; fi;

	prime := PrimePGroup(S);
	AutS := AutomorphismGroup(S);
	InnS := InnerAutomorphismsAutomorphismGroup(AutS);
	potentialCentrics := PotentialCentrics(S);

	syl_AutS := SylowSubgroup(AutS, prime);

	if IsPGroup(AutS) then 
		FAutS := [InnS];
	else
		FAutS := [];
		ccAutS := ConjugacyClassesSubgroups(AutS);
		for i in [1..Size(ccAutS)] do
			#if Size(InnS) = Size(SylowSubgroup(Representative(ccAutS[i])), prime) then
			subAutS := Representative(ccAutS[i]);
			if IsMapping(IsomorphismGroups(InnS, SylowSubgroup(subAutS, prime))) then
				for j in [1..Size(ccAutS[i])] do
					if IsSubgroup(ClassElementLattice(ccAutS[i], j), InnS) then
						Add(FAutS, subAutS);
						break;
					fi;
				od;
			fi;
		od;
	fi;

	List(potentialCentrics, g -> StructureDescription(g));



	fs := [];

	for fautS in FAutS do
		potentialCentricsClasses := [];
		hasClass := [];
		
		for index in [1..Size(potentialCentrics)] do
			class := [];
			if index in hasClass then continue; fi;
			P := potentialCentrics[index];
			Add(class, P);
			Add(hasClass, index);
			for indexx in [1..Size(potentialCentrics)] do
				if indexx in hasClass then continue; fi;
				Q := potentialCentrics[indexx];
				for f in fautS do
					if Image(f, P) = Q then
						Add(class, Q);
						Add(hasClass, indexx);
					fi;
				od;
			od;
			Add(potentialCentricsClasses, class);
		od;
		
		essentials := [];
		
		
		for cl in potentialCentricsClasses do
			essentialAutGroups := [];
			essentialClass := [];
			for index in [1..Size(cl)] do
				C := cl[index];
				autC := AutomorphismGroup(C);
				innC := InnerAutomorphismsAutomorphismGroup(autC);
				for autSubC in List(ConjugacyClassesSubgroups(autC), Representative) do
					f := IsomorphicSubgroups(autSubC, innC:findall:=false);
					if not IsEmpty(f) then
						if IsNormal(autSubC, Image(f[1])) then
							if ContainsStronglyPEmbedded(autSubC / Image(f[1]), prime) then 
								Add(essentialClass, [autSubC]);
							fi;
						fi;
					fi;
				od;
			od;
			Add(essentials, essentialClass);
		od;
		essentials := Filtered(essentials, c -> not IsEmpty(c));
		
		
		if IsEmpty(essentials) then
			Add(fs, ConstructFS(fautS));
		else
			for indices in IteratorOfCombinations([1..Size(essentials)]) do
				Add(fs, ConstructFS(fautS, essentials{indices}));
			od;
		fi;
		
	od;




	#In this part, we sort through isomorphic fusion systems
	indices := [];
	for i in [1..Size(fs)] do
		if i in Flat(indices) then continue; fi;
		indices[i] := [i];
		for j in [i..Size(fs)] do
			if i = j then continue; fi;
			if j in Flat(indices) then continue; fi;
			if AreIsomFS(fs[i], fs[j]) then
				Add(indices[i], j);
			fi;
		od;
	od;

	indices := List(indices, i -> i[1]);

	#return essentials;
	return fs{Flat(indices)};
end;;