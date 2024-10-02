# This file has a function to create a fusion system F of a finite group of S given by a finite group G, 
# and has some other functions that returns F-centric, F-radical, F-essential, fully F-normalized, fully F-centralized subgroups.
# There is a function that returns the universal fusion system of a finite group.
# The file also contains functions that can return a minimal characteristic biset of a given fusion system F and the fusion system 
# of a given biset.

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

	if true then
		for i in [1..Size(pairsOfSubgroups)] do
			Append(maps, FindConjugatorIsomorphisms(G, pairsOfSubgroups[i][1], pairsOfSubgroups[i][2]));
		od;
	else
		for i in [1..Size(pairsOfSubgroups)] do
			Append(maps, Filtered(AllIsomorphisms(pairsOfSubgroups[i][1], pairsOfSubgroups[i][2]), f -> IsConjugatorIsomorphism(f) and ConjugatorOfConjugatorIsomorphism(f) in G));
		od;
	fi;

	return [maps];
end;;


FusionSystem2 := function (S, G)
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

	ccS := ConjugacyClassesSubgroups(SinG);
	for i in [Size(ccS), Size(ccS)-1..1] do
		Append(pairsOfSubgroups, Tuples(ccS[i], 2));
	od;


	if true then
		for i in [1..Size(pairsOfSubgroups)] do
			Append(maps, FindConjugatorIsomorphisms(G, pairsOfSubgroups[i][1], pairsOfSubgroups[i][2]));
		od;
	else
		for i in [1..Size(pairsOfSubgroups)] do
			Append(maps, Filtered(AllIsomorphisms(pairsOfSubgroups[i][1], pairsOfSubgroups[i][2]), f -> IsConjugatorIsomorphism(f) and ConjugatorOfConjugatorIsomorphism(f) in G));
		od;
	fi;

	return [maps];
end;;

######################

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

######################
# Checks whether given two subgroups in a fusion system F are F-isomorphic.
AreFIsom := function(P, Q, fs)
	local maps, map;
	if IsMapping(fs[1]) then
		maps := fs;
	else
		maps := fs[1];
	fi;

	for map in maps do
		if Source(map) = P and Image(map) = Q then
			return true;
		fi;
	od;
	return false;
end;;


######################
# Returns the F-conjugacy class of a given subgroup P in a given fusion system.
FConjugacyClassOf := function (P, fs)
	local maps;

	if IsMapping(fs[1]) then
		maps := fs;
	else
		maps := fs[1];
	fi;

	return Filtered(FConjugacyClasses(maps), x -> P in x);
end;;

######################
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

######################
# For a given fusion system F, this function returns a list of subgroups that are fully F-normalized.
# These subgroups are seperated by their F-classes.
FullyFNormalizedSubgroups := function (fs)
	local maps, S, fullynormalized, fclasses, i, pos;

	if IsMapping(fs[1]) then
		maps := fs;
	else
		maps := fs[1];
	fi;

	S := Source(maps[1]);
	fullynormalized := [];
	fclasses := FConjugacyClasses(maps);

	for i in [1..Size(fclasses)] do
		pos := PositionMaximum(fclasses[i],x->Size(Normalizer(S,x)));
		Append(fullynormalized, [Filtered(fclasses[i],x->Size(Normalizer(S,fclasses[i][pos])) = Size(Normalizer(S,x)))]);
	od;

	return fullynormalized;
end;;

######################
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

FIsomorphisms := function(P, fs)
	local maps;

	if IsMapping(fs[1]) then
		maps := fs;
	else
		maps := fs[1];
	fi;

	return Filtered(maps, x -> Source(x) = P);
end;;

######################
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

######################
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


######################
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


######################
# If a spesific prime (that divides the order of G) is not given, this functions calls "ContainsStronglyPEmbedded" for each prime divisor of the order of G. 
# Returns "true" once finding a strongly p-embedded subgroup of G.
ContainsStronglyEmbedded := function (G)
	local divisors, p;

	divisors := PrimeDivisors(Size(G));
	for p in divisors do
		if ContainsStronglyPEmbedded(G,p) then return true; fi;
	od;

	return false;
end;;

######################
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


FCentricRadicalSubgroups := function (fs)
	local maps, centrics, p;

	if IsMapping(fs[1]) then
		maps := fs;
	else
		maps := fs[1];
	fi;

	p := PrimePGroup(Source(maps[1]));
	centrics := FCentricSubgroups(maps);

	return Filtered(centrics, x -> IsMapping(IsomorphismGroups(PCore(FAutomorphismGroup(x[1], maps), p), InnerAutomorphismsAutomorphismGroup(AutomorphismGroup(x[1])))));
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


AreCoprime := function (m, n)
	if Intersection(PrimeDivisors(m), PrimeDivisors(n)) = [] then
	return true;
	fi;
	return false;
end;;



AutomorphismGroupGivenBy := function(P, S)

local NSP, CSP, reps;
NSP := Normalizer(S,P);
CSP := Centralizer(S,P);
reps := AsList(RightTransversal(NSP,CSP));

return Group(List(reps, x -> ConjugatorAutomorphism(P,x)));
end;;

InverseMapFS := function (phi, fs)

local maps, P, Q, idP, QtoP;

if IsMapping(fs[1]) then
	maps := fs;
else
	maps := fs[1];
fi;

P := Source(phi);
Q := Image(phi);
idP := IdentityMapping(P);
QtoP := Filtered(maps, f -> Source(f) = Q and Image(f) = P);

return First(QtoP, f -> phi * f = idP);
end;;

ExtenderSubgroup := function (phi, fs)

local maps, S, P, Q, N_phi, elemAutSQ, NSP, difference, n, c_n;

if IsMapping(fs[1]) then
	maps := fs;
else
	maps := fs[1];
fi;

S := Source(maps[1]);
P := Source(phi);
Q := Image(phi);
N_phi := ShallowCopy(Elements(P));
NSP := Elements(Normalizer(S, P));
elemAutSQ := Elements(AutomorphismGroupGivenBy(Q, S));
difference := Difference(NSP, P);

for n in difference do

c_n := ConjugatorAutomorphism(P, n);
if InverseMapFS(phi, maps) * c_n  * phi in elemAutSQ then
Append(N_phi, [n]);
fi;

od;

return Group(N_phi);
end;;


IsSaturatedFS := function (fs)

local maps, S, p, sylowAxiom, extAxiom, cl, Q, P, phi, N_phi, extensions, phi_tilde, a;

if IsMapping(fs[1]) then
	maps := fs;
else
	maps := fs[1];
fi;

sylowAxiom := false;
S := Source(maps[1]);
p := PrimeDivisors(Size(S))[1];

if AreCoprime(Size(FOuterAutomorphismGroup(S, maps)),p) then
	sylowAxiom := true;
fi;
	extAxiom := true;

if sylowAxiom then

for cl in FullyFNormalizedSubgroups(maps) do
	for Q in cl do
		
		for phi in Filtered(maps, f -> Image(f) = Q) do
			N_phi := ExtenderSubgroup(phi, maps);
			extensions := Filtered(maps, g -> Source(g) = N_phi);
			P := Source(phi);
			for phi_tilde in extensions do
				extAxiom := true;
				for a in GeneratorsOfGroup(P) do
					if a^phi <> a^phi_tilde then
						extAxiom := false;
						break;
					fi;
				od;
				if extAxiom then break; fi;
					
			od;
			if extAxiom = false then break; fi;
		od;
		if extAxiom = false then break; fi;
		
	od;
	if extAxiom = false then break; fi;
od;
fi;

return sylowAxiom and extAxiom; 
end;;


IsFusionSystem := function (fs)

local maps, S, isFS, i, fsSS, phi, f, g, inverseExists, outers, P, subgroups;

if IsMapping(fs[1]) then
	maps := fs;
else
	maps := fs[1];
fi;

isFS := true;
SortBy(maps, x -> -Size(Source(x)));
S:= Source(maps[1]);
fsSS := FusionSystem(S,S);
for phi in fsSS do
	if not (phi in maps) then
		isFS := false;
		break;
	fi;
od;

if isFS then
	for f in maps do
		inverseExists := false;
		for g in maps do
			if Image(f) = Source(g) then
				if not (f * g in maps) then
				isFS := false;
				fi;
				if f * g = IdentityMapping(Source(f)) then
					inverseExists := true;
				fi;
			fi;
				
				if isFS = false then break; fi;
		od;
		isFS := isFS and inverseExists;
		if isFS = false then break; fi;
	od;
fi;

outers := Difference(maps, fsSS);

if (not IsEmpty(outers)) and isFS then 
	subgroups := ConjugacyClassesSubgroups(S);
	
	for f in outers do
		
		for P in subgroups do
			P := Representative(P);
			if Size(P) > Size(Source(f)) or P = Source(f) then
				break; 
			fi;
			isFS := false;
			for g in Filtered(maps, x -> Source(x) = P) do
				if Image(f, GeneratorsOfGroup(P)) = Image(g, GeneratorsOfGroup(P)) then
					isFS := true;
				fi;
					
			od;
			if isFS = false then break; fi;
		od;
		if isFS = false then break; fi;	
	od;
fi;

return isFS and inverseExists;
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

#Finds all fusion systems on P upto isomorphism.
AllFusionSystems := function (P, upperBound) 

local sizeP, fsPP, fusionSystems, groupSize, G, fsPG, newFS, fs;

StructureDescription(P);
sizeP := Size(P);
fsPP := FusionSystem(P,P);
fusionSystems := [[[P, P], IdGroup(P), fsPP]];

if upperBound < sizeP then return false; fi;

for groupSize in [2 * sizeP..upperBound] do
	#if groupSize <> upperBound then continue; fi;
	if groupSize mod sizeP <> 0 then continue; fi;
	
	for G in AllSmallGroups(groupSize) do
		if not (IsEmpty(IsomorphicSubgroups(G, P:findall:=false))) then
			fsPG := FusionSystem(P, G);
			newFS := true;
			
			for fs in fusionSystems do
				if AreIsomFS(fs[3], fsPG) then 
					newFS := false; 
					break; 
				fi;
			od;
			
			if newFS then 
				StructureDescription(G); 
				Append(fusionSystems, [[[P, G], IdGroup(G), fsPG]]);  
			fi;
		fi;
	od;
od;
return fusionSystems;
end;;


#Does a similar work with AllFusionSystems, however, it lists every fusion system on P. 
#Different fusion systems are encoded with id numbers.
AllFS := function (P, upperBound) 

local sizeP, fsPP, fusionSystems, groupSize, G, fsPGAll, fsPG, newFS, fs, id, PinG;

sizeP := Size(P);
fsPP := FusionSystem(P,P);
id := 1;
fusionSystems := [[id, fsPP, [P]]];

if upperBound < sizeP then return fail; fi;

for groupSize in [2 * sizeP..upperBound] do
	#if groupSize <> upperBound then continue; fi;
	if groupSize mod sizeP <> 0 then continue; fi;
	
	for G in AllSmallGroups(groupSize) do
		
		if not (IsEmpty(IsomorphicSubgroups(G, P:findall:=false))) then
			fsPGAll := FusionSystem(P, G);
			for fsPG in fsPGAll do
			newFS := true;
			PinG := Source(fsPG[1]);
			#if  IsNormal(G, Intersection(PinG, Centralizer(G, PinG))) and not (IsSubgroup(PinG, Centralizer(G, PinG))) then continue; fi;
        	#if not (IsSubgroup(PinG, Centralizer(G, PinG))) then continue; fi;
				for fs in fusionSystems do
				
					if AreIsomFS(fs[2], fsPG) then 
						newFS := false;
						if fs[1] > 1 then
							Append(fs[3], [G]);
						fi;
					fi;
				od;
				if newFS then 
					id := id + 1;
					Append(fusionSystems, [[id, fsPG, [G]]]);  
				fi;
			od;
		fi;
	od;
od;


return fusionSystems;
end;;





AllSaturatedFS := function (P, upperBound) 

local sizeP, fsPP, fusionSystems, groupSize, G, reps, R, PtoG, fsRG, newFS, fs, index, indexFS;

StructureDescription(P);
sizeP := Size(P);
fsPP := FusionSystem(P,P);
fusionSystems := [[[P, P], IdGroup(P), fsPP]];
if upperBound < sizeP then return false; fi;

for groupSize in [2 * sizeP..upperBound] do
	
	if groupSize mod sizeP <> 0 then continue; fi;
	
	for G in AllSmallGroups(groupSize) do
		reps := Filtered(List(ConjugacyClassesSubgroups(G), Representative), i -> Size(i) = Size(P));
		reps := Filtered(reps, i -> IdGroup(i) = IdGroup(P));

		if not (IsEmpty(reps)) then
			for R in reps do
			fsRG := FusionSystem(R, G);
			newFS := true;
				for indexFS in [1..Size(fusionSystems)] do
			
					if AreIsomFS(fusionSystems[indexFS][3], fsRG) then 
						newFS := false; 
						break; 
					fi;
				
					if indexFS = Size(fusionSystems) then

						if newFS and IsSaturatedFS(fsRG) then
							StructureDescription(G);
							Append(fusionSystems, [[[P, G], IdGroup(G), fsRG]]);
						fi;
					fi;
				od;
			od;
		fi;	
	od;	
od;

return fusionSystems;
end;;

IsomFSCouples := function (L)

local i, j, fs;

for i in [1..Size(L)] do

	for j in [i+1..Size(L)] do
		
		if AreIsomFS(L[i][1], L[j][1]) then
		
			Print("F(", StructureDescription(Source(L[i][1][1])),", ", StructureDescription(L[i][2]), ") and F(", StructureDescription(Source(L[j][1][1])), ", ", StructureDescription(L[j][2]), ") are isomorphic. \n\n");
		
		fi;
		
	od;
od;

end;;

PrintFS := function (fs) 
	local maps, f;
	if IsMapping(fs[1]) then
		maps := fs;
	else
		maps := fs[1];
	fi;

	for f in maps do
		#Print(StructureDescription(Source(f)), " -> ", StructureDescription(Image(f)), " given by ", f, "\n");
		Print(StructureDescription(Source(f)), " -> ", StructureDescription(Image(f)), " given by ");
		ViewObj(f);
		Print("\n");
	od;
end;;

SearchFS := function(low, high, upperBound)
	local index, S, indexS;

	for index in [low..high] do
		indexS := 0;
		for S in AllSmallGroups(index) do
			indexS := indexS + 1;
			#if IsPGroup(S) then continue; fi;
			if not (IsElementaryAbelian(S)) then continue; fi;
			Print("The fusion systems on the group ", StructureDescription(S), ": \n");
			ViewObj(AllFusionSystems(S, indexS, upperBound));
			Print("\n\n");
		od;
	od;
end;;




AllFusionSystemsIsomTo := function (fs, upperBound) 

	local maps, sizeP, fsPP, fusionSystems, fsPG, groupSize, G, newFS, index;

	if IsMapping(fs[1]) then
		maps := fs;
	else
		maps := fs[1];
	fi;

	for groupSize in [Size(Source(maps[1]))..upperBound] do

		index := 0;
		for G in AllSmallGroups(groupSize) do
			index := index + 1;
			if not (IsEmpty(IsomorphicSubgroups(G, Source(maps[1])))) then
				fsPG := FusionSystem(Source(maps[1]), G);
				
				if AreIsomFS(maps, fsPG) then 
						StructureDescription(G); 
					Append(fusionSystems, [[[Source(maps[1]), G], [groupSize, index], fsPG]]); 
					fi;
			fi;
		od;
	od;
	return fusionSystems;
end;;

MinimalGroupsGivingFusion := function(G)
	local cc, R, S, isMinimal, fsRG, fsRS, minimals, index;
	minimals := [];

	for cc in ConjugacyClassesSubgroups(G) do
		R := Representative(cc);
		if Size(R) = 1 then continue;fi;
		isMinimal := true;
		fsRG := FusionSystem(SmallGroup(IdGroup(Representative(cc))), G);
		for S in AllSubgroups(G) do
			if not (IsSubgroup(S, R)) then continue; fi;
			if S = G then continue; fi;
			fsRS := FusionSystem(R, S);
			if AreIsomFS(fsRS, fsRG) then
				#Print("F(", StructureDescription(R), ", ", StructureDescription(S), ") is isom. to ", "F(", StructureDescription(R), ", ", StructureDescription(G), ").\n");
				isMinimal := false;
				#Print("S: ", IdGroup(S)," R: ", IdGroup(R), "\n");
				if IdGroup(R) = [8,3] then
					Print("The group ", StructureDescription(S), " with id ", IdGroup(S), " does not respect the minimality of D8.\n");
				fi;
				break;
			fi;
		od;
		if (isMinimal) then Add(minimals, R); fi;
	od;
	if not(ValueOption("print") = false) then
		Print("\nMinimals in ", StructureDescription(G), ":\n");
		for index in [1..Size(minimals)] do
			if index = Size(minimals) then Print(StructureDescription(minimals[index]), ".\n"); break; fi;
			Print(StructureDescription(minimals[index]), ", ");
		od;
	fi;
	return minimals;
end;;


Minimals1 := function(G)
	local cc, R, S, isMinimal, fsRG, fsRS, minimals, index;
	minimals := [];

	for cc in ConjugacyClassesSubgroups(G) do
		R := cc[1];
		isMinimal := true;
		fsRG := FusionSystem(R, G);
		for S in AllSubgroups(G) do
			if not (IsSubgroup(S, R)) then continue; fi;
			if S = G then continue; fi;
			fsRS := FusionSystem(R, S);
			if AreIsomFS(fsRS, fsRG) then
				isMinimal := false;
				break;
			fi;
		od;
		if (isMinimal) then 
		StructureDescription(R);
		Append(minimals, [R]); 
		fi;
	od;

	return minimals;
end;;


Minimals2 := function(G)
	local cc, R, S, isMinimal, fsRG, fsRS, minimals, index;
	minimals := [];

	for cc in ConjugacyClassesSubgroups(G) do
		R := cc[1];
		isMinimal := true;
		fsRG := FusionSystem2(R, G);
		for S in AllSubgroups(G) do
			if not (IsSubgroup(S, R)) then continue; fi;
			if S = G then continue; fi;
			fsRS := FusionSystem2(R, S);
			if AreIsomFS(fsRS, fsRG) then
				isMinimal := false;
				break;
			fi;
		od;
		if (isMinimal) then 
		StructureDescription(R);
		Append(minimals, [R]); 
		fi;
	od;

	return minimals;
end;;


SearchMinimals := function(low, up)
	local index, G;
	if low > up then return fail; fi;

	for index in [low..up] do
		if index = 32 then continue; fi;
		for G in AllSmallGroups(index) do
			if IsAbelian(G) then continue; fi;
			MinimalGroupsGivingFusion(G);
		od;
	od;
end;;



SearchIncompatibleMinimals := function (low, up)

	local index, G, m1, m2, minimals, incompatible, indexM, myId;

	if low > up then return fail; fi;
	minimals := [];
	#myId := [4,5,8,9,10,11,12,13,14,23,24,25,30,90,91,92,93,94];

	for index in [low..up] do
		#if index = 32 then continue; fi;
		for G in AllSmallGroups(index) do
			if IsAbelian(G) then continue; fi;
			#if IsPGroup(G) and (Size(G) mod 2 = 0) then continue; fi;
			#if  (IdGroup(G)[2] in myId) then continue; fi;
			if IsPGroup(G) then continue; fi;
			m1 := Minimals1(G);
			m2 := Minimals2(G);
			
			if Size(m1) = Size(m2) then
				for indexM in [1..Size(m1)] do
					if not (IdGroup(m1[indexM]) = IdGroup(m2[indexM])) then 
						Append(minimals, [G]);
						break;
					fi;
				od;
			else 
				Append(minimals, [G]);
			fi;
		od;
	od;

	if IsEmpty(minimals) then return fail; fi;

	Print("Incompatible groups between ", low, " and ", up, " are \n");
	for G in minimals do
		Print(IdGroup(G)," ", StructureDescription(G));
		Print("\n");
	od;
	#return minimals;
end;;





ListMinimalGroupsWithFS := function (num)

local NNN, F, PrF, M, PrM, G, R, isMinimal, fsRG, fsRS, S, cc, i, n, idR, not_already_found_fus, aFi, aF, the_fus_index, aNewOne, NewOnes;

NNN := num;
F:=[];
PrF:=[];
M:=[];
PrM:=[];
for n in [2..NNN] do
    Print("\n The order of group = ",n,"\n The indexes that are searched: ");
    F[n]:=[];
	PrF[n]:=[];
    M[n]:=[];
	PrM[n]:=[];
    NewOnes:=[];
    for i in [1..NumberSmallGroups(n)] do
	    Print(i,", ");
        G:=SmallGroup(n,i);
        F[n][i]:=[];
		PrF[n][i]:=[];
        M[n][i]:=[];
		PrM[n][i]:=[];
        for cc in ConjugacyClassesSubgroups(G) do
            R := cc[1];
            isMinimal := true;
            fsRG := FusionSystem(R, G);
            for S in AllSubgroups(G) do
                if not (IsSubgroup(S, R)) then continue; fi;
                if S = G then continue; fi;
                fsRS := FusionSystem(R, S);
                if AreIsomFS(fsRS, fsRG) then
                    isMinimal := false;
			        break;
                fi;
            od;
            if (isMinimal) then
               idR:=IdGroup(R);
               not_already_found_fus:=true;
               for aFi in [1..Size(F[idR[1]][idR[2]])] do
                    aF:=F[idR[1]][idR[2]][aFi];
                    if  AreIsomFS(aF,fsRG) then 
                        the_fus_index:=aFi;
                        not_already_found_fus:=false;
                        break;
                    fi;
               od;
               if not_already_found_fus then 
			       Append(F[idR[1]][idR[2]], [fsRG]);
                   Append(PrF[idR[1]][idR[2]],[Size(PrF[idR[1]][idR[2]])+1]);
                   M[idR[1]][idR[2]][Size(F[idR[1]][idR[2]])]:=[[R,G]]; 
                   PrM[idR[1]][idR[2]][Size(PrF[idR[1]][idR[2]])]:=[[StructureDescription(R),StructureDescription(G)]]; 
				   Append(NewOnes,[[Size(PrF[idR[1]][idR[2]]), StructureDescription(R),[idR[1],idR[2]],StructureDescription(G),[n,i]]]);
               else 
                    Append(M[idR[1]][idR[2]][aFi], [[R,G]]);
                    Append(PrM[idR[1]][idR[2]][aFi], [[StructureDescription(R),StructureDescription(G)]]);
					Append(NewOnes,[[aFi, StructureDescription(R),[idR[1],idR[2]],StructureDescription(G),[n,i]]]);
               fi;
            fi;
        od;
    od;
	for aNewOne in NewOnes do
	  Print("\n ",aNewOne[1]);
	  if (RemInt( aNewOne[1], 10 )=1) then Print("st"); 
	  else if  (RemInt( aNewOne[1], 10 )=2) then Print("nd");
	  else Print("th"); fi; fi;
	  Print(" fus. sys. of group ", aNewOne[2]," with id ",aNewOne[3]," is minimaly realized by ",aNewOne[4]," with id ",aNewOne[5]);
	od;
od;

end;;



# Used by ListAllFS function
# Does a similar work with AllFusionSystems, however, it lists every fusion system on P. Different fusion systems are encoded with id numbers.
AllFSOnAGroup := function (P, low, high) 

	local sizeP, fsPP, fusionSystems, lowIndex, groupSize, G, fsPGAll, fsPG, newFS, fs, id, PinG;

	sizeP := Size(P);

	if high < sizeP then return fail; fi;
	if  sizeP >= low then lowIndex :=  sizeP; else lowIndex := low; fi;

	fsPP := FusionSystem(P,P);
	id := 1;
	fusionSystems := [[id, fsPP, [P]]];

	for groupSize in [lowIndex..high] do
		#if groupSize <> high then continue; fi;
		if groupSize mod sizeP <> 0 then continue; fi;
		
		for G in AllSmallGroups(groupSize) do
			
			if not (IsEmpty(IsomorphicSubgroups(G, P:findall:=false))) then
				fsPGAll := FusionSystem(P, G);
				
				for fsPG in fsPGAll do
				newFS := true;
				PinG := Source(fsPG[1]);
				#if  IsNormal(G, Intersection(PinG, Centralizer(G, PinG))) and not (IsSubgroup(PinG, Centralizer(G, PinG))) then continue; fi;
				#if not (IsSubgroup(PinG, Centralizer(G, PinG))) then continue; fi;
					for fs in fusionSystems do
					
						if AreIsomFS(fs[2], fsPG) then 
							newFS := false;
							if fs[1] > 1 then
								Append(fs[3], [G]);
							fi;
						fi;
					od;
					if newFS then 
						id := id + 1;
						Append(fusionSystems, [[id, fsPG, [G]]]);  
					fi;
				od;
			fi;
		od;
	od;

	return fusionSystems;
end;;







ListAllMins:= function (upperBound)
 
 local fusionSystems, PrF, minimals, pairs, G, R, isMinimal, fsRG, fsRS, S, cc, i, j, pair, n, idR, newFS, aFi, aF, indexfsR, fsR;
 
 fusionSystems := [];
 PrF := [];
 minimals := [];
 pairs := [];
 for n in [2..upperBound] do
     fusionSystems[n]:=[];
       PrF[n] := [];
     minimals[n] := [];
       pairs[n] := [];
     for i in [1..NumberSmallGroups(n)] do
         G:=SmallGroup(n, i);
         fusionSystems[n][i]:=[];
               PrF[n][i]:=[];
         minimals[n][i]:=[];
               pairs[n][i]:=[];
         for cc in ConjugacyClassesSubgroups(G) do
             R := cc[1];
             isMinimal := true;
             fsRG := FusionSystem(R, G);
             
			 if  IsNormal(G, Intersection(R, Centralizer(G, R))) and not (IsSubgroup(R, Centralizer(G,R))) then continue; fi;
             #if not (IsSubgroup(R, Centralizer(G, R))) then continue; fi;
			 for S in AllSubgroups(G) do
                 if not (IsSubgroup(S, R)) then continue; fi;
                 if S = G then continue; fi;
                 fsRS := FusionSystem(R, S);
                 if AreIsomFS(fsRS, fsRG) then
                	isMinimal := false;
                    break;
                 fi;
             od;
             if (isMinimal) then
                idR:=IdGroup(R);
                newFS := true;
                for indexfsR in  [1..Size(fusionSystems[ idR[1], idR[2] ])] do
                     fsR := fusionSystems[ idR[1], idR[2] ][indexfsR][1];
                     if  AreIsomFS(fsR, fsRG) then
                         #Append(minimals[idR[1]][idR[2]][Position(fusionSystems[idR[1], idR[2]]], [[R,G]]);
                         Append(pairs[ idR[1], idR[2] ][indexfsR], [[R, G]]);
                         Add(fusionSystems[ idR[1], idR[2] ][indexfsR], fsRG);
                         newFS := false;
                         break;
                     fi;
                od;
                if newFS then 
                    Add(fusionSystems[idR[1], idR[2]], [fsRG]);
                    #Append(PrF[idR[1]][idR[2]],[Size(PrF[idR[1]][idR[2]])+1]);
                    #minimals[idR[1]][idR[2]][Size(fusionSystems[idR[1]][idR[2]])]:=[[R,G]]; 
                    Add(pairs[ idR[1], idR[2] ], [[R, G]]); 
                fi;
             fi;
         od;
     od;
 od;
 
 for n in [2..Size(pairs)] do
    if n > Size(pairs) / 2 then break; fi;
     for i in [1..NumberSmallGroups(n)] do 
         if not (IsEmpty(pairs[n][i])) then
             Print("The group ", StructureDescription(SmallGroup(n, i)) ," with id = [",n,",",i,"] admits the following fusion systems: \n ");
         fi;
         for j in [1..Size(pairs[n][i])] do
             Print(" \ \ \ ",j);
             if j = 1 then Print("st"); elif j = 2 then Print("nd"); else Print("st"); fi;
             Print(" fusion is realized\n ");
             for pair in pairs[n][i][j] do
                 Print("\ \ \ \ \ \ \ \ \ by the group ", StructureDescription(pair[2]), " with id = ", IdGroup(pair[2]) ,"\n");
             od;
         od;
     od;
 od;
 
return fusionSystems;
end;;




Focal := function(S, G)

local ccG, reps, fg, focalGroup, SinG, GG;

focalGroup := [];
ccG := ConjugacyClassesSubgroups(G);
if not IsSubgroup(G, S) then
	reps := Filtered(List(ccG, Representative), i -> Size(i) = Size(S));
	reps := Filtered(reps, i -> IdGroup(i) = IdGroup(S));
	
	for SinG in reps do
		fg := Focal(SinG, G);
		Append(focalGroup, fg);
	od;
	return focalGroup;
else
	SinG := S;
fi;

GG:= CommutatorSubgroup(G,G);

focalGroup := Intersection(Elements(S), Elements(GG));
focalGroup := Group(focalGroup);
StructureDescription(focalGroup);
return [focalGroup];

end;;

CommutatorAutP := function(AutP, P)

	local phi, p, commutator;

	commutator := [];

	for phi in Elements(AutP) do
		for p in Elements(P) do
			Add(commutator, p^-1 * p^phi);
		od;
	od;

	return commutator;
end;;

FFocal := function (FS)

local fs, S, essentials, generators, focal, eClass, E, focalGroup;

if IsMapping(FS[1]) then
	fs := FS;
else
	fs := FS[1];
fi;

S := Source(fs[1]);

essentials := FEssentialSubgroups(fs);
Add(essentials, [S]);
generators := GeneratorsOfGroup(S);

focal := [];
for eClass in essentials do
    for E in eClass do
        Append(focal, CommutatorAutP(FAutomorphismGroup(E, fs), E));
    od;
od;

focalGroup := Group(focal);
StructureDescription(focalGroup);

return focalGroup;
end;;


#Lists all the fusion systems over the groups that have order at most "maxOrder".
#The fusion systems listed are realized by the groups whose order is between "low" and "high".
#If "p = 0", "ListAllFS" lists fusion systems on all groups whose order is at most "maxOrder".
#If "p = 1", "ListAllFS" lists fusion systems on non-p-groups.
#If "p > 0" and "p is prime", then "ListAllFS" lists fusion systems on 'p'-groups.
#If "p = -1", "ListAllFS" lists fusion systems on p-groups.
#If "p < 0" and "-p is prime", then "ListAllFS" lists fusion systems on groups which are not 'p'-groups.
ListAllFS := function(maxOrder,low, high, p) 
	local allFS, index, G, allFSoverG, fs, f, pair, j;
	allFS := [];
	for index in [2..maxOrder] do
		if low > high then return fail; fi;
		if index > high / 2 then break; fi;
		for G in AllSmallGroups(index) do
			if p <> 0 then
				if p > 0 then
					if p = 1 then
						if IsPGroup(G) then continue; fi;
					else
						if not (IsPGroup(G) and Size(G) mod p = 0) then continue; fi;
					fi;
				elif p < 0 then
					if p = -1 then
						if not IsPGroup(G) then continue; fi;
					else
						if  IsPGroup(G) and Size(G) mod -p = 0 then continue; fi;
					fi;
				else 
					return fail;
				fi;
			fi;
			allFSoverG := AllFSOnAGroup(G, low, high);
			Append(allFS, [allFSoverG]);
		od;
	od;

	for fs in allFS do
		Print("The group ", StructureDescription(fs[1][3][1]), " with id = ", IdGroup(fs[1][3][1]), " admits the following fusion systems: \n ");
		for f in fs do
			Print(" \ \ \ ", f[1]);
			if f[1] = 1 then Print("st"); elif f[1] = 2 then Print("nd"); else Print("st"); fi;
			Print(" fusion is realized\n ");
			for G in f[3] do
				Print("\ \ \ \ \ \ \ \ \ by the group ", StructureDescription(G), " with id = ", IdGroup(G) ,"\n");
			od;
		od;
	od;
end;;


#Finds all groups whose order are at most "maxOrder" that contain subgroups isom. to "P" and "Q"..
#..such that the intersection of "P" and "Q" is isom. to "H". 
FindAmbientGroup := function(P, Q, H, maxOrder)
	local index, G, subP, subQ, p, q;

	for index in [16..maxOrder] do
		for G in AllSmallGroups(index) do
			subP := Filtered(AllSubgroups(G), g -> IdGroup(g) = IdGroup(P));
			subQ := Filtered(AllSubgroups(G), g -> IdGroup(g) = IdGroup(Q));
			for p in subP do
				for q in subQ do
					if IdGroup(Intersection(p, q)) = IdGroup(H) then
						Print("G is ", StructureDescription(G), " with id = ", IdGroup(G), "\n");
					fi;
				od;
			od;
		od;
	od;
end;;





MaximalGroup := function(G, more...)
	local minSize, ccG, reps,subs, R, secondCont, ccR, pairs, repsR;

	minSize := 1;
	if not IsEmpty(more) then
		minSize := more[1];
	fi;

	ccG := ConjugacyClassesSubgroups(G);
	ccG := Filtered(ccG, g -> not Size(Representative(g)) < minSize);
	reps := Filtered(List(ccG, Representative), i -> Size(AutomorphismGroup(i)) = Size(Normalizer(G,i) / Centralizer(G,i)));
	subs := [];
	for R in reps do
		ccR := ConjugacyClassesSubgroups(R);
		repsR := Filtered(List(ccR, Representative), i -> Size(AutomorphismGroup(i)) = Size(Normalizer(G,i) / Centralizer(G,i)));
		if not Size(ccR) = Size(repsR) then continue; fi;
		secondCont := false;
		for pairs in Combinations(repsR, 2) do
			if IdGroup(pairs[1]) <> IdGroup(pairs[2]) then
				continue;
			elif not IsConjugate(G, pairs[1], pairs[2]) then
				secondCont := true;
				Print("\n\nInside the if...\n\n");
				break;
			fi;

		od;
		if secondCont then continue; fi;
		Add(subs, R);
	od;
	List(subs, StructureDescription);
	return subs;
end;;


OuterAutomorphismGroup := function(G)
	local innG, autG, outG;

	autG := AutomorphismGroup(G);
	innG := InnerAutomorphismsAutomorphismGroup(autG);
	outG := autG / innG;
	StructureDescription(outG);
	return outG;
end;;


MinimalUniversalRealizer := function (S)
	local sizeS, found, i, parentSize, G, cc, US, P, fsPG;

	parentSize := Size(OuterAutomorphismGroup(S)) * Size(S);
	Print("Parent Size: ", parentSize, "\n");
	i := 0;
	found := false;
	US := UniversalFusionSystem(S);
	Print("Size US: ", Size(US),"\n");
	while not found do
		
		i := i + 1;
		parentSize := parentSize * i;
		Print("Parent Size: ", parentSize, "\n");
		for G in AllSmallGroups(parentSize) do
			cc := Filtered(List(ConjugacyClassesSubgroups(G), Representative), r -> IdGroup(S) = IdGroup(r));
			#Print(cc, "\n");
			if IsEmpty(cc) then continue; fi;
			
			for P in cc do
				fsPG := FusionSystem(P, G);
				Print("Size fsPG: ", Size(fsPG[1]),"\n");
				if Size(US) = Size(fsPG[1]) then
					Print(StructureDescription(G), " with id = ", IdGroup(G),"\n");
					return G;
				fi;

				
			od;

		od;

	od;
	return fail;
end;;



ListUniversalPairs := function(low, up, more...)
	local maximals, index, subsIndex, G, subs, maxs, i, j, maxPair,flag, P;
	
	if low > up then return fail; fi;
	
	maximals := [];

	if not IsEmpty(more) then
		flag := true;
		P := more[1];
	else
		flag := false;
	fi;

	for index in [1..(up - low + 1)] do
		
		maximals[index] := [];
		for G in AllSmallGroups(index + low - 1) do
			if flag then
				if IsEmpty(IsomorphicSubgroups(G,P:findall:=false)) then continue; fi;
			fi;
			maximals[index, IdGroup(G)[2]] := []; 
			subs := MaximalGroup(G, low);
			
			for subsIndex in [1..Size(subs)] do
				if subsIndex = Size(subs) then 
					Add(maximals[IdGroup(subs[subsIndex])[1]  - low + 1, IdGroup(subs[subsIndex])[2]], [subs[subsIndex], G]); 
					continue;
				fi;
				if IdGroup( subs[subsIndex] ) <> IdGroup( subs[subsIndex + 1] ) then
					Add(maximals[IdGroup(subs[subsIndex])[1]  - low + 1, IdGroup(subs[subsIndex])[2]], [subs[subsIndex], G]);
				fi;
			od;
		od;
	od;

	if not(ValueOption("print") = false) then
		
		if IsEmpty(Flat(maximals)) then Print("none\n"); fi;
		
		for i in [1..Size(maximals)] do
			for j in [1..Size(maximals[i])] do
				if IsEmpty(maximals[i, j]) then continue; fi;
				Print("The universal FS over the group ", StructureDescription(SmallGroup(i + low - 1, j)), " with ID = ", IdGroup(SmallGroup(i + low - 1, j)), " might be realzied\n\n" );
				for maxPair in maximals[i, j] do 
					Print("\ \ \ \ \ \ \ by \ ", StructureDescription(maxPair[2]), " with ID = ", IdGroup(maxPair[2]), "\n");
				od;
				Print("\n");
			od;
		od;
	fi;

	return maximals;
end;;



CheckUniversalPairs := function(low, up)
	local maximals, incompatiblePairs, firstPrint, i, j, S, universalS, maxPair, pair, sizeUS;

	maximals := ListUniversalPairs(low, up:print:=false);
	incompatiblePairs := [];
	firstPrint := true;
	for i in [1..Size(maximals)] do
		if i > 32 then
			Print("\nRunning over the index ", i, "\n");
		else
			if firstPrint then
				firstPrint := false;
				Print("\nRunning over the indices between ", low, " and 32.\n");
			fi;
		fi;
		for j in [1..Size(maximals[i])] do
			if IsEmpty(maximals[i, j]) then continue; fi;
			S := SmallGroup(i + low - 1, j);
			sizeUS := Size(UniversalFusionSystem(S));
			for maxPair in maximals[i, j] do
				if not sizeUS = Size(FusionSystem(maxPair[1], maxPair[2])[1]) then
					Add(incompatiblePairs, maxPair);
					#Print("\ \ \ \ ", StructureDescription(maxPair[1]), " and ", StructureDescription(maxPair[2]), "\n");
				fi;
			od;
		od;
	od;

	if IsEmpty(incompatiblePairs) then
		Print("There is no incompability.\n");
	else
		Print("Incompatibles: \n");
		for pair in incompatiblePairs do
			Print("\ \ \ \ ", StructureDescription(pair[1]), " and ", StructureDescription(pair[2]), "\n");
		od;

		return incompatiblePairs; 
	fi;

end;;


#######
#######
#######












D := SmallGroup(8,3);;
D16 := SmallGroup(16, 7);;
DxD := DirectProduct(D,D);;
gensD := GeneratorsOfGroup(D);;
V1 := Subgroup(D,[D.1, D.3]);;
V2 := Subgroup(D, [D.2,D.3]);;
C4 := Subgroup(D, [D.1*D.2*D.3]);;
Q1 := Subgroup(D, [D.1]);;
Q2 := Subgroup(D, [D.1*D.3]);;
Q3 := Subgroup(D, [D.3]);;
Q4 := Subgroup(D, [D.2]);;
Q5 := Subgroup(D, [D.2*D.3]);;
autD := AutomorphismGroup(D);;
innD := InnerAutomorphismsAutomorphismGroup(autD);;
autV1 := AutomorphismGroup(V1);;
autV2 := AutomorphismGroup(V2);;

V4 := SmallGroup(4, 2);;
Q8 := SmallGroup(8, 4);;
S3 := SymmetricGroup(3);;
S4 := SymmetricGroup(4);;
S5 := SymmetricGroup(5);;
A4 := AlternatingGroup(4);;
A5 := AlternatingGroup(5);;
A6 := AlternatingGroup(6);;
GL32 := GL(3,2);;
CCC2 := SmallGroup(8, 5);;
ES2 := ExtraspecialGroup(8, "+");;
ES3 := ExtraspecialGroup(27, "+");;
ES5 := ExtraspecialGroup(125, "+");;
ES7 := ExtraspecialGroup(343, "+");;
autES3 := AutomorphismGroup(ES3);;
innES3 := InnerAutomorphismsAutomorphismGroup(autES3);;


fsDD := FusionSystem(D, D);;
fsDD16 := FusionSystem(D, D16);;
fsDS4 := FusionSystem(D, S4);;
fsDA6 := FusionSystem(D, A6);;
