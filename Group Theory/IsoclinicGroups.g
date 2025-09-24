# This file contains functions to study isoclinic groups.
# Two groups are isoclinic if their commutator structures are essentially the same.
# In other words, their quotient by the center and their commutator subgroups are isomorphic
# in a way that respects the commutator map.
#
# The function AreIsoclinic checks whether two groups are isoclinic.
# The function FindIsoclinicFamilies groups all small groups of a given order into isoclinic families.
# These families help classify groups not by full isomorphism, but by their commutator behavior.


Commutator := function(a, b)
	return a^-1 * b^-1 * a * b;
end;;

AreIsoclinic := function (P, Q)
	local homPC, homQC, PC, PCPC, QC, QCQC, comP, comQ, f, g, f_list, g_list, commute, T, centerP;

	homPC := NaturalHomomorphismByNormalSubgroup(P, Center(P));
	homQC := NaturalHomomorphismByNormalSubgroup(Q, Center(Q));

	PC := Image(homPC);
	QC := Image(homQC);
	comP := CommutatorSubgroup(P, P);
	comQ := CommutatorSubgroup(Q, Q);
	PCPC := Tuples(Elements(PC), 2);
	#QCQC := Tuples(QC, 2);

	if IsomorphismGroups(PC, QC) <> fail then
		f_list := AllIsomorphisms(PC, QC);
	else
		#Print("PC and QC are not isom.\n");
		return false;
	fi;

	if IsomorphismGroups(comP, comQ) <> fail then
		g_list := AllIsomorphisms(comP, comQ);
	else
		#Print("comP and comQ are not isom.\n");
		return false;
	fi;

	centerP := Center(P);

	for f in f_list do
		for g in g_list do
			commute := true;
			for T in PCPC do 
				if Image(g, Commutator(PreImagesRepresentative(homPC,T[1]), PreImagesRepresentative(homPC,T[2]))) <> Commutator(PreImagesRepresentative(homQC,Image(f, T[1])) , PreImagesRepresentative(homQC,Image(f, T[2]))) then
					commute := false;
					break;
				fi;
			od;
			if commute then
				return true;
			fi;
		od;
	od;

	return false;
end;;



FindIsoclinicFamilies := function (n)
	local families, i, j, newFamily, family, familySize, G;

	families := [];
	Add(families, [SmallGroup(n, 1)]);
	if IsPrime(n) then
		Print("There is only one isoclinic family of groups of order ", n, ":\n");
		Print("\ \ \ 1. ", StructureDescription(SmallGroup(n, 1)), "\n");
		return families;
	fi;

	for i in [2..NumberSmallGroups(n)] do
		G := SmallGroup(n, i);
		newFamily := true;

		for family in families do
			if AreIsoclinic(family[1], G) then
				Add(family, G);
				newFamily := false;
				break;
			fi;
		od;
		if newFamily then
			Add(families, [G]);
		fi;
	od;

	if Size(families) <> 1 then
		Print("There are ", Size(families), " isoclinic families of groups of order ", n, ":\n\n");
	else
		Print("There is only one isoclinic family of groups of order ", n, ":\n");
	fi;
	for i in [1.. Size(families)] do
		Print("\ \ \ ", i, ". ");
		familySize := Size(families[i]);
		for j in [1..familySize] do
			if j <> familySize then
				Print(StructureDescription(families[i, j]), ", ");
			else
				Print(StructureDescription(families[i, j]), ".");
			fi;
			
		od;
		Print("\n");
	od;
	Print("\n");

	return families;
end;;
