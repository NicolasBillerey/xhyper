/*
	Variant of the first proof of our main theorem using the Frey elliptic curves E/Q and (twists of) F/K.
*/

load "7-curveE.m";
load "7-fieldK.m";
load "7-curveF.m";


print "";
print "**************************************************";
print "* Using the curve E, we show that either         *";
print "* (1) 7 does not divide a+b and 4 divides ab, or *";
print "* (2) 7 divides a+b and 4 does not divide ab.    *";
print "**************************************************";
print "";

print "";
print "*******************************";
print "* Let us assume 4 divides ab. *";
print "*******************************";
print "";


print "";
print "The mod p representation of E(a,b) arises in level 2^2*7^2 = 196";
print "";

forms196:=Newforms(CuspidalSubspace(ModularForms(196,2)));
print "There are",#forms196,"newforms at level 196";


BoundE(forms196);

print "Only form no 2 is not eliminated. Computing the difference of the a_3 coefficients, we check that it corresponds to the Frey curve E(1,0) :";
fE:=Newform(FreyE(1,0));
forms:=Newforms(CuspidalSubspace(ModularForms(196,2)));
for i in [1..#forms] do
	f:=forms[i,1];
	print "Form f no",i,": a_3(E) - a_3(f) =",Coefficient(fE,3)-Coefficient(f,3);
end for;
print "Therefore, the mod p representations of E(a,b) and E(1,0) are isomorphic. ";
print "In particular, 7 does not divide a+b and hence we are in Case (1).";
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();


print "";
print "***************************************";
print "* Let us assume 4 does not divide ab. *";
print "***************************************";
print "";

print "";
print "The mod p representation of E(a,b) arises in level 2^3*7^2 = 392";

forms392:=Newforms(CuspidalSubspace(ModularForms(392,2)));
print "There are",#forms392,"newforms at level 392";

BoundE(forms392);

print "Only form no 1 is not eliminated. Computing the difference of the a_3 coefficients, we check that it corresponds to the Frey curve E(1,-1) :";
fE:=Newform(FreyE(1,-1));
for i in [1..#forms392] do
	f:=forms392[i,1];
	print "Form f no",i,": a_3(E) - a_3(f) =",Coefficient(fE,3)-Coefficient(f,3);
end for;

print "Therefore, the mod p representations of E(a,b) and E(1,-1) are isomorphic. ";
print "In particular, 7 divides a+b and hence we are in Case (2).";
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();


print "";
print "**************************************************";
print "* Using the curve E, We have proved that either  *";
print "* (1) 7 does not divide a+b and 4 divides ab, or *";
print "* (2) 7 divides a+b and 4 does not divide ab.    *";
print "**************************************************";
print "";

print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();

print "";
print "**************************************************************************";
print "* We deal with the two remaining cases using the curve F and its twists. *";
print "**************************************************************************";
print "";

print "";
print "***************************************************************";
print "* Eliminating case (1): 7 not dividing a+b and 4 dividing ab. *";
print "***************************************************************";
print "";




N310:=I2^3*I3;
print "Computing forms at level Q2^3*Q3...";
forms310:=Eigenforms(NewSubspace(HilbertCuspForms(K,N310)));
print "Done!";
print "There are ", #forms310, "newforms";
print "++++++++++++++++++++++", Realhours();


print "";
print "We first perform standard elimination at level Q2^3*Q3 using primes q = 5, 13, 29, and 41 and the Frey curve twisted by -7:";
BoundF(forms310,-7,[5,13,29,41]);
print "++++++++++++++++++++++", Realhours();



print "";
print "The prime p = 5 survives for the form no 24; we discard it using refined elimination with q = 13:";
RefinedBoundF(forms310[24],-7,[13],{5});
print "++++++++++++++++++++++", Realhours();
print "";




print "";
print "***************************************************************";
print "* Eliminating case (2): 7 dividing a+b and 4 not dividing ab. *";
print "***************************************************************";
print "";


print "";
print "***********************************";
print "* Eliminating the subcase ab odd. *";
print "***********************************";
print "";

N111:=I2*I3*I7;
print "Computing forms at level Q2*Q3*Q7...";
forms111:=Eigenforms(NewSubspace(HilbertCuspForms(K,N111)));
print "Done!";
print "There are ", #forms111, "newforms";
print "++++++++++++++++++++++", Realhours();

print "We first perform standard elimination at level Q2*Q3*Q7 using primes q = 5, 13, 29, and 41 and the Frey curve not twisted:";
BoundF(forms111,1,[5,13,29,41]);
print "++++++++++++++++++++++", Realhours();




print "";
print "The primes p = 5, 13 survive for the form no 3; we discard p = 5 using refined elimination with q = 29:";
RefinedBoundF(forms111[3],1,[29],{5,13});
print "++++++++++++++++++++++", Realhours();
print "";

print "The prime p = 5 is eliminated for form no 3 (but the prime p = 13 still survives).";

print "";
print "For each form f at level Q2*Q3*Q7, we compute Norm(a_Q(f)-(Norm(Q)+1)) mod 13 for any of the three prime ideals Q above 29 in K:";
print "";
Q29:=Factorisation(29*OK)[1,1];
for i in [1..#forms111] do
	f:=forms111[i];
	print "Form no",i,": Norm(a_Q(f)-(Norm(Q)+1)) mod 13 =",Integers()!Norm(HeckeEigenvalue(f,Q29)-(Norm(Q29)+1)) mod 13;
end for;
print "";
print "Hence form no 3 is the *unique* form with reducible mod 13 representation whose existence is predicted by Martin's result.";
F:=CoefficientField(forms111[3]);
print "It has exactly",#Factorisation(13*Integers(F)),"prime ideal above 13 in its coefficient field.";
print "++++++++++++++++++++++", Realhours();
print "";





print "";
print "**********************************************************";
print "* Eliminating the subcase ab divisible by 2 exactly once *";
print "**********************************************************";
print "";


N311:=I2^3*I3*I7;
print "Computing forms at level Q2^3*Q3*Q7...";
forms311:=Eigenforms(NewSubspace(HilbertCuspForms(K,N311)));
print "Done !";
print "There are ", #forms311, "newforms";
print "++++++++++++++++++++++", Realhours();

print "We first perform standard elimination at level Q2^3*Q3*Q7 using primes q = 5, 13, 29, and 41 and the Frey curve twisted by w2:";
BoundF(forms311,z^2-2,[5,13,29,41]);
print "++++++++++++++++++++++", Realhours();


print "";
print "The prime p = 5 survives for the forms no 56 and 79; we discard it using refined elimination with q = 83 and q = 29 respectively:";
print "";
print "Dealing with form no 56:";
print "";
RefinedBoundF(forms311[56],z^2-2,[83],{5});
print "";
print "Dealing with form no 79:";
print "";
RefinedBoundF(forms311[79],z^2-2,[29],{5});
print "++++++++++++++++++++++", Realhours();
print "";





print "";
print "***********************************************************";
print "* We have proved that x^7 + y^7 = 3z^p has no non trivial *";
print "* solutions for p = 5 or p > 7 using E and F.             *";
print "***********************************************************";
print "";