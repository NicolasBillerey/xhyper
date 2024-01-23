/*
	First proof of our main theorem using only the Frey elliptic curve F/K and its twists.
*/

load "fieldK.m";
load "curveF.m";



print "*******************************************************";
print "* PART A : Eliminating in the case 7 not dividing a+b *";
print "*******************************************************";
print "";


print "";
print "*******************************";
print "* Eliminating the case ab odd *";
print "*******************************";
print "";

N110:=I2*I3;
print "Computing forms at level Q2*Q3...";
forms110:=Eigenforms(NewSubspace(HilbertCuspForms(K,N110)));
print "Done!";
print "There are ", #forms110, "newforms";
print "++++++++++++++++++++++", Realhours();

print "We perform standard elimination at level Q2*Q3 using primes q = 5, 13, and 29 and the Frey curve twisted by -7:";
BoundF(forms110,-7,[5,13,29]);
print "++++++++++++++++++++++", Realhours();

print "";
print "***********************************";
print "* Eliminating the case ab even... *";
print "***********************************";
print "";




N310:=I2^3*I3;
print "Computing forms at level Q2^3*Q3...";
forms310:=Eigenforms(NewSubspace(HilbertCuspForms(K,N310)));
print "Done!";
print "There are ", #forms310, "newforms";
print "++++++++++++++++++++++", Realhours();




print "";
print "*******************************************";
print "* ... with ab divisible by 2 exactly once *";
print "*******************************************";
print "";

print "We first perform standard elimination at level Q2^3*Q3 using primes q = 13, 29, and 41 and the Frey curve twisted by -7*w2:";
BoundF(forms310,-7*(z^2 - 2),[13,29,41]);
print "++++++++++++++++++++++", Realhours();



print "";
print "The prime p = 5 survives for the form no 24; we discard it using refined elimination with q = 13:";
RefinedBoundF(forms310[24],-7*(z^2 - 2),[13],{5});
print "++++++++++++++++++++++", Realhours();
print "";



print "";
print "******************************";
print "* ... with ab divisible by 4 *";
print "******************************";
print "";

print "This is the same level as before but with a different twist for the Frey curve.";
print "We first perform standard elimination at level Q2^3*Q3 using primes q = 5, 13, 29, and 41 and the Frey curve twisted by -7:";
BoundF(forms310,-7,[5,13,29,41]);
print "++++++++++++++++++++++", Realhours();



print "";
print "The prime p = 5 survives for the form no 24; we discard it using refined elimination with q = 13:";
RefinedBoundF(forms310[24],-7,[13],{5});
print "++++++++++++++++++++++", Realhours();
print "";





print "***************************************************";
print "* PART B : Eliminating in the case 7 dividing a+b *";
print "***************************************************";
print "";



print "";
print "*******************************";
print "* Eliminating the case ab odd *";
print "*******************************";
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
print "***********************************";
print "* Eliminating the case ab even... *";
print "***********************************";
print "";


N311:=I2^3*I3*I7;
print "Computing forms at level Q2^3*Q3*Q7...";
forms311:=Eigenforms(NewSubspace(HilbertCuspForms(K,N311)));
print "Done !";
print "There are ", #forms311, "newforms";
print "++++++++++++++++++++++", Realhours();


print "";
print "*******************************************";
print "* ... with ab divisible by 2 exactly once *";
print "*******************************************";
print "";

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
print "******************************";
print "* ... with ab divisible by 4 *";
print "******************************";
print "";


print "This is the same level as before but with a different twist for the Frey curve.";
print "We first perform standard elimination at level Q2^3*Q3*Q7 using primes q = 5, 13, 29, and 41 and the Frey curve not twisted:";
BoundF(forms311,1,[5,13,29,41]);
print "++++++++++++++++++++++", Realhours();

print "";
print "The prime p = 5 survives for the forms no 56, 79 and 120; we discard it using refined elimination with q = 83, 41, and 29 respectively:";
print "";
print "Dealing with form no 56:";
print "";
RefinedBoundF(forms311[56],1,[83],{5});
print "";
print "Dealing with form no 79:";
print "";
RefinedBoundF(forms311[79],1,[41],{5});
//alternatively:
//RefinedBoundF(forms311[79],1,[13,29]);
print "";
print "Dealing with form no 120:";
print "";
RefinedBoundF(forms311[120],1,[29],{5});
print "++++++++++++++++++++++", Realhours();
print "";

print "";
print "***********************************************************";
print "* We have proved that x^7 + y^7 = 3z^p has no non trivial *";
print "* solutions for p = 5 or p > 7 using F only.              *";
print "***********************************************************";
print "";

