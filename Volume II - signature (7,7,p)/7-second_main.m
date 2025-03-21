/*
	Proof of our second main theorem using the Frey elliptic curve F/K (and its twists) and C.
*/

load "7-fieldK.m";
load "7-curveF.m";
load "7-curveC.m";




print "";
print "************";
print "* PART (1) *";
print "************";
print "";


print "";
print "*******************************";
print "* Eliminating the case ab odd *";
print "*******************************";
print "";

N10:=I2;
print "Computing forms at level Q2...";
forms10:=Eigenforms(NewSubspace(HilbertCuspForms(K,N10)));
print "Done!";
print "There are ", #forms10, "newform.";
print "The case ab odd and 7 does not divide a + b is (trivially!) eliminated!";
print "++++++++++++++++++++++", Realhours();
print "";



N11:=I2*I7;
print "Computing forms at level Q2*Q7...";
forms11:=Eigenforms(NewSubspace(HilbertCuspForms(K,N11)));
print "Done!";
print "There are ", #forms11, "newforms";
print "++++++++++++++++++++++", Realhours();

print "We perform standard elimination at level Q2*Q7 using primes q = 13, 29, and 41 and the Frey curve F (not twisted):";
BoundF(forms11,1,[13,29,41]);

print "";
print "The case ab odd and 7 divides a + b is eliminated!";
print "";

print "";
print "**********************************";
print "* The case ab odd is eliminated! *";
print "**********************************";
print "";


print "";
print "****************************************";
print "* Eliminating the case 7 divides a + b *";
print "****************************************";
print "";


print "";
print "We already know that ab is even";
print "";


N31:=I2^3*I7;
print "Computing forms at level Q2^3*Q7...";
forms31:=Eigenforms(NewSubspace(HilbertCuspForms(K,N31)));
print "Done!";
print "There are ", #forms31, "newforms";
print "++++++++++++++++++++++", Realhours();


print "We perform standard elimination at level Q2^3*Q7 using primes q = 13, 29, and 41 and the Frey curve F twisted by omega_2:";
BoundF(forms31,z^2 - 2,[13,29,41]);
print "";
print "All forms are eliminated! Hence the case 2 divides ab exactly once is discarded.";

print "";
print "We perform standard elimination at level Q2^3*Q7 using primes q = 13, 29, and 41 and the Frey curve F (not twisted):";
BoundF(forms31,1,[13,29,41]);

print "";
print "The prime p = 13 survives for the form no 11; we discard it using refined elimination with q = 5:";
RefinedBoundF(forms31[11],1,[5],{13});
print "++++++++++++++++++++++", Realhours();
print "";
print "All forms are eliminated! Hence the case 4 divides ab is discarded as well.";


print "";
print "*******************************************";
print "* The case 7 divides a + b is eliminated! *";
print "* We are done with Part (1)!              *";
print "*******************************************";
print "";




print "";
print "************";
print "* PART (2) *";
print "************";
print "";




// Compute newforms at level Q2^2*Q7^2.
N22:=I2^2*I7^2;
print "Computing forms at level Q2^2*Q7^2...";
forms22:=Eigenforms(NewSubspace(HilbertCuspForms(K,N22)));
print "Done !";
print "There are", #forms22, "newforms at level Q2^2*Q7^2.";
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();
print "";



// we test which forms have coefficient field containing K
print "Eliminating forms by checking whether K is included in the field of coefficients...";
degForms22:=[];
index:=[];
for i in [1..#forms22] do
	f:=forms22[i];
	F:=BaseField(f);
	degF:=Degree(F);
	bolF:=false;
	if degF mod 3 eq 0 then 
		subsDeg3:=Subfields(F,3);
		for fld in subsDeg3 do
			if IsIsomorphic(K,fld[1]) then bolF:=true; end if;
		end for;
	end if;
	if bolF then 
		Append(~index,i); 
		Append(~degForms22,degF);
	end if;
end for;
"Done!";






assert index eq [4,5,6,8];


print "";
print "The forms at level Q2^2*Q7^2 whose coefficient field contains K are the forms labelled:";
print "[4,5,6,8]";
print "";

print "";
print "The degrees of the coefficient fields of these forms are:";
degForms22;
print "";





print "";
print "Eliminating form 4";
f:=forms22[4];
Kf:=BaseField(f);
_,toKf:=IsSubfield(K,Kf);
B3:=BoundFormC([3*OK],f,Kf,{},toKf);
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();


print "";
print "Eliminating form 6";
f:=forms22[6];
Kf:=BaseField(f);
_,toKf:=IsSubfield(K,Kf);
B3:=BoundFormC([3*OK],f,Kf,{},toKf);
B13a:=BoundFormC([I13a],f,Kf,B3,toKf);
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();


print "";
print "Eliminating form 8";
f:=forms22[8];
Kf:=BaseField(f);
_,toKf:=IsSubfield(K,Kf);
B3:=BoundFormC([3*OK],f,Kf,{},toKf);
B13a:=BoundFormC([I13a],f,Kf,B3,toKf);
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();

print "";
print "We have eliminated all forms except form no 5.";
print "By modularity we know that the remaining form no 5 corresponds to J(0,1).";
print "As a sanity check, we show that their coefficients coincide for primes above q = 3, 5, 13, 29.";
print "";

AuxPrimes:=[3,5,13,29];
f:=forms22[5];
C:=FreyC(0,1);
for q in AuxPrimes do
	Factq:=Factorisation(q*OK);
	Tq:=TraceFrobenius(C,Factq[1,1]);
	for i in {1..#Factq} do
		Q:=Factq[i,1];
		assert HeckeEigenvalue(f,Q) in Tq;
	end for;
end for;
print "";
print "Done !";
print "";




print "";
print "************************************************************";
print "* The second main theorem is proved using curves F and C ! *";
print "************************************************************";
print "";

