/*
	Third proof of our main theorem using E, F and C.
*/

load "7-curveE.m";
load "7-fieldK.m";
load "7-curveF.m";
load "7-curveC.m";




print "";
print "***********************************************************************";
print "* We eliminate in turn each of the following cases:                   *";
print "* (1) 4 does not divide ab and 7 does not divide a + b using E        *";
print "* (2) 4 divides ab and 7 does not divide a + b using F twisted by -7  *";
print "* (3) 2 does not divide ab and 7 divides a + b using F                *";
print "* (4) 2 divides ab and 7 divides a + b using C                        *";
print "***********************************************************************";
print "";



print "";
print "****************************************************";
print "* (1) We use E to eliminate the case               *"; 
print "* 4 does not divide ab and 7 does not divide a + b *";
print "****************************************************";
print "";



print "";
print "Assume for a contradiction that 4 does not divide ab and 7 does not divide a + b";
print "The mod p representation of E(a,b) arises in level 2^3*7^2 = 392";

formsQ392:=Newforms(CuspidalSubspace(ModularForms(392,2)));
print "There are",#formsQ392,"newforms at level 392";

BoundE(formsQ392);

print "Only form no 1 is not eliminated. Computing the difference of the a_3 coefficients, we check that it corresponds to the Frey curve E(1,-1) :";
fE:=Newform(FreyE(1,-1));
for i in [1..#formsQ392] do
	f:=formsQ392[i,1];
	print "Form f no",i,": a_3(E) - a_3(f) =",Coefficient(fE,3)-Coefficient(f,3);
end for;

print "Therefore, the mod p representations of E(a,b) and E(1,-1) are isomorphic. ";
print "This is a contradiction since by assumption 7 does not divide a + b.";

print "";
print "******************************************";
print "* We have eliminated all the forms.      *";
print "* Therefore, we have ruled out case (1). *";
print "******************************************";
print "";

print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();




print "";
print "****************************************************";
print "* (2) We use F twisted by -7 to eliminate the case *"; 
print "* 4 divides ab and 7 does not divide a + b         *";
print "****************************************************";
print "";

print "";
print "Assume for a contradiction that 4 divides ab and 7 does not divide a + b";
print "The mod p representation of F(a,b) twisted by -7 arises in level Q2^3*Q3";


N310:=I2^3*I3;
print "Computing forms at level Q2^3*Q3...";
forms310:=Eigenforms(NewSubspace(HilbertCuspForms(K,N310)));
print "Done!";
print "There are", #forms310, "newforms";
print "++++++++++++++++++++++", Realhours();

print "We first perform standard elimination at level Q2^3*Q3 using primes q = 5, 13, 29, and 41 and the Frey curve twisted by -7:";
BoundF(forms310,-7,[5,13,29,41]);
print "++++++++++++++++++++++", Realhours();



print "";
print "The prime p = 5 survives for the form no 24; we discard it using refined elimination with q = 13:";
RefinedBoundF(forms310[24],-7,[13],{5});
print "++++++++++++++++++++++", Realhours();
print "";


print "";
print "******************************************";
print "* We have eliminated all the forms.      *";
print "* Therefore, we have ruled out case (2). *";
print "******************************************";
print "";

print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();




print "";
print "********************************************";
print "* (3) We use F to eliminate the case       *"; 
print "* 2 does not divide ab and 7 divides a + b *";
print "********************************************";
print "";

print "";
print "Assume for a contradiction that 2 does not divide ab and 7 divides a + b";
print "The mod p representation of F(a,b) arises in level Q2^3*Q3";

N111:=I2*I3*I7;
print "Computing forms at level Q2*Q3*Q7...";
forms111:=Eigenforms(NewSubspace(HilbertCuspForms(K,N111)));
print "Done!";
print "There are", #forms111, "newforms";
print "++++++++++++++++++++++", Realhours();

print "We first perform standard elimination at level Q2*Q3*Q7 using primes q = 5, 13, 29, and 41 and the Frey curve not twisted:";
BoundF(forms111,1,[5,13,29,41]);
print "++++++++++++++++++++++", Realhours();




print "";
print "The primes p = 5, 13 survive for the form no 3; we discard p = 5 using refined elimination with q = 29:";
RefinedBoundF(forms111[3],1,[29],{5,13});
print "";

print "The prime p = 5 is eliminated for form no 3, but the prime p = 13 still survives.";

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
print "******************************************";
print "* We have eliminated all the forms.      *";
print "* Therefore, we have ruled out case (3). *";
print "******************************************";
print "";

print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();



print "";
print "**************************************";
print "* (4) We use C to eliminate the case *"; 
print "* 2 divides ab and 7 divides a + b   *";
print "**************************************";
print "";


print "";
print "Assume for a contradiction that 2 divides ab and 7 divides a + b";
print "The mod p representation of J(a,b) arises in level Q2^3*Q3*Q7";

N211:=I2^2*I3*I7;
print "Computing forms in level Q2^2*Q3*Q7...";
forms211:=Eigenforms(NewSubspace(HilbertCuspForms(K,N211)));
print "Done!";
print "There are",#forms211,"newforms to eliminate.";
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();
print "";




// We test which forms have coefficient field containing K
//degForms:=[];
index:=[];
for i in [1..#forms211] do
	f:=forms211[i];
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
	end if;
end for;
print "";
print "Only the forms no",index,"have coefficient field containing K";

print "";
print "We finally eliminate each of these forms in turn:";



print "";
print "Eliminating form 9";
print "";
f:=forms211[9];
Kf:=BaseField(f);
_,toKf:=IsSubfield(K,Kf);
B5:=BoundFormCTwisted([5*OK],f,Kf,{},toKf);
B13ab:=BoundFormCTwisted([I13a,I13b],f,Kf,B5,toKf);
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();




print "";
print "Eliminating form 10";
f:=forms211[10];
Kf:=BaseField(f);
_,toKf:=IsSubfield(K,Kf);

B13a:=BoundFormCTwisted([I13a],f,Kf,{},toKf);
B11:=BoundFormCTwisted([11*OK],f,Kf,B13a,toKf);

print "We use refined elimination with auxiliary prime q = 29 to deal with p = 13";

RB29:=RefinedEliminationFormCTwisted([I29a,I29b,I29c],f,Kf,13,toKf);
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();


print "";
for i in [15,17,18] do 
	print "";
	print "Eliminating form",i;
	f:=forms211[i];
	Kf:=BaseField(f);
	_,toKf:=IsSubfield(K,Kf);
	B5:=BoundFormCTwisted([5*OK],f,Kf,{},toKf);
	B13a:=BoundFormCTwisted([I13a],f,Kf,B5,toKf);
  	print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();
end for;


print "";
print "Eliminating form 19";
f:=forms211[19];
Kf:=BaseField(f);
_,toKf:=IsSubfield(K,Kf);
B5:=BoundFormCTwisted([5*OK],f,Kf,{},toKf);
B13a:=BoundFormCTwisted([I13a],f,Kf,B5,toKf);
B11:=BoundFormCTwisted([11*OK],f,Kf,B13a,toKf);

print "";
print "******************************************";
print "* We have eliminated all the forms.      *";
print "* Therefore, we have ruled out case (4). *";
print "******************************************";
print "";

print "";
print "*******************************************************";
print "* The main theorem is proved using curves E, F and C! *";
print "*******************************************************";
print "";

print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();

