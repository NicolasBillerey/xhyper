/*
	Second proof of our main theorem using C in the case ab even and (twists of) F in the case ab odd, 
	but *without* taking into account the improvements explained at the end of the paper.
*/


load "fieldK.m";
load "curveF.m";
load "curveCslow.m";


print "";
print "*****************************************************************";
print "* We eliminate in turn each of the following cases:             *";
print "* (1) ab odd and 7 does not divide a + b using F twisted by -7; *";
print "* (2) ab odd and 7 divides a + b using F;                       *";
print "* (3) ab even using C.                                          *";
print "*****************************************************************";
print "";



print "";
print "****************************************************";
print "* (1) We use F twisted by -7 to eliminate the case *"; 
print "* ab odd and 7 does not divide a + b               *";
print "****************************************************";
print "";

print "";
print "Assume for a contradiction that ab is odd and 7 does not divide a + b.";
print "The mod p representation of F(a,b) twisted by -7 arises in level Q2*Q3";
print "";


N110:=I2*I3;
print "Computing forms at level Q2*Q3...";
forms110:=Eigenforms(NewSubspace(HilbertCuspForms(K,N110)));
print "Done!";
print "There are", #forms110, "newforms";
print "++++++++++++++++++++++", Realhours();

print "";
print "We perform standard elimination at level Q2*Q3 using primes q = 5, 13, and 29 and the Frey curve F twisted by -7:";
BoundF(forms110,-7,[5,13,29]);
print "++++++++++++++++++++++", Realhours();


print "";
print "******************************************";
print "* We have eliminated all the forms.      *";
print "* Therefore, we have ruled out case (1). *";
print "******************************************";
print "";




print "";
print "****************************************************";
print "* (2) We use F (not twisted) to eliminate the case *"; 
print "* ab odd and 7 divides a + b                       *";
print "****************************************************";
print "";

print "";
print "Assume for a contradiction that ab is odd and 7 divides a + b.";
print "The mod p representation of F(a,b) arises in level Q2*Q3*Q7";
print "";

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
print "******************************************";
print "* We have eliminated all the forms.      *";
print "* Therefore, we have ruled out case (2). *";
print "******************************************";
print "";



print "";
print "**********************************************";
print "* (3) We use C to eliminate the case ab even *"; 
print "**********************************************";
print "";

print "";
print "Assume for a contradiction that ab is even.";
print "The mod p representation of J(a,b) arises in level Q2^2*Q3*Q7^2.";
print "";




// Compute newforms at level I2^2*I3*I7^2.
N212:=I2^2*I3*I7^2;
print "Computing forms at level Q2^2*Q3*Q7^2...";
forms212:=Eigenforms(NewSubspace(HilbertCuspForms(K,N212)));
print "Done !";
print "There are", #forms212, "newforms at level Q2^2*Q3*Q7^2.";
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();
print "";



// we test which forms have coefficient field containing K
print "Eliminating forms by checking whether K is included in the field of coefficients...";
degForms212:=[];
index:=[];
for i in [1..#forms212] do
	f:=forms212[i];
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
		Append(~degForms212,degF);
	end if;
end for;
"Done!";



assert index eq [ 12, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 28, 33, 38, 41, 42, 45, 46, 47, 48, 51, 57, 58, 60, 61 ];
print "";

print "";
print "The forms at level Q2^2*Q3*Q7^2 whose coefficient field contains K are the forms labelled:";
print "[ 12, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 28, 33, 38, 41, 42, 45, 46, 47, 48, 51, 57, 58, 60, 61 ]";
print "";

print "";
print "The degrees of the coefficient fields of these forms are:";
degForms212;
print "";

print "";
print "Eliminating form 38";
f:=forms212[16];
Kf:=BaseField(f);
_,toKf:=IsSubfield(K,Kf);
B5:=BoundFormC([5*OK],f,Kf,{},toKf);
B5:={x : x in B5 | x notin {1,2,3,7}};
B13a:=BoundFormC([I13a],f,Kf,{},toKf);
B11:=BoundFormC([11*OK],f,Kf,B13a,toKf);
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();


print "";
print "Eliminating form 16";
f:=forms212[16];
Kf:=BaseField(f);
_,toKf:=IsSubfield(K,Kf);
B13a:=BoundFormC([I13a],f,Kf,{},toKf);
B13a:={x : x in B13a | x notin {1,2,3,7}}; 
B11:=BoundFormC([11*OK],f,Kf,B13a,toKf);

print "";
print "We use refined elimination with auxiliary prime q = 29 to deal with p = 13.";
B29:=RefinedEliminationFormC([I29a,I29b,I29c],f,Kf,13,toKf);
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();


print "";
print "Eliminating form 26";
f:=forms212[26];
Kf:=BaseField(f);
_,toKf:=IsSubfield(K,Kf);
B5:=BoundFormC([5*OK],f,Kf,{},toKf);
B5:={x : x in B5 | x notin {1,2,3,7}};
B13ab:=BoundFormC([I13a,I13b],f,Kf,B5,toKf);
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();



for i in [33,41,42] do 
	print "";
	print "Eliminating form",i;
	f:=forms212[i];
	Kf:=BaseField(f);
	_,toKf:=IsSubfield(K,Kf);
	B5:=BoundFormC([5*OK],f,Kf,{},toKf);
	B5:={x : x in B5 | x notin {1,2,3,7}};
	B13a:=BoundFormC([I13a],f,Kf,B5,toKf);
  	print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();
end for;


print "";
print "Eliminating form 45";
f:=forms212[45];
Kf:=BaseField(f);
_,toKf:=IsSubfield(K,Kf);
B5:=BoundFormC([5*OK],f,Kf,{},toKf);
B5:={x : x in B5 | x notin {1,2,3,7}};
B13a:=BoundFormC([I13a],f,Kf,B5,toKf);
B11:=BoundFormC([11*OK],f,Kf,B13a,toKf);	
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();


print "";
print "Eliminating form 12";
f:=forms212[12];
Kf:=BaseField(f);
_,toKf:=IsSubfield(K,Kf);
B29a:=BoundFormC([I29a],f,Kf,{},toKf);
B29a:={x : x in B29a | x notin {1,2,3,7}};
B17:=BoundFormC([17*OK],f,Kf,B29a,toKf);
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();

print "";
print "Eliminating form 28";
f:=forms212[28];
Kf:=BaseField(f);
_,toKf:=IsSubfield(K,Kf);
B29a:=BoundFormC([I29a],f,Kf,{},toKf);
B29a:={x : x in B29a | x notin {1,2,3,7}};
B17:=BoundFormC([17*OK],f,Kf,B29a,toKf);
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();


print "";
print "Eliminating form 17";
f:=forms212[17];
Kf:=BaseField(f);
_,toKf:=IsSubfield(K,Kf);
B5:=BoundFormC([5*OK],f,Kf,{},toKf);
B5:={x : x in B5 | x notin {1,2,3,7}};
B13a:=BoundFormC([I13a],f,Kf,B5,toKf);
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();


print "";
print "Eliminating form 24";
f:=forms212[24];
Kf:=BaseField(f);
_,toKf:=IsSubfield(K,Kf);
B5:=BoundFormC([5*OK],f,Kf,{},toKf);
B5:={x : x in B5 | x notin {1,2,3,7}};
B13a:=BoundFormC([I13a],f,Kf,B5,toKf);
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();


print "";
print "Eliminating form 18";
f:=forms212[18];
Kf:=BaseField(f);
_,toKf:=IsSubfield(K,Kf);
B13a:=BoundFormC([I13a],f,Kf,{},toKf);
B13a:={x : x in B13a | x notin {1,2,3,7}};
B5:=BoundFormC([5*OK],f,Kf,B13a,toKf);
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();

print "";
print "Eliminating form 19";
f:=forms212[19];
Kf:=BaseField(f);
_,toKf:=IsSubfield(K,Kf);
B13a:=BoundFormC([I13a],f,Kf,{},toKf);
B13a:={x : x in B13a | x notin {1,2,3,7}};
B5:=BoundFormC([5*OK],f,Kf,B13a,toKf);
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();



print "";
print "Eliminating form 20";
f:=forms212[20];
Kf:=BaseField(f);
_,toKf:=IsSubfield(K,Kf);
B13a:=BoundFormC([I13a],f,Kf,{},toKf);
B13a:={x : x in B13a | x notin {1,2,3,7}};
B11:=BoundFormC([11*OK],f,Kf,B13a,toKf);
B17:=BoundFormC([17*OK],f,Kf,B11,toKf);
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();

print "";
print "Eliminating form 21";
f:=forms212[21];
Kf:=BaseField(f);
_,toKf:=IsSubfield(K,Kf);
B13a:=BoundFormC([I13a],f,Kf,{},toKf);
B13a:={x : x in B13a | x notin {1,2,3,7}};
B11:=BoundFormC([11*OK],f,Kf,B13a,toKf);
B17:=BoundFormC([17*OK],f,Kf,B11,toKf);
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();


print "";
print "Eliminating form 22";
f:=forms212[22];
Kf:=BaseField(f);
_,toKf:=IsSubfield(K,Kf);
B13a:=BoundFormC([I13a],f,Kf,{},toKf);
B13a:={x : x in B13a | x notin {1,2,3,7}};
B11:=BoundFormC([11*OK],f,Kf,B13a,toKf);
B17:=BoundFormC([17*OK],f,Kf,B11,toKf);
print "We use refined elimination with auxiliary prime q = 29 to deal with p = 13:";
_:=RefinedEliminationFormC([I29a,I29b],f,Kf,13,toKf);
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();

print "";
print "Eliminating form 23";
f:=forms212[23];
Kf:=BaseField(f);
_,toKf:=IsSubfield(K,Kf);
B13a:=BoundFormC([I13a],f,Kf,{},toKf);
B13a:={x : x in B13a | x notin {1,2,3,7}};
B11:=BoundFormC([11*OK],f,Kf,B13a,toKf);
B17:=BoundFormC([17*OK],f,Kf,B11,toKf);
print "We use refined elimination with auxiliary prime q = 29 to deal with p = 13:";
_:=RefinedEliminationFormC([I29a,I29b],f,Kf,13,toKf);
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();



print "";
print "Eliminating form 46";
f:=forms212[46];
Kf:=BaseField(f);
_,toKf:=IsSubfield(K,Kf);
B5:=BoundFormC([5*OK],f,Kf,{},toKf);
B5:={x : x in B5 | x notin {1,2,3,7}};
B13a:=BoundFormC([I13a],f,Kf,B5,toKf);
B11:=BoundFormC([11*OK],f,Kf,B13a,toKf);
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();

print "";
print "Eliminating form 47";
f:=forms212[47];
Kf:=BaseField(f);
_,toKf:=IsSubfield(K,Kf);
B5:=BoundFormC([5*OK],f,Kf,{},toKf);
B5:={x : x in B5 | x notin {1,2,3,7}};
B13a:=BoundFormC([I13a],f,Kf,B5,toKf);
B11:=BoundFormC([11*OK],f,Kf,B13a,toKf);
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();


print "";
print "Eliminating form 48";
f:=forms212[48];
Kf:=BaseField(f);
_,toKf:=IsSubfield(K,Kf);
B5:=BoundFormC([5*OK],f,Kf,{},toKf);
B5:={x : x in B5 | x notin {1,2,3,7}};
B13a:=BoundFormC([I13a],f,Kf,B5,toKf);
B11:=BoundFormC([11*OK],f,Kf,B13a,toKf);
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();


print "";
print "Eliminating form 51";
f:=forms212[51];
Kf:=BaseField(f);
_,toKf:=IsSubfield(K,Kf);
B5:=BoundFormC([5*OK],f,Kf,{},toKf);
B5:={x : x in B5 | x notin {1,2,3,7}};
B13a:=BoundFormC([I13a],f,Kf,B5,toKf);
B11:=BoundFormC([11*OK],f,Kf,B13a,toKf);
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();


print "";
print "Eliminating form 57";
f:=forms212[57];
Kf:=BaseField(f);
_,toKf:=IsSubfield(K,Kf);
B29a:=BoundFormC([I29a],f,Kf,{},toKf);
B29a:={x : x in B29a | x notin {1,2,3,7}};
B5:=BoundFormC([5*OK],f,Kf,B29a,toKf);
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();

print "";
print "Eliminating form 58";
f:=forms212[58];
Kf:=BaseField(f);
_,toKf:=IsSubfield(K,Kf);
B29a:=BoundFormC([I29a],f,Kf,{},toKf);
B29a:={x : x in B29a | x notin {1,2,3,7}};
B5:=BoundFormC([5*OK],f,Kf,B29a,toKf);
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();



print "";
print "Eliminating form 60";
f:=forms212[60];
Kf:=BaseField(f);
_,toKf:=IsSubfield(K,Kf);
B5:=BoundFormC([5*OK],f,Kf,{},toKf);
B5:={x : x in B5 | x notin {1,2,3,7}};
B11:=BoundFormC([11*OK],f,Kf,B5,toKf);
B13a:=BoundFormC([I13a],f,Kf,B11,toKf);
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();


print "";
print "Eliminating form 61";
f:=forms212[61];
Kf:=BaseField(f);
_,toKf:=IsSubfield(K,Kf);
B5:=BoundFormC([5*OK],f,Kf,{},toKf);
B5:={x : x in B5 | x notin {1,2,3,7}};
B11:=BoundFormC([11*OK],f,Kf,B5,toKf);
B13a:=BoundFormC([I13a],f,Kf,B11,toKf);

print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();

print "";
print "All forms were eliminated.";

print "";
print "********************************************************";
print "* The main theorem is proved using curves E, F and C ! *";
print "********************************************************";
print "";
