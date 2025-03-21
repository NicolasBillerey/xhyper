/*
	Second proof of our main theorem using C in the case ab even and (twists of) F in the case ab odd.
*/


//load "curveE.m";
load "7-fieldK.m";
load "7-curveF.m";
load "7-curveC.m";


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
print "We first determine which of these forms are quadratic twists by the mod 7 cyclotomic character (which is quadratic when restricted to K) of forms in the two possible smaller levels.";
print "";

N210:=I2^2*I3;
print "Computing forms at level Q2^2*Q3...";
forms210:=Eigenforms(NewSubspace(HilbertCuspForms(K,N210)));
print "Done!";
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();
print "";


print "Degrees of the coefficient fields of the forms at level Q2^2*Q3:";
degForms210:=[];
for i in [1..#forms210] do
	f:=forms210[i];
	degForms210:=Append(degForms210,Degree(CoefficientField(f)));
end for;
degForms210;
print "";


N211:=I2^2*I3*I7;
print "Computing forms in level Q2^2*Q3*Q7...";
forms211:=Eigenforms(NewSubspace(HilbertCuspForms(K,N211)));
print "Done!";
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();
print "";


print "Degrees of the coefficient fields of the forms at level Q2^2*Q3*Q7:";
degForms211:=[];
for i in [1..#forms211] do
	f:=forms211[i];
	degForms211:=Append(degForms211,Degree(CoefficientField(f)));
end for;
degForms211;
print "";



print "We already conclude that forms at level Q2^2*Q3*Q7^2 with coefficient field containing K of degree > 15 do not arise from lower level.";
print "";

print "We look for the forms in level Q2^2*Q3*Q7^2 whose coefficient field contains K and has degree <= 15 and such that they arise by quadratic twist from level Q2^2*Q3 or Q2^2*Q3*Q7.";
print "";

print "Checking for forms that arises from twisting forms at level Q2^2*Q3 by comparing the coefficient fields:";
for i in [2..#forms210] do
	fi:=forms210[i];
	Fi:=BaseField(fi);
	degi:=Degree(Fi);
	if degi ge 3 and IsSubfield(K,Fi) then
		for j in [1..17] do
			fj:=forms212[index[j]];
			Fj:=BaseField(fj);
			degj:=Degree(Fj);
			if degj eq degi then
				if IsIsomorphic(Fj,Fi) then
					print "Form no",index[j],"with field of degree",Degree(Fj),"seems to be arising by quadratic twist from form no",i,"in level Q2^2*Q3";
				end if;
			end if;
		end for;
	end if;
end for;
print "Checked all forms.";
print "Since there are no repetitions of the first form number we conclude that the Galois conjugacy classes of the previous pairs of forms are related by quadratic twist.";
print "";

print "Checking for forms f in level Q2^2*Q3*Q7^2 that arise by twisting forms at level Q2^2*Q3*Q7 by comparing the coefficient fields for forms f such that [Kf:Q]>3 and by comparing the Fourier coefficient at 11*OK for forms f such that [Kf:Q] = 3 (i.e. Kf is isomorphic to K):";
for i in [9..#forms211] do
	fi:=forms211[i];
	Fi:=BaseField(fi);
	degi:=Degree(Fi);
	if degi gt 3 and IsSubfield(K,Fi) then
		for j in [13..17] do
			fj:=forms212[index[j]];
			Fj:=BaseField(fj);
			degj:=Degree(Fj);
			if degj eq degi then
				if IsIsomorphic(Fj,Fi) then
					print "Form no",index[j],"with field of degree", Degree(Fj)," seems to be arising by quadratic twist from form no ", i ," in level Q2^2*Q3*Q7";
				end if;
			end if;
		end for;
	end if;
	if degi eq 3 and IsIsomorphic(K,Fi) then
		for j in [1..12] do
			fj:=forms212[index[j]];
			Fj:=BaseField(fj);
			degj:=Degree(Fj);
			_,FjtoFi:=IsIsomorphic(Fj,Fi);
			if (HeckeEigenvalue(fi,11*OK)*Fi!TwistCyclo(11*OK) - FjtoFi(HeckeEigenvalue(fj,11*OK))) eq Fi!0 then	
				print "Form no",index[j],"with field of degree",Degree(Fj),"seems to be arising by quadratic twist from form no",i,"in level Q2^2*Q3*Q7";
			end if;
		end for;
	end if;
end for;
print "Checked all forms.";
print "Since there are no repetitions of the first form number we conclude that the Galois conjugacy classes of the previous pairs of forms are related by quadratic twist.";
print "";

print "We conclude that at the level Q2^2*Q3*Q7^2 all the forms of degree 9, 12, 15 and two of degree 3 arise from smaller levels by quadratic twist.";
print "";
print "It remains to determine which forms in level Q2^2*Q3*Q7^2 are quadratic twists of each other by the same character:"; 
print "";
print "Forms no 46 and 47 are twists of each other as they are the only forms with coefficient field of degree 18.";
print "Forms no 60 and 61 are twists of each other as they are the only forms with coefficient field of degree 54.";
print "Forms no 48 and 51 are twists of each other as they are the only forms with coefficient field of degree 21 containing K.";
print "Forms no 57 and 58 are twists of each other as they are the only forms with coefficient field of degree 36 containing K.";

print "Next we show that the remaining 10 forms of level Q2^2*Q3*Q7^2 with Deg(Kf) = 3 appear in 5 pairs of quadratic twists:";
Deg3index:=[i : i in index | i notin [16,26] and i le 28 ];

for i, j in [1..#Deg3index] do 
	if i lt j then
		fi:=forms212[Deg3index[i]];
		Fi:=BaseField(fi);
		_,FitoK:=IsIsomorphic(Fi,K);
		fj:=forms212[Deg3index[j]];
		Fj:=BaseField(fj);
		_,FjtoK:=IsIsomorphic(Fj,K);
		if FitoK(HeckeEigenvalue(fi,11*OK)*Fi!TwistCyclo(11*OK)) - FjtoK(HeckeEigenvalue(fj,11*OK)) eq K!0 then	
			print "Form no ",Deg3index[i], " seems to be a quadratic twist of form no ", Deg3index[j];
		end if;
	end if;
end for;
print "Checked all forms.";
print "Since there are no repetitions of the first form number we conclude that the Galois conjugacy classes of the previous pairs of forms are related by quadratic twist.";
print "";



print "We first eliminate the forms that arise from a smaller level by the quadratic twist corresponding to L/K where L = Cyclotomic(7).";
print "";

print "Form no 38 is eliminated because it is a quadratic twist of a form at level Q2^2*Q3, while the conductor of the Frey variety at Q7 has exponent 1 or 2 up to quadratic twist.";
print "";

print "";
print "Eliminating form 16";
f:=forms212[16];
Kf:=BaseField(f);
_,toKf:=IsSubfield(K,Kf);
B13a:=BoundFormC([I13a],f,Kf,{},toKf);
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
B13ab:=BoundFormC([I13a,I13b],f,Kf,B5,toKf);
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();



for i in [33,41,42] do 
	print "";
	print "Eliminating form",i;
	f:=forms212[i];
	Kf:=BaseField(f);
	_,toKf:=IsSubfield(K,Kf);
	B5:=BoundFormC([5*OK],f,Kf,{},toKf);
	B13a:=BoundFormC([I13a],f,Kf,B5,toKf);
  	print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();
end for;


print "";
print "Eliminating form 45";
f:=forms212[45];
Kf:=BaseField(f);
_,toKf:=IsSubfield(K,Kf);
B5:=BoundFormC([5*OK],f,Kf,{},toKf);
B13a:=BoundFormC([I13a],f,Kf,B5,toKf);
B11:=BoundFormC([11*OK],f,Kf,B13a,toKf);	
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();


print "";
print "We have eliminated all forms that arise by quadratic twist from smaller levels.";
print "";

print "We next deal with the remaining forms, which are distributed into 9 pairs of forms that are quadratic twists by L/K.";
print "";

print "";
print "Eliminating pair of forms 12 and 28";
f:=forms212[12];
Kf:=BaseField(f);
_,toKf:=IsSubfield(K,Kf);
B29a:=BoundPairC([I29a],f,Kf,{},toKf);
B17:=BoundPairC([17*OK],f,Kf,B29a,toKf);
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();


print "";
print "Eliminating pair of forms 17 and 24";
f:=forms212[17];
Kf:=BaseField(f);
_,toKf:=IsSubfield(K,Kf);
B5:=BoundPairC([5*OK],f,Kf,{},toKf);
B13a:=BoundPairC([I13a],f,Kf,B5,toKf);
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();


print "";
print "Eliminating pair of forms 18 and 19";
f:=forms212[18];
Kf:=BaseField(f);
_,toKf:=IsSubfield(K,Kf);
B13a:=BoundPairC([I13a],f,Kf,{},toKf);
B5:=BoundPairC([5*OK],f,Kf,B13a,toKf);
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();


print "";
print "Eliminating pair of forms 20 and 21";
f:=forms212[20];
Kf:=BaseField(f);
_,toKf:=IsSubfield(K,Kf);
B13a:=BoundPairC([I13a],f,Kf,{},toKf);
B11:=BoundPairC([11*OK],f,Kf,B13a,toKf);
B17:=BoundPairC([17*OK],f,Kf,B11,toKf);
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();

print "";
print "Eliminating pair of forms 22 and 23";
f:=forms212[22];
Kf:=BaseField(f);
_,toKf:=IsSubfield(K,Kf);
B13a:=BoundPairC([I13a],f,Kf,{},toKf);
B11:=BoundPairC([11*OK],f,Kf,B13a,toKf);
B17:=BoundPairC([17*OK],f,Kf,B11,toKf);
print "We use refined elimination with auxiliary prime q = 29 to deal with p = 13:";
_:=RefinedEliminationPairC([I29a,I29b],f,Kf,13,toKf);
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();



print "";
print "Eliminating pair of forms 46 and 47";
f:=forms212[46];
Kf:=BaseField(f);
_,toKf:=IsSubfield(K,Kf);
B5:=BoundPairC([5*OK],f,Kf,{},toKf);
B13a:=BoundPairC([I13a],f,Kf,B5,toKf);
B11:=BoundPairC([11*OK],f,Kf,B13a,toKf);
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();


print "";
print "Eliminating pair of forms 48 and 51";
f:=forms212[48];
Kf:=BaseField(f);
_,toKf:=IsSubfield(K,Kf);
B5:=BoundPairC([5*OK],f,Kf,{},toKf);
B13a:=BoundPairC([I13a],f,Kf,B5,toKf);
B11:=BoundPairC([11*OK],f,Kf,B13a,toKf);
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();


print "";
print "Eliminating pair of forms 57 and 58";
f:=forms212[57];
Kf:=BaseField(f);
_,toKf:=IsSubfield(K,Kf);
B29a:=BoundPairC([I29a],f,Kf,{},toKf);
B5:=BoundPairC([5*OK],f,Kf,B29a,toKf);
print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();



print "";
print "Eliminating pair of forms 60 and 61";
f:=forms212[60];
Kf:=BaseField(f);
_,toKf:=IsSubfield(K,Kf);
Kf18:=Subfields(Kf,18)[1,1];
_,QtoKf18:=IsSubfield(Rationals(),Kf18);
Kf6:=OptimizedRepresentation(Subfields(Kf,6)[1,1]);
_,toKf6:=IsSubfield(K,Kf6);
Kfrel:=RelativeField(Kf6,Kf);
B5:=BoundPairC([5*OK],f,Kf18,{},QtoKf18);
B11:=BoundPairC([11*OK],f,Kf18,B5,QtoKf18);
B13a:=BoundPairC([I13a],f,Kfrel,B11,toKf6);

print "++++++++++++++++++++++ Total running time (in hours) =", Realhours();
print "All forms were eliminated.";

print "";
print "********************************************************";
print "* The main theorem is proved using curves E, F and C ! *";
print "********************************************************";
print "";
