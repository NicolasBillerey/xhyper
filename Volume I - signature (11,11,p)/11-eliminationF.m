/*
    We perform the elimination in the case 2 divides a+b using F/K for p \geq 5.
*/


load "11-fieldK.m";
load "11-curveF.m";


N10:=I2;
print "\nComputing newforms of level Q2. Dimension of the space:", Dimension(NewSubspace(HilbertCuspForms(K,N10)));
forms10:=Eigenforms(NewSubspace(HilbertCuspForms(K,N10)));
print "There is",#forms10,"newform to eliminate.";


BoundF(forms10,[3,23],-11);

f10:=forms10[1];
RefinedBoundF(f10,{23},5,-11);
RefinedBoundF(f10,{23},31,-11);


// To apply Kimball Martin Theorem 2.1 we use formula (1.6) in his paper to compute m(O).
// This formula involves evaluation the Zeta function of K at -1.


print "We now compute m(O) in the notation of Kimball Martin.";
assert ClassNumber(K) eq NarrowClassNumber(K);

print "\nWe first compute Zeta_K(-1):\n";
LK := LSeries(K : Precision := 10);
s := Evaluate(LK, -1);
MinimalPolynomial(s,1);
print "\nThis shows that Zeta_K(-1) = -20/33.";
print "\nWe now compute m(O):";
print "m(O) =",2^(1-Degree(K))*ClassNumber(K)*20/33*Norm(I2)*(1-1/#ResidueClassField(I2));

print "\nSince 5 and 31 divide the numerator of m(O), we have eliminated all forms at level Q2.\n";
print "*******************************\n";

N11:=I2*I11;
print "\nComputing newforms of level Q2*Q11. Dimension of the space:", Dimension(NewSubspace(HilbertCuspForms(K,N11)));
forms11:=Eigenforms(NewSubspace(HilbertCuspForms(K,N11)));
print "There are",#forms11,"newforms to eliminate.";

BoundF(forms11,[3,23],1);

print "We have proved that for p > 3 prime, there are no primitive solutions (a,b,c) to x^11 + y^11 = z^p such that 2 divides a+b.";

print "++++++++++++++++++++++", Realhours();