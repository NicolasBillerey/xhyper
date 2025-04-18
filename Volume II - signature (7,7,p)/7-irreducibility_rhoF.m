/*
    We check that the mod p representation associated with F is absolutely irreducible (except for the case p = 7)
*/

load "7-fieldK.m";
load "7-curveF.m";

print "";
print "The field K is generated by z with minimal polynomial:";
print MinimalPolynomial(z);

print "";
print "The unit group of K is:";
print U;
print "and is generated by {-1, eps1, eps2} where eps1 =", K!phi(U.2)," and eps2 =", K!phi(U.3);
print "";


S:= {[0,0,12], [0,12,0], [12,0,0], [12,12,0], [12,0,12], [0,12,12]}; // list of possible signatures

// This function computes the twisted norm associated to a given signatures as in Freitas-Siksek's paper
function TwistedNorm(a,s);
    N:=1;
    i:=1;
    for g in G do
        N:=N*g(a)^s[i];
        i:= i + 1;
    end for;
    return N;
end function;

// This function computes the number A_s that appears in Theorem 1 of Freitas-Siksek
function As(s);
    return Norm(Gcd((TwistedNorm(K!phi(U.2),s) - 1)*OK,(TwistedNorm(K!phi(U.2),s) - 1)*OK));
end function;


B:=Lcm([As(s) : s in S]);

print "The integer B for the number field K from Theorem 1 in [Freitas-Siksek] is:";
print B;
print "Its factorization is:";
print Factorization(B);

print "";
print "The Ray Class Group for modulus Q2^2*Q7*oo1*oo2*oo3 is:";
R,_:=RayClassGroup(I2^2*I7,[1,2,3]);
print R;

print "";
print "This concludes the case p > 13 in the theorem.";
print "";

print "";
print "We deal with the case p = 11:";
print "";

F11:=FiniteField(11);
R<x>:=PolynomialRing(F11);
for u in {[1,1],[-1,-1],[1,0],[-1,0],[0,1],[0,-1]} do 
    C:=FreyF(u[1],u[2],1);
    assert LocalInformation(C,I3)[3] eq 0; // check whether C has good reduction at Q3
    assert IsIrreducible(x^2 - TraceOfFrobenius(C,I3)*x + Norm(I3));
end for;

print "";
print "For each curve F(a,b) with (a,b) in {(1,1),(-1,-1),(1,0),(-1,0),(0,1),(0,-1)},";
print "the characteristic polynomial of F(a,b) at Q3 is irreducible mod 11.";
print "Therefore none of these curves has a K-rational isogeny of degree 11";
print "This rules out case p = 11";
print "";



print "";
print "We deal with the case p = 13:";
print "";

print "";
print "The Ray Class Group for modulus Q2^2*Q7*Pj*oo1*oo2*oo3 where Pj|13 are:";
R13a,_:=RayClassGroup(I2^2*I7*I13a,[1,2,3]);
R13b,_:=RayClassGroup(I2^2*I7*I13b,[1,2,3]);
R13c,_:=RayClassGroup(I2^2*I7*I13c,[1,2,3]);
print R13a,R13b,R13c;

print "";
print "This concludes the case p = 13 and finishes the proof of this result.";
print "";

