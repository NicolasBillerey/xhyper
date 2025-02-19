/*
    Field K and useful general functions
*/


// The number field K
// In the notation of the paper, we have w1 = z and w2 = w1^2 - 2 = z^2 - 2
P<x>:=PolynomialRing(Rationals());
K<z>:=NumberField(x^3 + x^2 - 2*x - 1);
OK:=Integers(K);

// The unit group in K
U,phi:=UnitGroup(K);

G:=Automorphisms(K); // Automorphism group of K

// Useful factorizations and prime ideals

I2:=Factorisation(2*OK)[1,1];
I3:=Factorisation(3*OK)[1,1];
I7:=Factorisation(7*OK)[1,1];


fact13:=Factorisation(13*OK);
I13a:=fact13[1,1];
I13b:=fact13[2,1];
I13c:=fact13[3,1];

fact29:=Factorisation(29*OK);
I29a:=fact29[1,1];
I29b:=fact29[2,1];
I29c:=fact29[3,1];

// General functions

// This function computes the running time (in hours)
t0:=Realtime();
function Realhours();
   return Realtime(t0)/3600;
end function;
