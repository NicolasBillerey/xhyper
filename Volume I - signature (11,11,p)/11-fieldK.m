/*
We introduce the field K = Q(zeta11)^+ (i.e., the maximal totally real subfield in Q(zeta_11)).
*/

S<x>:=PolynomialRing(Rationals());
K<w>:=NumberField(x^5 + x^4 - 4*x^3 - 3*x^2 + 3*x + 1);
OK:=Integers(K);
w2:=w^2-2;


// The unit group in K
U,phi:=UnitGroup(K);

G:=Automorphisms(K); // Automorphism group of K

// Useful factorizations and prime ideals

I2:=Factorization(2*OK)[1,1];
I3:=Factorization(3*OK)[1,1];
I5:=Factorization(5*OK)[1,1];
I7:=Factorization(7*OK)[1,1];
I11:=Factorization(11*OK)[1,1];

I23a:=Factorization(23*OK)[1,1];
//I23b:=Factorization(23*OK)[2,1];
//I23c:=Factorization(23*OK)[3,1];
//I23d:=Factorization(23*OK)[4,1];
//I23e:=Factorization(23*OK)[5,1];




// This function computes the running time (in hours)
t0:=Realtime();
function Realhours();
   return Realtime(t0)/3600;
end function;


// This function is necessary to deal with some incompatibility of universes arising in the output of some Magma functions.
// Return the set of prime divisors of x, with special treatment when x is zero or a unit.
S:=Parent({1,2,3});
function PrimeSet(x)
	x:=Integers()!x;

	if x eq 0 then
	return S!{0};
	elif x in {-1,1} then
	return S!{x};
	else 
	return S!Set(PrimeDivisors(x));
	end if;
end function;