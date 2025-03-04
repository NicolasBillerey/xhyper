/*
    We define the Frey hyperelliptic curve C = C_11(a,b)/K as well as the functions used for elimination.
*/



// Returns the base change to K of the hyperelliptic Frey curve C constructed by Kraus attached to solution (a,b,c) 
function FreyC(a,b);
	R<x>:=PolynomialRing(K);
	return HyperellipticCurve(x^11 + 11*a*b*x^9 + 44*a^2*b^2*x^7 + 77*a^3*b^3*x^5 + 55*a^4*b^4*x^3 + 11*a^5*b^5*x + b^11 - a^11);
end function;


// This function finds the automorphism of G mapping ideal (or element) Q1 to Q2
function find_g(Q1,Q2);
	for g in G do
        if Q2 eq g(Q1) then
            return g;
        end if;
	end for;
end function;


// The Jacobian J=J(C) is of GL2-type over K. We want to extract the traces of Frobenius of the 2-dim representations of G_K attached to J/K . 
// For a prime Q of K of good reduction the degree 10 Euler factor at Q factors into 5 degree 2 polynomials, where the middle coefficients are minus the traces.

function TraceFrobenius(C,Q);
	R:=PolynomialRing(K);	
	Lf:=EulerFactor(C,Q);
	Lf:=Reverse(Lf);
	Lfactor:=Factorization(R!Lf);
	return Set([-Coefficient(f[1],1) : f in Lfactor]); 
end function;


// Computes the value of the mod 11 cyclotomic character on a Frobenius at Q
function TwistCyclo(Q);
	if (Norm(Q) mod 11) eq (1 mod 11) then
		 return 1;
	else
		return -1;
	end if;
end function;


// Check for an isomorphism between the mod p representation of J and 
// that of f twisted by the mod 11 cyclotomic character using the NORM 
// of the difference of the traces

function BoundFormCTwisted(QQs,f,LL,exponents,toLL)
	// QQs is a subset of the primes in K above the same rational prime q
	// f is the form to eliminate satisfying that K is contained in its coefficient field Kf
	// LL should be Kf or a subfield of it containing the trace of Frobenius at QQs of f
	// exponents should be a set with a list of prime exponents to eliminate; 
	// if no restrictions are known set exponents:={}
	// toLL should be a field inclusion of K into (a subfield of) LL
	// When q is inert in K, one may take for toLL the trivial embedding of Q into LL


	Q1:=QQs[1]; // pick one prime ideal in QQs
	q:=Characteristic(ResidueClassField(Q1)); // common residue characteristic of prime ideals in QQs
	Nq:=Norm(Q1); // common norm of prime ideals in QQs

	twist:=TwistCyclo(Q1); // independent of the choice of Q = Q1 in QQs

	print "Performing standard elimination with",#Set(QQs),"prime ideal(s) above",q;


	B:={};

    ggs:=[find_g(Q1,Q) : Q in QQs]; // for each Q in QQs find g in G such that g(Q1) = Q

	// traces of Frobenius at prime ideals in QQs twisted by mod 11 cyclotomic character
	hL:=[HeckeEigenvalue(f,Q)*twist : Q in QQs]; 

	// Taking into account primes of bad reduction
	Lbad:=Gcd([Integers()!AbsoluteNorm(LL!(Nq+1)^2 - LL!hL[i]^2) : i in [1..#QQs]]);


	if #exponents eq 0 then 
		B:=B join PrimeSet(Lbad);
	else 
		B:=B join {p : p in exponents | Lbad mod p eq 0};		    
	end if;

	if (Nq mod 4 eq 1) then
		for x,y in [0..q-1] do
			if (x le y) and ((x^11+y^11) mod q ne 0) then
				C:=FreyC(x,y);
                Tq:=TraceFrobenius(C,Q1); // independent of the choice of Q = Q1 in QQs
					Lxy:=1;
					for u in Tq do
						Gcdxyu:=Gcd([Integers()!AbsoluteNorm(toLL(g(u)) - LL!HeckeEigenvalue(f,g(Q1))*twist) : g in ggs]);
						if Gcdxyu eq 0 then
							if #exponents eq 0 then
								print "Form not eliminated using",QQs;
							else
								print "We still have to eliminate",exponents;
							end if;
							return false;
						end if;
						Lxy:=Lxy*Gcdxyu;
					end for;
				if #exponents eq 0 then 
						B:=B join PrimeSet(Lxy);
					else 
						B:=B join {p : p in exponents | Lxy mod p eq 0};		    
                end if;
			end if;  
		end for;
	else
		for x,y in [0..q-1] do
			if (x le y) and ((x^11+y^11) mod q ne 0) then
				C:=FreyC(x,y);
                Tq:=TraceFrobenius(C,Q1); // independent of the choice of Q = Q1 in QQs
					Lxy:=1;
					for u in Tq do
						Gcdxyu:=Gcd([Integers()!AbsoluteNorm(toLL(g(u)^2) - LL!HeckeEigenvalue(f,g(Q1))^2) : g in ggs]);
						if Gcdxyu eq 0 then
							if #exponents eq 0 then
								print "Form not eliminated using",QQs;
							else
								print "We still have to eliminate",exponents;
							end if;
							return false;
						end if;
						Lxy:=Lxy*Gcdxyu;
					end for;
				if #exponents eq 0 then 
						B:=B join PrimeSet(Lxy);
					else 
						B:=B join {p : p in exponents | Lxy mod p eq 0};		    
						end if;
			end if;  
		end for;
	end if;

	B:={x : x in B | x notin {1,2,3,11,q}};

	if (q in exponents) or ((exponents eq {}) and (q notin {2,3,11})) then
		B:= B join {q};
	end if;

	if #B eq 0 then
			print "The form (twisted by the mod 11 cyclotomic character) is eliminated !";
			return B, true;
	else		
		if #exponents eq 0 then
    		print "We still have to eliminate exponents p =",B;
    		return B, false;
        else
            print "We still have to eliminate exponents p =",B meet exponents;
            return B meet exponents, false;
        end if;
	end if;
end function;



  
