/*
    Frey curve C
*/



// Returns the base change to K of the hyperelliptic Frey curve C constructed by Kraus attached to solution (a,b,c) 
function FreyC(a,b);
	R<x>:=PolynomialRing(K);
	return HyperellipticCurve(x^7 + 7*a*b*x^5 + 14*a^2*b^2*x^3 + 7*a^3*b^3*x + b^7 - a^7);
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
// For a prime Q of K of good reduction the degree 6 Euler factor at Q factors into 3 degree 2 polynomials, where the middle coefficients 
// are minus the traces.

function TraceFrobenius(C,Q);
	R:=PolynomialRing(K);	
	Lf:=EulerFactor(C,Q);
	Lf:=Reverse(Lf);
	Lfactor:=Factorization(R!Lf);
	return Set([-Coefficient(f[1],1) : f in Lfactor]); 
end function;


// Computes the value of the mod 7 cyclotomic character on a Frobenius at Q
function TwistCyclo(Q);
	if (Norm(Q) mod 7) eq (1 mod 7) then
		 return 1;
	else
		return -1;
	end if;
end function;


// Check for an isomorphism between the mod p representation of J and that of f
// using the NORM OF THE DIFFERENCE of the traces

function BoundFormC(QQs,f,LL,exponents,toLL)
	// QQs is a subset of the primes in K above the same rational prime q
	// f is the form to eliminate satisfying that K is contained in its coefficient field Kf
	// LL should be Kf or a subfield of it containing the trace of Frobenius at QQs of f
	// exponents should be a set with a list of prime exponents to eliminate; 
	// (if no restrictions are known set exponents:={})
	// toLL should be a field inclusion of K into (a subfield of) LL
	// When q is inert in K, one may take for toLL the trivial embedding of Q into LL

		
	Q1:=QQs[1]; // pick one prime ideal in QQs
	q:=Characteristic(ResidueClassField(Q1)); // common residue characteristic of prime ideals in QQs
	Nq:=Norm(Q1); // common norm of prime ideals in QQs


	print "Performing standard elimination with",#Set(QQs),"prime ideal(s) above",q;

	B:={};

    ggs:=[find_g(Q1,Q) : Q in QQs]; // for each Q in QQs find g in G such that g(Q1) = Q 

	// traces of Frobenius at prime ideals in QQs
	hL:=[HeckeEigenvalue(f,Q) : Q in QQs]; 

	// Taking into account primes of bad reduction
	Lbad:=Gcd([Integers()!AbsoluteNorm(LL!(Nq+1)^2 - LL!hL[i]^2) : i in [1..#QQs]]);


	if #exponents eq 0 then 
		B:=B join PrimeSet(Lbad);
	else 
		B:=B join {p : p in exponents | Lbad mod p eq 0};		    
	end if;

	if (Nq mod 4) eq (1 mod 4) then
		for x,y in [0..q-1] do
			if (x le y) and ((x^7+y^7) mod q ne 0) then
				C:=FreyC(x,y);
                Tq:=TraceFrobenius(C,Q1); // independent of the choice of Q = Q1 in QQs
				Lxy:=1;
				for u in Tq do
					Gcdxyu:=Gcd([Integers()!AbsoluteNorm(toLL(g(u)) - LL!HeckeEigenvalue(f,g(Q1))) : g in ggs]);
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
			if (x le y) and ((x^7+y^7) mod q ne 0) then
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

	B:={x : x in B | x notin {1,2,3,7,q}};

	if (q in exponents) or ((exponents eq {}) and (q notin {2,3,7})) then
		B:= B join {q};
	end if;

	if #B eq 0 then
			print "Form eliminated !";
			return B, true;
	else		
		print "We still have to eliminate exponents p =",B meet exponents;
		return B, false;
	end if;
end function;


// Check for an isomorphism between the mod p representation of J and that of f
// using the DIFFERENCE of the traces

function RefinedEliminationFormC(QQs,f,LL,p,toLL);
	// QQs is a subset of the primes in K above the same rational prime q
	// f is the form to eliminate satisfying that K is contained in its coefficient field Kf
	// LL should be Kf or a subfield of it containing the trace of Frobenius at QQs of f
	// p is the prime exponent to eliminate; 
	// toLL should be a field inclusion of K into (a subfield of) LL
	// When q is inert in K, one may take for toLL the trivial embedding of Q into LL

	Q1:=QQs[1]; // pick one prime ideal in QQs
	q:=Characteristic(ResidueClassField(Q1)); // common residue characteristic of prime ideals in QQs
	Nq:=Norm(Q1); // common norm of prime ideals in QQs

	afQ:=[HeckeEigenvalue(f,Q) : Q in QQs];
	
	Kf:=BaseField(f);
	factP:=[I[1] : I in Factorization(p*Integers(Kf))]; // Factorization of p in Kf

	// List of residue fields and reduction maps for each prime ideals above p in Kf

	ResFields:=[<QQ,toQQ> where QQ,toQQ := ResidueClassField(I) : I in factP]; // residue fields and reduction maps
	zeroes:=[*[res[2](0) : j in [1..#QQs]] : res in ResFields*];
	reductions:=[*[res[2]((Nq+1)^2 - afQ[i]^2) : i in [1..#QQs]] : res in ResFields*]; // reductions of aQ(f)^2 - (Nq + 1)^2 mod P for P|p

	BoolBadRed:=({reductions[i] eq zeroes[i] : i in [1..#ResFields]} eq {false});

	if BoolBadRed eq false then 
		print "form not eliminated for p =", p;
		return false;
	end if;

	BoolGoodRed:=true;

	ggs:=[find_g(Q1,Q) : Q in QQs];

	if (Nq mod 4) eq (1 mod 4) then
		for x,y in [0..q-1] do
			if (x le y) and ((x^7+y^7) mod q ne 0) and BoolGoodRed then
				C:=FreyC(x,y);
				Tq:=TraceFrobenius(C,Q1); // independent of the choice of Q = Q1 in QQs
				for u in Tq do
					list:=[*[res[2](HeckeEigenvalue(f,g(Q1)) - toLL(g(u)))  : g in ggs]: res in ResFields*];
					if not ({list[i] eq zeroes[i] : i in [1..#ResFields]} eq {false}) then 
						BoolGoodRed:=false;
						break;
					end if;	
				end for;	 
			end if;
		end for;
	else
		for x,y in [0..q-1] do
			if (x le y) and ((x^7+y^7) mod q ne 0) and BoolGoodRed then
				C:=FreyC(x,y);
				Tq:=TraceFrobenius(C,Q1); // independent of the choice of Q = Q1 in QQs
				for u in Tq do
					list:=[*[res[2](HeckeEigenvalue(f,g(Q1))^2 - toLL(g(u)^2))  : g in ggs]: res in ResFields*];
					if not ({list[i] eq zeroes[i] : i in [1..#ResFields]} eq {false}) then 
						BoolGoodRed:=false;      				
						break;
					end if;
				end for;
			end if;		
		end for;	 
	end if;  

	
	
	if BoolGoodRed then 
		print "Form eliminated for p =", p;
		return true;	
	else
		print "Form not eliminated for p =", p;
		return false;
	end if;	
	
end function;


// Check for an isomorphism between the mod p representation of J and that of f
// or its quadratic twist by the mod 7 cyclotomic character
// using the NORM OF THE DIFFERENCE of the traces

function BoundPairC(QQs,f,LL,exponents,toLL)
	// QQs is a subset of the primes in K above the same rational prime q
	// f is one of two forms which are related by the quadratic twist by the character corresponding to Q(zeta_7)/K
	// f should contain K in its field of coefficients Kf. This implies that the traces of Frobenius of FreyC at QQs belong to Kf
	// LL should be Kf or a subfield of it containing the trace of Frobenius at QQs of f
	// exponents should be a set with a list of prime exponents to eliminate; if no restrictions are known set exponents:={}
	// toLL should be a field inclusion of K into (a subfield of) LL
	// When q is inert in K, one may take for toLL the trivial embedding of Q into LL

	Q1:=QQs[1]; // pick one prime ideal in QQs
	q:=Characteristic(ResidueClassField(Q1)); // common residue characteristic of prime ideals in QQs
	Nq:=Norm(Q1); // common norm of prime ideals in QQs

	print "Performing standard elimination with",#Set(QQs),"prime ideal(s) above",q;	

	B:={};

    ggs:=[find_g(Q1,Q) : Q in QQs]; // for each Q in QQs find g in G such that g(Q1) = Q 

	// traces of Frobenius at prime ideals in QQs
	hL:=[HeckeEigenvalue(f,Q) : Q in QQs]; 

	// Taking into account primes of bad reduction
	Lbad:=Gcd([Integers()!AbsoluteNorm(LL!(Nq+1)^2 - LL!hL[i]^2) : i in [1..#QQs]]);

	

	if #exponents eq 0 then 
		B:=B join PrimeSet(Lbad);
	else 
		B:=B join {p : p in exponents | Lbad mod p eq 0};		    
	end if;


	if (Nq mod 4 eq 1) and (Nq mod 7 eq 1) then
		for x,y in [0..q-1] do
			if (x le y) and ((x^7+y^7) mod q ne 0) then
				C:=FreyC(x,y);
                Tq:=TraceFrobenius(C,Q1); // independent of the choice of Q = Q1 in QQs
				Lxy:=1;
				for u in Tq do
					Gcdxy:=Gcd([Integers()!AbsoluteNorm(toLL(g(u)) - LL!HeckeEigenvalue(f,g(Q1))) : g in ggs]);
					if Gcdxy eq 0 then
						if #exponents eq 0 then
							print "Form not eliminated using",QQs;
						else
							print "We still have to eliminate",exponents;
						end if;
						return false;
					end if;
					Lxy:=Lxy*Gcdxy;
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
			if (x le y) and ((x^7+y^7) mod q ne 0) then
				C:=FreyC(x,y);
                Tq:=TraceFrobenius(C,Q1); // independent of the choice of Q = Q1 in QQs
				Lxy:=1;
				for u in Tq do
					Gcdxy:=Gcd([Integers()!AbsoluteNorm(toLL(g(u)^2) - LL!HeckeEigenvalue(f,g(Q1))^2) : g in ggs]);
					if Gcdxy eq 0 then
						if #exponents eq 0 then
							print "Form not eliminated using",QQs;
						else
							print "We still have to eliminate",exponents;
						end if;
						return false;
					end if;
					Lxy:=Lxy*Gcdxy;
				end for;
				if #exponents eq 0 then 
					B:=B join PrimeSet(Lxy);
				else 
					B:=B join {p : p in exponents | Lxy mod p eq 0};		    
				end if;
			end if;  
		end for;
	end if;

	B:={x : x in B | x notin {1,2,3,7,q}};

	if (q in exponents) or ((exponents eq {}) and (q notin {2,3,7})) then
		B:= B join {q};
	end if;

	if #B eq 0 then
			print "The form and its twist by the mod 7 cyclotomic character are eliminated !";
			return B, true;
	else		
		print "We still have to eliminate exponents p =",B meet exponents;
		return B, false;
	end if;
end function;


// Check for an isomorphism between the mod p representation of J and that of f
// or its quadratic twist by the mod 7 cyclotomic character
// using THE DIFFERENCE of the traces

function RefinedEliminationPairC(QQs,f,LL,p,toLL);
	// QQs is a subset of the primes in K above the same rational prime q
	// f is the form to eliminate satisfying that K is contained in its coefficient field Kf
	// LL should be Kf or a subfield of it containing the trace of Frobenius at QQs of f
	// p is the prime exponent to eliminate
	// toLL should be a field inclusion of K into (a subfield of) LL
	// When q is inert in K, one may take for toLL the trivial embedding of Q into LL

	Q1:=QQs[1]; // pick one prime ideal in QQs
	q:=Characteristic(ResidueClassField(Q1)); // common residue characteristic of prime ideals in QQs
	Nq:=Norm(Q1); // common norm of prime ideals in QQs
	afQ:=[HeckeEigenvalue(f,Q) : Q in QQs];

	Kf:=BaseField(f);
	factP:=[I[1] : I in Factorization(p*Integers(Kf))]; // Factorization of p in Kf

	// List of residue fields and reduction maps for each prime ideals above p in Kf

	ResFieldsKf:=[<QQ,toQQ> where QQ,toQQ := ResidueClassField(I) : I in factP];
	zeroes:=[*[res[2](0) : j in [1..#QQs]] : res in ResFieldsKf*];
	list:=[*[res[2]((Nq+1)^2 - afQ[i]^2) : i in [1..#QQs]] : res in ResFieldsKf*];

	BoolBadRed:=({list[i] eq zeroes[i] : i in [1..#ResFieldsKf]} eq {false});

	if BoolBadRed eq false then 
		print "form not eliminated for p =", p;
		return false;
	end if;

	BoolGoodRed:=true;
	
	ggs:=[find_g(Q1,Q) : Q in QQs];

	//ResFieldsK:=[<QQ,toQQ> where QQ,toQQ := ResidueClassField(I[1]) : I in Factorisation(p*OK)];
		
		
	if  (Nq mod 4 eq 1) and (Nq mod 7 eq 1) then
		ReducedTracesf:=[*[res[2](t) : t in afQ] : res in ResFieldsKf*];
		for x,y in [0..q-1] do	
			if (x le y) and ((x^7+y^7) mod q ne 0) and BoolGoodRed then
				C:=FreyC(x,y);
				Tq:=TraceFrobenius(C,Q1); // independent of the choice of Q = Q1 in QQs
				for t in Tq do
						list:=[*[res[2](HeckeEigenvalue(f,g(Q1)) - toLL(g(t)))  : g in ggs]: res in ResFieldsKf*];
						if not ({list[i] eq zeroes[i] : i in [1..#ResFieldsKf]} eq {false}) then 
							BoolGoodRed:=false;
						break;
					end if;	
				end for;
			end if;
		end for;
	else
		for x,y in [0..q-1] do	
			if (x le y) and ((x^7+y^7) mod q ne 0) and BoolGoodRed then
				C:=FreyC(x,y);
				Tq:=TraceFrobenius(C,Q1); // independent of the choice of Q = Q1 in QQs
				for t in Tq do
					list:=[*[res[2](HeckeEigenvalue(f,g(Q1))^2 - toLL(g(t)^2))  : g in ggs]: res in ResFieldsKf*];
					if not ({list[i] eq zeroes[i] : i in [1..#ResFieldsKf]} eq {false}) then 
						BoolGoodRed:=false;      				
						break;
					end if;
				end for;
			end if;
		end for;
	end if;	 

	if BoolBadRed eq false then 
		print "Form not eliminated due to level raising condition for p =", p;
		return false;
	else
		if BoolGoodRed then 
			print "The form and its twist by the mod 7 cyclotomic character are eliminated for p =", p;
			return true;	
		else
			print "Form not eliminated for p =", p;
			return false;
		end if;	
	end if;
end function;



// Check for an isomorphism between the mod p representation of J and 
// that of f twisted by the mod 7 cyclotomic character using the NORM 
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

	// traces of Frobenius at prime ideals in QQs twisted by mod 7 cyclotomic character
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
			if (x le y) and ((x^7+y^7) mod q ne 0) then
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
			if (x le y) and ((x^7+y^7) mod q ne 0) then
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

	B:={x : x in B | x notin {1,2,3,7,q}};

	if (q in exponents) or ((exponents eq {}) and (q notin {2,3,7})) then
		B:= B join {q};
	end if;

	if #B eq 0 then
			print "The form (twisted by the mod 7 cyclotomic character) is eliminated !";
			return B, true;
	else		
		print "We still have to eliminate exponents p =",B meet exponents;
		return B, false;
	end if;
end function;


// Check for an isomorphism between the mod p representation of J and that
// of f twisted by the mod 7 cyclotomic character using the difference of the traces

function RefinedEliminationFormCTwisted(QQs,f,LL,p,toLL);
	// QQs is a subset of the primes in K above the same rational prime q
	// f is the form to eliminate satisfying that K is contained in its coefficient field Kf
	// LL should be Kf or a subfield of it containing the trace of Frobenius at QQs of f
	// p is the prime exponent to eliminate; 
	// toLL should be a field inclusion of K into (a subfield of) LL
	// When q is inert in K, one may take for toLL the trivial embedding of Q into LL

	Q1:=QQs[1]; // pick one prime ideal in QQs
	q:=Characteristic(ResidueClassField(Q1)); // common residue characteristic of prime ideals in QQs
	Nq:=Norm(Q1); // common norm of prime ideals in QQs

	twist:=TwistCyclo(Q1); // independent of the choice of Q = Q1 in QQs

	afQ:=[HeckeEigenvalue(f,Q)*twist : Q in QQs];
	
	Kf:=BaseField(f);
	factP:=[I[1] : I in Factorization(p*Integers(Kf))]; // Factorization of p in Kf

	// List of residue fields and reduction maps for each prime ideals above p in Kf
	
	ResFields:=[<QQ,toQQ> where QQ,toQQ := ResidueClassField(I) : I in factP];
	zeroes:=[*[res[2](0) : j in [1..#QQs]] : res in ResFields*];
	reductions:=[*[res[2]((Nq+1)^2 - afQ[i]^2) : i in [1..#QQs]] : res in ResFields*]; // reductions of aQ(f)^2 - (Nq + 1)^2 mod P|p

	BoolBadRed:=({reductions[i] eq zeroes[i] : i in [1..#ResFields]} eq {false});

	if BoolBadRed eq false then 
		print "form not eliminated for p =", p;
		return false;
	end if;

	BoolGoodRed:=true;

	ggs:=[find_g(Q1,Q) : Q in QQs];

	if (Nq mod 4 eq 1) then
		for x,y in [0..q-1] do
			if (x le y) and ((x^7+y^7) mod q ne 0) and BoolGoodRed then
				C:=FreyC(x,y);
				Tq:=TraceFrobenius(C,Q1); // independent of the choice of Q = Q1 in QQs
				for u in Tq do
						list:=[*[res[2](HeckeEigenvalue(f,g(Q1))*twist - toLL(g(u)))  : g in ggs]: res in ResFields*];
						if not ({list[i] eq zeroes[i] : i in [1..#ResFields]} eq {false}) then 
							BoolGoodRed:=false;
						break;
					end if;	
				end for;	 
			end if;  
		end for;
	else
		for x,y in [0..q-1] do
			if (x le y) and ((x^7+y^7) mod q ne 0) and BoolGoodRed then
				C:=FreyC(x,y);
				Tq:=TraceFrobenius(C,Q1); // independent of the choice of Q = Q1 in QQs
				for u in Tq do
					list:=[*[res[2](HeckeEigenvalue(f,g(Q1))^2 - toLL(g(u)^2))  : g in ggs]: res in ResFields*];
					if not ({list[i] eq zeroes[i] : i in [1..#ResFields]} eq {false}) then 
						BoolGoodRed:=false;      				
						break;
					end if;
				end for;
			end if;		
		end for;	 
	end if;  

	
	
	if BoolGoodRed then 
		print "Form (twisted by the mod 7 cyclotomic character) eliminated for p =", p;
		return true;	
	else
		print "Form not eliminated for p =", p;
		return false;
	end if;	
	
end function;
