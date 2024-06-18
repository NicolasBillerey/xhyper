/*
    Frey curve F
*/


// The Frey elliptic curve F and its twists
alfa:=z^2 - z - 2; // this is w2 - w1 in the notation of the paper
beta:=-z^2 + 4; // this is 2 - w2 in the notation of the paper

function FreyF(a,b,d);
	A:=alfa*(a+b)^2;
	B:=beta*(a^2 + z*a*b + b^2);
	return EllipticCurve([0,d*(B-A),0,-d^2*A*B,0]);
end function;



// Given a form f, this function computes a possible bound for p using the NORM OF THE DIFFERENCE between the a_Q coefficients for Q|q 
// When p is bounded, returns a set of possible values for p
// When no bound is found, returns {}

function BoundFormF(q,f,twist,exponents);
	// q is the residue characteristic of the auxiliary primes
	// f is the form to eliminate
	// d is the twist of the Frey curve F to be considered
	// exponents should be a set with the prime exponents to eliminate; if no restrictions are known set exponents:={}
	F:=CoefficientField(f);
	factQ:=Factorisation(q*OK);
	B:=1;
	for x,y in [0..q-1] do
		if (x le y) and ([x,y] ne [0,0]) then
			Bxy:=0;
			C:=FreyF(x,y,twist);
			for i in [1..#factQ] do
				Q:=factQ[i,1];
				if LocalInformation(C,Q)[3] eq 0 then 
					// Here C has good reduction at Q
					diffQ:=Norm(TraceOfFrobenius(C,Q)-HeckeEigenvalue(f,Q));
				else
					// Here C has bad multiplicative reduction at Q
					diffQ:=Norm((Norm(Q)+1)^2-HeckeEigenvalue(f,Q)^2);
				end if;
				Bxy:=Gcd(Integers()!Bxy,Integers()!diffQ);
			end for;
			if Bxy eq 0 then
				return {}; // Here p is unbounded
			else
				B:=B*Bxy;
			end if;
		end if;
	end for;
	Sf:={p : p in Set(PrimeDivisors(B)) | p gt 3 and p ne 7};
	if exponents ne {} then
		return (Sf meet exponents) join {q};
	else
		return Sf join {q};
	end if;
end function;

// Given a form f, this function computes a possible bound for P using the DIFFERENCE between the a_Q coefficients for Q|q
// When a bound is found, returns a set of possible values for P
// When no bound is found, returns {}

function RefinedBoundFormF(q,f,twist,ideals);
	// q is the residue characteristic of the auxiliary primes
	// f is the form to eliminate
	// d the twist of the Frey curve F to be considered
	// ideals should be a set of prime ideals to eliminate; if no restrictions are known set ideals:={}
	F:=CoefficientField(f);
	if F eq Rationals() then
		OF:=1;
	else
		OF:=Integers(F);
	end if;
	factQ:=Factorisation(q*OK);
	B:=1*OF;
	for x,y in [0..q-1] do
		if (x le y) and ([x,y] ne [0,0]) then
			Bxy:=0*OF;
			C:=FreyF(x,y,twist);
			for i in [1..#factQ] do
				Q:=factQ[i,1];
				if LocalInformation(C,Q)[3] eq 0 then
					// Here C has good reduction at Q
					diffQ:=TraceOfFrobenius(C,Q)-HeckeEigenvalue(f,Q);
				else
					// Here C has bad multiplicative reduction at Q
					diffQ:=(Norm(Q)+1)^2-HeckeEigenvalue(f,Q)^2;
				end if;
				if F eq Rationals() then
					Bxy:=Gcd(Integers()!Bxy,Integers()!diffQ);			
				else
					Bxy:=Gcd(Bxy,diffQ*OF);
				end if;
			end for;
			if Bxy eq 0*OF then
				print "p unbounded using refined elimination with q = ",q;
				return {}; // Here p is unbounded
			else
				B:=B*Bxy;
			end if;
		end if;
	end for;

	Sf:=Set([I[1] : I in Factorisation(B)]);

	if ideals ne {} then
		return (Sf meet ideals) join Set([I[1] : I in Factorisation(q*OF)]);
	else
		return Sf join Set([I[1] : I in Factorisation(q*OF)]);
	end if;
end function;




// For each form f in a given space, this function checks for a congruence between f and the twisted curve using standard 
// elimination with a given set of auxiliary primes 

function BoundF(forms,twist,AuxiliaryPrimes);
	print "Performing standard elimination for",#forms,"form(s) with set of auxiliary primes",AuxiliaryPrimes;
	for i in [1..#forms] do
		f:=forms[i];
		print "";
		print "Checking form no",i;
		print "";
		Sf:={};
		bool:=0;
  		for q in AuxiliaryPrimes do
			if bool eq 0 or Sf ne {} then
				print "Dealing with q =",q;
				Sq:=BoundFormF(q,f,twist,Sf);
				if Sq ne {} then // Here f can be discarded for large enough p
					if bool eq 0 then
						print "This form can be eliminated for large enough p !";
						Sf:=Sq;
						bool:=1;
					end if;
					Sf:=Sf meet Sq;
					Sf:={p : p in Sf | p gt 3 and p ne 7};
					if Sf ne {} then
                        print "Prime exponents remaining to eliminate =",Sf;
                    end if;
			    end if;
			end if;
		end for;
		if bool eq 0 then
		    	print "Form no",i," not eliminated for large enough p";
	  	else
			if Sf eq {} then
				print "Form no",i,"is eliminated";
			else
				print "Form no",i;
				print "with coefficient field :", CoefficientField(f) ;
				print "is not eliminated for prime(s) :",Sf;
			end if;
		end if;
		print "*************************************************************";
	end for;
	return "";
end function;


// For a given form f, this function returns the possible ideals P|p (possibly for restricted values of p) such that 
// there is a possible congruence between f and the twisted curve using refined elimination with a given set of auxiliary primes

function RefinedBoundF(f,twist,AuxiliaryPrimes,exponents);
	// exponents should be a set of prime exponents to eliminate; if no restrictions are known set exponents:={}
	print "Performing refined elimination with set of auxiliary primes",AuxiliaryPrimes;
	print "";
	F:=CoefficientField(f);
	if F eq Rationals() then
		OF:=1;
	else
		OF:=Integers(F);
	end if;
	if #exponents eq 0 then
		Sf:={};
	else
		N:=1;
		for p in exponents do
			N:=N*p;
		end for;
		Sf:=Set([I[1] :  I in Factorisation(N*OF)]);
	end if;
	bool:=0;
  	for q in AuxiliaryPrimes do
		if bool eq 0 or Sf ne {} then
			print "Dealing with q =",q;
			Sq:=RefinedBoundFormF(q,f,twist,Sf);
			if Sq ne {} then
				if bool eq 0 then
					Sf:=Sq;
					bool:=1;
				end if;
				Sf:=Sf meet Sq;
				if #exponents eq 0 then
					Sf:={P : P in Sf};
				else
					Sf:={P : P in Sf | Characteristic(ResidueClassField(P)) in exponents};
				end if;
				print "Number of prime ideals remaining to eliminate = ",#Sf;
		    end if;
		end if;
	end for;
	if bool eq 0 then
	    	print "The form is not eliminated";
	else
		if Sf eq {} then
			print "The form is eliminated";
		else
			print "The form with coefficient field :", CoefficientField(f) ;
			print "is not eliminated for",#Sf,"prime ideal(s) above :", Set([Characteristic(ResidueClassField(P)) : P in Sf]);
		end if;
	end if;
	print "*************************************************************";
	return "";
end function;
