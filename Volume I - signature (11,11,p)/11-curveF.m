/*
    We define the elliptic curve F/K with K = Q(zeta11)^+ as in arXiv, subsection 10.1.
*/


//load "11-fieldK.m";


// Definition of the elliptic curve F/K
function FreyF(a,b,d)
    A:=(w2-w)*(a+b)^2;
    B:=(2-w2)*(a^2+w*a*b+b^2);
    return EllipticCurve([0,d*(B-A),0,-d^2*A*B,0]);
end function;




// This function is used to eliminate (exponents for) f using the prime q and NORMS of differences of traces
function BoundFormF(q,f,exponents,d)
    // q is the auxiliary prime
	// f is the form to eliminate
	// exponents should be a set with the prime exponents to eliminate; if no restrictions are known set exponents:={}
    // Note that the ouput is {} iff q does NOT bound any exponent.
    // Moreover, if the ouput is different from {}, then it contains q by construction, but this is harmless for the elimination procedure.
    B:=1;
    factQ:=Factorisation(q*OK);
    for x,y in [0..q-1] do
        if ([x,y] ne [0,0]) and (x le y) then
            Bxy:=0; 
            C:=FreyF(x,y,d);
            for i in [1..#factQ] do
                Q:=factQ[i,1];
                if LocalInformation(C,Q)[3] eq 0 then
                    // Here C has good reduction at Q
                    diffQ:=Norm(TraceOfFrobenius(C,Q) - HeckeEigenvalue(f,Q));
                else
                    diffQ:=Norm((Norm(Q)+1)^2 - HeckeEigenvalue(f,Q)^2);
                end if;
                Bxy:=Gcd(Bxy,Integers()!diffQ);
            end for;
            if Bxy eq 0 then
            	return {}; // Here p is unbounded
            else
              B:=B*Bxy;
            end if;
        end if;
    end for;
	assert B ne 0;
    Sf:={p : p in Set(PrimeDivisors(B)) | p notin {2,3,11}};
    if exponents ne {} then
      return (Sf meet exponents) join {q};
    else
      return Sf join {q};
    end if;
end function;


// This function is used to eliminate each form in a given space using specified auxiliary primes and NORMS of differences of traces
function BoundF(forms,AuxiliaryPrimes,d);
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
                Sq:=BoundFormF(q,f,Sf,d);
                if Sq ne {} then // Here f can be discarded for large enough p
                    if bool eq 0 then
                        print "This form can be eliminated for large enough p !";
                        Sf:=Sq;
                        bool:=1;
                    end if;
                    Sf:=Sf meet Sq;
                    Sf:={p : p in Sf | p notin {2,3,11}};
                end if;
                if Sf ne {} then
                    print "Prime exponent(s) remaining to eliminate =",Sf;
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


// This function is used to eliminate the exponent p for f using a fixed prime q and DIFFERENCES of traces
// Note that the ouput is {} iff q does NOT eliminate p.
// Moreover, if the ouput is different from {}, then it contains q by construction.
// This implies that this function should NOT be used directly. Instead use the next function RefinedBoundF.
function RefinedBoundFormF(q,f,p,d);
	// q is the auxiliary prime
	// f is the form to eliminate
	// p is the exponent to eliminate
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
			C:=FreyF(x,y,d);
			for i in [1..#factQ] do
				Q:=factQ[i,1];
				if LocalInformation(C,Q)[3] eq 0 then
					// Here C has good reduction at Q
					diffQ:=TraceOfFrobenius(C,Q) - HeckeEigenvalue(f,Q);
				else
					// Here C has bad multiplicative reduction at Q
					diffQ:=(Norm(Q)+1)^2 - HeckeEigenvalue(f,Q)^2;
				end if;
				if F eq Rationals() then
					Bxy:=Gcd(Integers()!Bxy,Integers()!diffQ);			
				else
					Bxy:=Gcd(Bxy,diffQ*OF);
				end if;
			end for;
			if Bxy eq 0*OF then
            			return {}; // Here p is unbounded
            		else
              			B:=B*Bxy;
            		end if;
		end if;
	end for;
	assert B ne 0*OF;
	Sf:=Set([I[1] : I in Factorisation(q*Gcd(B,p*OF))]);
    return Sf;
end function;

// For a given form f, this function returns the possible ideals P|p (possibly for restricted values of p) such that 
// there is a possible congruence between f and the twisted curve using refined elimination with a given set of auxiliary primes

// This function is used to eliminate the exponent p for f using in turn a bunch of auxiliary primes and DIFFERENCES of traces
// Even in the case where only a single auxilliary prime is necessary, this function should be used instead of the previous one.

function RefinedBoundF(f,AuxiliaryPrimes,p,d);
	// f is the form to eliminate
	// AuxiliaryPrimes is a set of auxiliary
	// p is the exponent to eliminate
	print "Performing refined elimination to eliminate exponent",p,"with set of auxiliary primes",AuxiliaryPrimes;
	print "";
	F:=CoefficientField(f);
	if F eq Rationals() then
		OF:=1;
	else
		OF:=Integers(F);
	end if;
	Sf:=Set([I[1] :  I in Factorisation(p*OF)]);
  	for q in AuxiliaryPrimes do
		if Sf ne {} then
			print "Dealing with q =",q;
			Sq:=RefinedBoundFormF(q,f,p,d);
            if Sq ne {} then
                Sf:=Sf meet Sq;
            end if;
            if Sf ne {} then
                print "Prime ideal(s) remaining to eliminate =",Sf;
            end if;
        end if;
	end for;
	if Sf eq {} then
        print "The form is eliminated";
    else
        print "The form with coefficient field :", CoefficientField(f) ;
        print "is not eliminated for",#Sf,"prime ideal(s) above :", p;
    end if;
	print "*************************************************************";
	return "";
end function;



