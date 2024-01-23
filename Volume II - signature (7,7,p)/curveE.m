/*
    Frey curve E
*/


// The Frey elliptic curve E
function FreyE(a,b)
	a2:=-(a-b)^2;
	a4:=-2*a^4 + a^3*b - 5*a^2*b^2 + a*b^3 -2*b^4;
	a6:=a^6 - 6*a^5*b + 8*a^4*b^2 - 13*a^3*b^3 + 8*a^2*b^4 - 6*a*b^5 + b^6;
	return EllipticCurve([0,a2,0,a4,a6]);
end function;


// This function returns the list of prime ideals P|p for which there is a possible congruence (mod P) between f and the Frey curve E by checking this congruence with the Frobenius elements at a prime q.

function BoundFormE(q,f);
	F:=CoefficientField(f);
	OF:=Integers(F);
	L:={};
	for x,y in [0..q-1] do
  		if [x,y] ne [0,0] then
	    		C:=FreyE(x,y);
			if LocalInformation(C,q)[3] eq 0 then 
				// Here, C has good reduction at q
				diffq:=TraceOfFrobenius(C,q)-Coefficient(f,q);
			else
				// Here C has bad (multiplicative) reduction at q
				diffq:=(q+1)^2-Coefficient(f,q)^2;
			end if;
			if diffq eq 0 then
				return {}; // here p is unbounded
			else
				fact:=Set([I[1] : I in Factorisation(diffq*OF)]); // here p is bounded using congruences for the a_q coefficients
				if fact ne {} then
					L:=L join fact;
				end if;
			end if;
	    end if;
	end for;
	if q eq 3 then
		return L; 
	else
		return L join Set([I[1] : I in Factorisation(q*OF)]);
	end if;
end function;

// Given a space of forms, this function returns the possible surviving forms using the "good" primes q less than 40 using the curve E
function BoundE(forms);
	setofprimes:=[x : x in PrimesUpTo(40) | x notin [2,7] and (x mod 7 ne 1)];
	for i in [1..#forms] do
		f:=forms[i,1];
		Sf:={};
		bool:=0;
  		for q in setofprimes do
		    Sq:=BoundFormE(q,f);
		    if Sq ne {} then
				if bool eq 0 then
					Sf:=Sq;
					bool:=1;
				end if;
			Sf:=Sf meet Sq;
		    end if;
		end for;
		if (Sf eq {}) and (bool eq 0) then
			print "*********************************";
		    print "Form no",i,"is not eliminated !";
	  	else
			survivingprimes:=[P : P in Sf | Characteristic(ResidueClassField(P)) gt 3 and Characteristic(ResidueClassField(P)) ne 7];
			print "*********************************";
			if survivingprimes eq [] then
				print "Form no",i,"eliminated";
			else
				print "Form no",i;
				print "with coefficient field :", CoefficientField(f) ;
				print "not eliminated for the following prime ideals :", survivingprimes;
			end if;
		end if;  
	end for;
    return "";
end function;