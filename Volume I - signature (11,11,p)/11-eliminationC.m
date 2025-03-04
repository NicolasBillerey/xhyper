/*
    We prove that x^11 + y^11 = z^p has no non-trivial solution with a + b odd and 11 | a + b
    We use the curve C = C_11(a,b)/K.
*/

load "11-fieldK.m";
load "11-curveC.m";


N21:=I2^2*I11;

print "Computing newforms of level Q2^2*Q11. Dimension of the space:", Dimension(NewSubspace(HilbertCuspForms(K,N21)));
forms21:=Eigenforms(NewSubspace(HilbertCuspForms(K,N21)));
print "There are",#forms21,"newforms to eliminate.";
print "\n++++++++++++++++++++++", Realhours();



// we test which forms have coefficient field containing K
print "\nEliminating forms by checking whether K is included in the field of coefficients...";
degForms21:=[];
index:=[];
for i in [1..#forms21] do
	f:=forms21[i];
	F:=BaseField(f);
	degF:=Degree(F);
	bolF:=false;
	if degF mod 5 eq 0 then 
		subsDeg5:=Subfields(F,5);
		for fld in subsDeg5 do
			if IsIsomorphic(K,fld[1]) then bolF:=true; end if;
		end for;
	end if;
	if bolF then 
		Append(~index,i); 
		Append(~degForms21,degF);
	end if;
end for;
print "\n...done!";




print "\nThe forms at level Q2^2*Q11 whose coefficient field contains K are the forms labelled:";
print index; // [ 7, 8, 9, 10, 11, 12 ]

print "\nThe degrees of the coefficient fields of these forms are:\n";
degForms21; // [ 5, 10, 25, 25, 50, 60 ]


print "\n***************************************";
print "Eliminating form 7\n";
f:=forms21[7];
Kf:=BaseField(f);
_,toKf:=IsSubfield(K,Kf);

B3:=BoundFormCTwisted([I3],f,Kf,{},toKf); // { 5, 7 }
//B5:=BoundFormCTwisted([I5],f,Kf,B3,toKf); // { 5, 23, 257 } // {5} (useless)
//B7:=BoundFormCTwisted([I7],f,Kf,B5,toKf); // { 5, 7, 13, 19 } // {5} (useless)
//B13:=BoundFormCTwisted([I13],f,Kf,{},toKf); // (WAY TOO LONG)
B23a:=BoundFormCTwisted([I23a],f,Kf,B3,toKf); // { 23, 43, 109, 353, 5741 } // eliminated!
//B23a:=BoundFormCTwisted([I23a],f,Kf,B5,toKf); // { 23, 43, 109, 353, 5741 } // eliminated! (useless)
print "\n++++++++++++++++++++++", Realhours();


print "\n***************************************";
print "Eliminating form 8\n";
f:=forms21[8];
Kf:=BaseField(f);
_,toKf:=IsSubfield(K,Kf);

B3:=BoundFormCTwisted([I3],f,Kf,{},toKf); // { 17, 37, 53527, 65239 }
B5:=BoundFormCTwisted([I5],f,Kf,B3,toKf); // { 5, 13, 17, 31, 421, 631, 1931, 5081, 7829, 4830689 } // { 17 }
B7:=BoundFormCTwisted([I7],f,Kf,B5,toKf); // { 7, 37, 41, 101, 157, 181, 313, 4967, 7079 } // eliminated!  
print "\n++++++++++++++++++++++", Realhours();


print "\n***************************************";
print "Eliminating form 9\n";
f:=forms21[9];
Kf:=BaseField(f);
_,toKf:=IsSubfield(K,Kf);

B3:=BoundFormCTwisted([I3],f,Kf,{},toKf); // { 5, 23, 43, 757, 1709, 2677, 270270757, 10990417189 }
B5:=BoundFormCTwisted([I5],f,Kf,B3,toKf); // { 5, 47, 53, 241, 523, 1931, 1987, 19237, 233851, 44449079, 2033688239971, 162218814643373 } // { 5 }
//B7:=BoundFormCTwisted([I7],f,Kf,B5,toKf); // { 5, 7, 23, 229, 307, 421, 433, 449, 857, 131009, 2070883, 121340873, 54980564031839, 43482546754887551 } // {5} (useless)
//B13:=BoundFormCTwisted([I13],f,Kf,{},toKf); // (WAY TOO LONG)
B23a:=BoundFormCTwisted([I23a],f,Kf,B5,toKf); // { 23, 43, 67, 307, 419, 683, 1013, 8999, 12101, 24793, 68531, 122167, 285451, 309013, 416239, 4866707, 75340123, 29770032667, 301513381159, 390315071719, 970717147973, 21425345486687, 5456723112767869141561, 228145974957128815675524701 } // eliminated!
print "\n++++++++++++++++++++++", Realhours();


print "\n***************************************";
print "Eliminating form 10\n";
f:=forms21[10];
Kf:=BaseField(f);
_,toKf:=IsSubfield(K,Kf);

B3:=BoundFormCTwisted([I3],f,Kf,{},toKf); // { 5, 7, 13, 17, 59, 227, 29599, 85373917, 855942583 }
//B5:=BoundFormCTwisted([I5],f,Kf,B3,toKf); // { 5, 7, 13, 17, 43, 449, 661, 5051, 13513, 90931, 92033, 120977, 3291391, 29242769, 752783249558563 } // { 5, 7, 13, 17 } (useless)
//B7:=BoundFormCTwisted([I7],f,Kf,B5,toKf); // { 5, 7, 37, 89, 127, 631, 1361, 4861, 25087, 119701, 132361, 1025407, 74831359, 654784799, 31688169263, 35106694619767 } // { 5, 7 } (useless)
//B13:=BoundFormCTwisted([I13],f,Kf,{},toKf); // (WAY TOO LONG)
//B23a:=BoundFormCTwisted([I23a],f,Kf,B7,toKf); // { 23, 43, 89, 109, 263, 593, 617, 1297, 1979, 23209, 45959, 138247, 186889, 239557, 297263, 332903, 625087, 7360231, 13435291, 45196601, 93072407, 564573833, 1244887117, 16526964631, 187179381817, 409859457523, 4680544251213007, 33110159464307617, 214643271041832472012658077 } // eliminated! (enough with B3!)
B23a:=BoundFormCTwisted([I23a],f,Kf,B3,toKf); // // eliminated!
print "\n++++++++++++++++++++++", Realhours();


print "\n***************************************";
print "Eliminating form 11\n";
f:=forms21[11];
Kf:=BaseField(f);
_,toKf:=IsSubfield(K,Kf);
	
B3:=BoundFormCTwisted([I3],f,Kf,{},toKf); // { 991, 2341, 2953, 4621, 19139, 71429, 25232971, 145533061, 5959935857, 7238726353, 17894720017 } 
//B5:=BoundFormCTwisted([I5],f,Kf,B3,toKf); // { 5, 17, 31, 3527, 4621, 14009, 418391, 1129111, 6463463, 10555537, 41517169, 3429376409, 6739064867, 16202105089, 1088557984571, 22341901670929, 8641393760666797243, 1366631292650463614201617 } // { 4621 } (useless)
//B7:=BoundFormCTwisted([I7],f,Kf,B5,toKf);  // { 7, 29, 173, 1783, 40099, 45641, 97813, 124699, 4034399, 39732263, 205510763, 180588750833, 1248015225773, 4713065813843, 74814833910991, 3203198683182063411281, 431420413362311578200204432855221 } // eliminated!
B7:=BoundFormCTwisted([I7],f,Kf,B3,toKf); // // eliminated!
print "\n++++++++++++++++++++++", Realhours();


print "\n***************************************";
print "Eliminating form 12\n";
f:=forms21[12];
Kf:=BaseField(f);
_,toKf:=IsSubfield(K,Kf);

B3:=BoundFormCTwisted([I3],f,Kf,{},toKf); // { 41, 131, 487, 70583, 1590101, 212152939, 433116589, 1369803583, 2404455199, 702034129733, 873294786686194457479 } // 
//B5:=BoundFormCTwisted([I5],f,Kf,B3,toKf); // { 5, 17, 37, 41, 97, 1667, 6827, 7549, 15973, 98669, 591757, 2753693, 337219903, 879492727, 5046853979, 6795133843, 13556666491, 24943381831, 76542697201, 17315694330239, 5507540994926471521, 191364893549173088287900531 } // { 41 } (useless)
//B7:=BoundFormCTwisted([I7],f,Kf,B5,toKf); // { 5, 7, 17, 37, 149, 1303, 2803, 3137, 9739, 15923, 76561, 1443713, 4982833, 2022450641, 98885510491, 60843896460041, 72517849506523, 828651286663621, 1266452975010724859, 9376109106845292191, 279785698569594337074498307064030599 } // eliminated!
B7:=BoundFormCTwisted([I7],f,Kf,B3,toKf); // // eliminated!
print "\n++++++++++++++++++++++", Realhours();
