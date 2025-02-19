# Darmon's program on generalized Fermat equations
Electronic resources for the series of papers `On Darmon's program for the generalized Fermat equation' vol. I and II by Nicolas Billerey, Imin Chen, Luis Dieulefait, and Nuno Freitas.

Remark: The programs were run using Magma V2.28-9 either on a 2.35/3.35 Ghz 32 core AMD EPYC 7452 machine with 512 Gb from Laboratoire de Mathématiques Blaise Pascal in Université Clermont Auvergne or on a personal computer.

Last modifications: Feb 19, 2025

********************************
Volume I - signature (11,11,p) (<a href="https://arxiv.org/abs/2205.15861">arXiv:2205.15861</a>)
********************************

Theorem 10.1 (= Theorem 1.5 when 2|a+b):  OptimalF11.txt (20 seconds) 

Theorem 1.5 when 2\nmid a+b: OptimalC11.txt (7 hours)


********************************
Volume II - signature (7,7,p) (<a href="https://arxiv.org/abs/2308.07062">arXiv:2308.07062</a>)
********************************

* General library files of functions used by files supporting assertions made in the paper:

curveE.m: Functions related to the Frey elliptic curve E/Q

fieldK.m: Functions related to the cubic field K = Q(zeta7)^+ (and other useful functions)

curveF.m: Functions related to the Frey elliptic curve F/K

curveC.m: Functions related to the Kraus' Frey hyperelliptic curve C and its Jacobian J/K

curveCslow.m: Only basic versions of the functions from the file curveC.m related to the Kraus' Frey hyperelliptic curve C and its Jacobian J/K, i.e. without the improvements explained in §§7.2.2-7.2.4


* Files supporting assertions made in the paper:

irreducibility_rhoF.m: Irreducibility of the mod p representation associated with F

irreducibility_rhoJ.m: Irreducibility of the mod p representation associated with J

first_proof.m: First proof of our main theorem (= Theorem 1.2 from the Introduction on x^7 + y^7 = 3z^p) using only the Frey elliptic curve F/K and its twists (~40 minutes)

first_proof_variant.m: Variant of the first proof of our main theorem using the Frey elliptic curves E/Q and (twists of) F/K (~40 minutes)

second_proof.m: Second proof of our main theorem using C in the case ab even and (twists of) F in the case ab odd (~10 minutes)

second_proofslow.m: Second proof of our main theorem using C in the case ab even and (twists of) F in the case ab odd, but without using the improvements explained in §§7.2.2-7.2.4 (~40 minutes)

third_proof.m: Third (and fastest of all) proof of our main theorem using E, F and C (~1 minute)

second_main.m: Proof of our second main theorem (= Theorem 1.4 from the Introduction on x^7 + y^7 = z^p) using the Frey elliptic curve F/K (and its twists) and C (~9 hours)

For more details on the timings, see output files in the corresponding folder.
