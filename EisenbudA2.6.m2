--Goal: define a function which takes a map phi: R^f-->R^g with f
--greater than or equal to g and returns a list {C^{-1},C^0,...,C^g} of the
--complexes of length f-g+1 as defined in Eisenbud A2.6.

--Examples in the Toric case on P^1xP^1 with f=4 and g=2

--Example #1
R=ZZ/32003[x_0,x_1,y_0,y_1,Degrees=>{{1,0},{1,0},{0,1},{0,1}}]
phi=map(R^{{2,0},{0,2}},R^4,matrix{{x_0^2,x_0*x_1,x_1^2,0},{0,y_0^2,y_0*y_1,y_1^2}})
isHomogeneous phi
C0= eagonNorthcott phi
--check if C0 is a free resolution
apply(4,i->HH_i C0 ==0)
B=intersect(ideal(x_0,x_1),ideal(y_0,y_1))
I=minors(2,phi)
IB=saturate(I,B)
needsPackage "VirtualResolutions"
isVirtual(B,C0)
--so C0 is a virtual resolution but not a free resolution
--we can also see this by looking at the depth condition
needsPackage "Depth"
depth(I,R)
depth(IB,R)
--note that depth(I)=2 \not\geq f-g+1=3
--but depth(IB)= \infty > 3


--Attempt to build the complexes C^{-1},C^0,...,C^g for the previous example.
F=source phi
G=target phi
S=symmetricAlgebra(G,Degrees=>{{1,0,0},{1,0,0}})
apply(4,i-> e_i=F_i)
apply(4,i-> y_i=(((map(S^1,S^2,matrix{{p_0,p_1}}))(substitute(phi(e_i),S))))_0)
K=koszul(matrix{oo})
K.dd
--now need to figure out how to take the (d,*,*) strands of K
--then need to define the splitting map
--then need to construct the C^i


--Example #2
restart
R=ZZ/32003[x_0,x_1,y_0,y_1,Degrees=>{2:{1,0},2:{0,1}}]
phi=map(R^{{1,0},{0,1}},R^4,matrix{{x_0,0,x_1,0},{0,y_0,0,y_1}})
isHomogeneous phi


--2nd Attempt: Constructing C^i explicitly in general by defining generators of the modules and the matrices
restart
--Define a function that outputs a list of the free modules in C^i by giving
--pairs (a,b) that correspond to the terms S_a \otimes \wedge^b F, where
--S=symmetricAlgebra(G). Recall that C^i: K(phi')^*_{f-g-i} \to K(phi')_i
--and we will let (-a,b) correspond to S^*_a \otimes \wedge^b F.

L1 = (f,g,i)->(apply(i+1,j->{i-j,j}))
L2 = (f,g,i)->(apply(f-g-i+1,j->{-j,f-i+j}))
--Now C^i is built from L1 \epsilon L2 (with maps going right to left)


--3rd Attempt: Constructing C^{-1}, C^0, C^1, C^2, and C^3 explicitly in the 2x4 matrix case
restart

--Function for rings that are Z-graded and maps of linear forms
ComplexesList1 = M -> (
    I := {-1,0,1,2,3};
    apply(I, i-> C_i = new ChainComplex);
    R := ring(M);
    apply(I, i-> C_i.ring = R);
    
    --Define modules for C^(-1)
    apply(4, j-> C_(-1)#j = R^{(binomial(4,j+1)*binomial(1+j,j)):-(j+1)});
    C_(-1)#4 = 0;
    
    --Define maps for C^(-1)
    C_(-1).dd#1 = map(C_(-1)_0,C_(-1)_1,matrix{{M_(0,0), M_(0,1), M_(0,2), M_(0,3), 0, 0, 0, 0, 0, 0, 0, 0}, {M_(1,0), M_(1,1), M_(1,2), M_(1,3), M_(0,0), M_(0,1), M_(0,2), M_(0,3), 0 ,0 ,0 ,0},{0,0,0,0,M_(1,0),M_(1,1), M_(1,2),M_(1,3),M_(0,0),M_(0,1),M_(0,2),M_(0,3)},{0,0,0,0,0,0,0,0,M_(1,0),M_(1,1),M_(1,2),M_(1,3)}});
    C_(-1).dd#2 = map(C_(-1)_1,C_(-1)_2,matrix{{-M_(0,1), -M_(0,2), -M_(0,3),0,0,0,0,0,0,0,0,0}, {M_(0,0), 0, 0, -M_(0,2), -M_(0,3), 0, 0, 0, 0, 0, 0, 0}, {0, M_(0,0), 0, M_(0,1), 0, -M_(0,3), 0,0,0,0,0,0}, {0,0, M_(0,0), 0, M_(0,1), M_(0,2),0,0,0,0,0,0}, {-M_(1,1), -M_(1,2), -M_(1,3), 0,0,0, -M_(0,1), -M_(0,2), -M_(0,3),0,0,0}, {M_(1,0), 0,0, -M_(1,2), -M_(1,3), 0, M_(0,0),0,0,-M_(0,2), -M_(0,3),0}, {0, M_(1,0), 0, M_(1,1), 0, -M_(1,3), 0, M_(0,0), 0, M_(0,1), 0, -M_(0,3)}, {0,0, M_(1,0), 0, M_(1,1), M_(1,2),0,0, M_(0,0), 0,M_(0,1), M_(0,2)}, {0,0,0,0,0,0, -M_(1,1), -M_(1,2), -M_(1,3), 0,0,0}, {0,0,0,0,0,0,M_(1,0),0,0,-M_(1,2), -M_(1,3),0}, {0,0,0,0,0,0,0,M_(1,0),0,M_(1,1),0,-M_(1,3)}, {0,0,0,0,0,0,0,0,M_(1,0),0,M_(1,1),M_(1,2)}});
    C_(-1).dd#3 = map(C_(-1)_2,C_(-1)_3,matrix{{M_(0,2), M_(0,3), 0,0}, {-M_(0,1), 0, M_(0,3),0}, {0, -M_(0,1), -M_(0,2), 0}, {M_(0,0),0,0, M_(0,3)}, {0, M_(0,0), 0 , M_(0,2)} ,{0,0, M_(0,0), M_(0,1)} ,{M_(1,2), M_(1,3),0,0} ,{-M_(1,1), 0, M_(1,3),0} , {0,-M_(1,1), -M_(1,2), 0} ,{M_(1,0),0,0, M_(1,3)}, {0, M_(1,0), 0, M_(1,2)} ,{0,0, M_(1,0), M_(1,1)}});
    
    --Define modules for C^0
    C_0#0 = R^1;
    apply({1,2,3}, j-> C_0#j = R^{(binomial(4,j+1)*binomial(j,j-1)):-(j+1)});
    C_0#4 = 0;
    
    --Define maps for C^0
    (C_0).dd#1 = map(C_0_0,C_0_1,matrix{{M_(0,0)*M_(1,1)-M_(1,0)*M_(0,1), M_(0,0)*M_(1,2)-M_(1,0)*M_(0,2), M_(0,0)*M_(1,3)-M_(1,0)*M_(0,3), M_(0,1)*M_(1,2)-M_(1,1)*M_(0,2), M_(0,1)*M_(1,3)-M_(1,1)*M_(0,3), M_(0,2)*M_(1,3)-M_(1,2)*M_(0,3)}});
    (C_0).dd#2 = map(C_0_1,C_0_2,matrix{{M_(0,2),M_(0,3),0,0,M_(1,2),M_(1,3),0,0},{-M_(0,1),0,M_(0,3),0,-M_(1,1),0,M_(1,3),0},{0,-M_(0,1),-M_(0,2),0,0,-M_(1,1),-M_(1,2),0},{M_(0,0),0,0,M_(0,3),M_(1,0),0,0,M_(1,3)},{0,M_(0,0),0,-M_(0,2),0,M_(1,0),0,-M_(1,2)},{0,0,M_(0,0),M_(0,1),0,0,M_(1,0),M_(1,1)}});
    (C_0).dd#3 = map(C_0_2,C_0_3,matrix{{-M_(0,3),-M_(1,3),0},{M_(0,2),M_(1,2),0},{-M_(0,1),-M_(1,1),0},{M_(0,0),M_(1,0),0},{0,-M_(0,3),-M_(1,3)},{0,M_(0,2),M_(1,2)},{0,-M_(0,1),-M_(1,1)},{0,M_(0,0),M_(1,0)}});
    
    --Define modules for C^1
    C_1#0 = R^2;
    C_1#1 = R^{4:-1};
    C_1#2 = R^{4:-3};
    C_1#3 = R^{2:-4};
    C_1#4 = 0;
    
    --Define maps for C^1
    (C_1).dd#1 = map(C_1_0,C_1_1,M);
    (C_1).dd#2 = map(C_1_1,C_1_2,matrix{{M_(0,1)*M_(1,2)-M_(1,1)*M_(0,2), M_(0,1)*M_(1,3)-M_(1,1)*M_(0,3), M_(0,2)*M_(1,3)-M_(1,2)*M_(0,3),0},{-M_(0,0)*M_(1,2)+M_(1,0)*M_(0,2), -M_(0,0)*M_(1,3)+M_(1,0)*M_(0,3),0,M_(0,2)*M_(1,3)-M_(1,2)*M_(0,3)},{M_(0,0)*M_(1,1)-M_(1,0)*M_(0,1),0,-M_(0,0)*M_(1,3)+M_(1,0)*M_(0,3), -M_(0,1)*M_(1,3)+M_(1,1)*M_(0,3)},{0,M_(0,0)*M_(1,1)-M_(1,0)*M_(0,1), M_(0,0)*M_(1,2)-M_(1,0)*M_(0,2), M_(0,1)*M_(1,2)-M_(1,1)*M_(0,2)}});
    (C_1).dd#3 = map(C_1_2,C_1_3,matrix{{-M_(0,3),-M_(1,3)},{M_(0,2),M_(1,2)},{-M_(0,1),-M_(1,1)},{M_(0,0),M_(1,0)}});
    
    --Define modules for C^2
    C_2#0 = R^3;
    C_2#1 = R^{8:-1};
    C_2#2 = R^{6:-2};
    C_2#3 = R^{1:-4};
    C_2#4 = 0;
   	 
    --Define maps for C^2
    (C_2).dd#1 = map(C_2_0,C_2_1,matrix{{M_(0,0),M_(0,1),M_(0,2),M_(0,3),0,0,0,0},{M_(1,0),M_(1,1),M_(1,2),M_(1,3),M_(0,0),M_(0,1),M_(0,2),M_(0,3)},{0,0,0,0,M_(1,0),M_(1,1),M_(1,2),M_(1,3)}});
    (C_2).dd#2 = map(C_2_1,C_2_2,matrix{{-M_(0,1),-M_(0,2),-M_(0,3),0,0,0},{M_(0,0),0,0,-M_(0,2),-M_(0,3),0},{0,M_(0,0),0,M_(0,1),0,-M_(0,3)},{0,0,M_(0,0),0,M_(0,1),M_(0,2)},{-M_(1,1),-M_(1,2),-M_(1,3),0,0,0},{M_(1,0),0,0,-M_(1,2),-M_(1,3),0},{0,M_(1,0),0,M_(1,1),0,-M_(1,3)},{0,0,M_(1,0),0,M_(1,1),M_(1,2)}});
    (C_2).dd#3 = map(C_2_2,C_2_3,matrix{{M_(0,2)*M_(1,3)-M_(1,2)*M_(0,3)},{-M_(0,1)*M_(1,3)+M_(1,1)*M_(0,3)},{M_(0,1)*M_(1,2)-M_(1,1)*M_(0,2)},{M_(0,0)*M_(1,3)-M_(1,0)*M_(0,3)},{-M_(0,0)*M_(1,2)+M_(1,0)*M_(0,2)},{M_(0,0)*M_(1,1)-M_(0,1)*M_(1,0)}});
    
    --Define modules for C^3
    apply(4, j-> C_3#j = R^{(binomial(4,j+1)*binomial(1+j,j)):-(j+1)});
    C_3#4 = 0;
    
    --Define maps for C^3
    (C_3).dd#1 = map(C_3_0,C_3_1,matrix{{M_(0,1), M_(0,2), M_(0,3), 0,0, 0, M_(1,1), M_(1,2), M_(1,3), 0,0,0}, {-M_(0,0), 0,0, M_(0,2), M_(0,3), 0, -M_(1,0), 0, 0, M_(1,2), M_(1,3),0}, {0, -M_(0,0), 0, -M_(0,1), 0, M_(0,3), 0, -M_(1,0), 0, -M_(1,1), 0, M_(1,3)}, {0,0, -M_(0,0), 0 ,-M_(0,1), -M_(0,2), 0,0, -M_(1,0), 0,-M_(1,1),-M_(1,2)}});
    (C_3).dd#2 = map(C_3_1,C_3_2,matrix{{M_(0,2), M_(0,3), 0,0,M_(1,2), M_(1,3), 0,0,0,0,0,0}, {-M_(0,1), 0, M_(0,3), 0, -M_(1,1), 0, M_(1,3), 0,0,0,0,0}, {0,-M_(0,1), -M_(0,2), 0,0, -M_(1,1), -M_(1,2), 0,0,0,0,0}, {M_(0,0), 0,0,M_(0,3),M_(1,0),0,0,M_(1,3),0,0,0,0},{0, M_(0,0),0,-M_(0,2),0,M_(1,0),0,-M_(1,2),0,0,0,0}, {0,0,M_(0,0), M_(0,1),0,0,M_(1,0),M_(1,1),0,0,0,0}, {0,0,0,0,-M_(0,2), -M_(0,3),0,0,M_(1,2),M_(1,3),0,0}, {0,0,0,0,M_(0,1),0,-M_(0,3),0,-M_(1,1),0,M_(1,3),0}, {0,0,0,0,0,M_(0,1),M_(0,2),0,0,-M_(1,1),-M_(1,2),0}, {0,0,0,0,-M_(0,0),0,0,-M_(0,3),M_(1,0),0,0,M_(1,3)}, {0,0,0,0,0,-M_(0,0), 0, M_(0,2), 0, M_(1,0), 0, -M_(1,2)}, {0,0,0,0,0,0,-M_(0,0), -M_(0,1),0,0,M_(1,0), M_(1,1)}});
    (C_3).dd#3 = map(C_3_2,C_3_3,matrix{{-M_(0,3),-M_(1,3),0,0}, {M_(0,2),M_(1,2),0,0}, {-M_(0,1),-M_(1,1),0,0}, {M_(0,0),M_(1,0),0,0}, {0,-M_(0,3),-M_(1,3),0}, {0,M_(0,2),M_(1,2),0} ,{0,-M_(0,1),-M_(1,1),0}, {0,M_(0,0),M_(1,0), 0}, {0,0, -M_(0,3), -M_(1,3)}, {0,0,M_(0,2),M_(1,2)}, {0,0,-M_(0,1),-M_(1,1)}, {0,0,M_(0,0),M_(1,0)}});
    
    return {C_(-1),C_0,C_1,C_2,C_3};)

--Function for rings that are Multigraded--------------------------------------------------------------------------------------------------------------------------
--This function works for any homogeneous 2x4 map between multigraded rings where all of the entries have the same degree.

needsPackage "TensorComplexes"

ComplexesList2 = M -> (
    I := {-1,0,1,2,3};
    apply(I, i-> C_i = new ChainComplex);
    R := ring(M);
    apply(I, i-> C_i.ring = R);
    
    Rows := degrees target M;
    Columns := degrees source M;
    deg := (rsort(Columns))_0;
    
    --Define modules for C^(-1)
    apply(4, j-> C_(-1)#j = R^{(binomial(4,j+1)*binomial(1+j,j)):-(j+1)*deg});
    C_(-1)#4 = 0;
    
    --Define maps for C^(-1)
    C_(-1).dd#1 = map(C_(-1)_0,C_(-1)_1,matrix{{M_(0,0), M_(0,1), M_(0,2), M_(0,3), 0, 0, 0, 0, 0, 0, 0, 0}, {M_(1,0), M_(1,1), M_(1,2), M_(1,3), M_(0,0), M_(0,1), M_(0,2), M_(0,3), 0 ,0 ,0 ,0},{0,0,0,0,M_(1,0),M_(1,1), M_(1,2),M_(1,3),M_(0,0),M_(0,1),M_(0,2),M_(0,3)},{0,0,0,0,0,0,0,0,M_(1,0),M_(1,1),M_(1,2),M_(1,3)}});
    C_(-1).dd#2 = map(C_(-1)_1,C_(-1)_2,matrix{{-M_(0,1), -M_(0,2), -M_(0,3),0,0,0,0,0,0,0,0,0}, {M_(0,0), 0, 0, -M_(0,2), -M_(0,3), 0, 0, 0, 0, 0, 0, 0}, {0, M_(0,0), 0, M_(0,1), 0, -M_(0,3), 0,0,0,0,0,0}, {0,0, M_(0,0), 0, M_(0,1), M_(0,2),0,0,0,0,0,0}, {-M_(1,1), -M_(1,2), -M_(1,3), 0,0,0, -M_(0,1), -M_(0,2), -M_(0,3),0,0,0}, {M_(1,0), 0,0, -M_(1,2), -M_(1,3), 0, M_(0,0),0,0,-M_(0,2), -M_(0,3),0}, {0, M_(1,0), 0, M_(1,1), 0, -M_(1,3), 0, M_(0,0), 0, M_(0,1), 0, -M_(0,3)}, {0,0, M_(1,0), 0, M_(1,1), M_(1,2),0,0, M_(0,0), 0,M_(0,1), M_(0,2)}, {0,0,0,0,0,0, -M_(1,1), -M_(1,2), -M_(1,3), 0,0,0}, {0,0,0,0,0,0,M_(1,0),0,0,-M_(1,2), -M_(1,3),0}, {0,0,0,0,0,0,0,M_(1,0),0,M_(1,1),0,-M_(1,3)}, {0,0,0,0,0,0,0,0,M_(1,0),0,M_(1,1),M_(1,2)}});
    C_(-1).dd#3 = map(C_(-1)_2,C_(-1)_3,matrix{{M_(0,2), M_(0,3), 0,0}, {-M_(0,1), 0, M_(0,3),0}, {0, -M_(0,1), -M_(0,2), 0}, {M_(0,0),0,0, M_(0,3)}, {0, M_(0,0), 0 , M_(0,2)} ,{0,0, M_(0,0), M_(0,1)} ,{M_(1,2), M_(1,3),0,0} ,{-M_(1,1), 0, M_(1,3),0} , {0,-M_(1,1), -M_(1,2), 0} ,{M_(1,0),0,0, M_(1,3)}, {0, M_(1,0), 0, M_(1,2)} ,{0,0, M_(1,0), M_(1,1)}});
    
    --Define modules for C^0
    C_0#0 = R^1;
    C_0#1 = R^{6:-2*deg};
    C_0#2 = R^{8:-3*deg};
    C_0#3 = R^{3:-4*deg};
    --Cmoddegs = apply({1,2,3},j->(
	    --if j==1 then apply(subsets(Columns,j+1),L-> (sum L-degree(M_(0,0)*M_(1,1)-M_(0,1)*M_(1,0)))) else (
	   --flatten apply(multiSubsets(Rows,j-1),L'->(apply(subsets(Columns,j+1),L->(sum L-degree(M_(0,0)*M_(1,1)-M_(0,1)*M_(1,0))+sum L')))))
	    --));
    
    --apply({1,2,3}, j-> C_0#j = R^(Cmoddegs_(j-1)));
    C_0#4 = 0;
    
    --Define maps for C^0
    (C_0).dd#1 = map(C_0_0,C_0_1,matrix{{M_(0,0)*M_(1,1)-M_(1,0)*M_(0,1), M_(0,0)*M_(1,2)-M_(1,0)*M_(0,2), M_(0,0)*M_(1,3)-M_(1,0)*M_(0,3), M_(0,1)*M_(1,2)-M_(1,1)*M_(0,2), M_(0,1)*M_(1,3)-M_(1,1)*M_(0,3), M_(0,2)*M_(1,3)-M_(1,2)*M_(0,3)}});
    (C_0).dd#2 = map(C_0_1,C_0_2,matrix{{M_(0,2),M_(0,3),0,0,M_(1,2),M_(1,3),0,0},{-M_(0,1),0,M_(0,3),0,-M_(1,1),0,M_(1,3),0},{0,-M_(0,1),-M_(0,2),0,0,-M_(1,1),-M_(1,2),0},{M_(0,0),0,0,M_(0,3),M_(1,0),0,0,M_(1,3)},{0,M_(0,0),0,-M_(0,2),0,M_(1,0),0,-M_(1,2)},{0,0,M_(0,0),M_(0,1),0,0,M_(1,0),M_(1,1)}});
    (C_0).dd#3 = map(C_0_2,C_0_3,matrix{{-M_(0,3),-M_(1,3),0},{M_(0,2),M_(1,2),0},{-M_(0,1),-M_(1,1),0},{M_(0,0),M_(1,0),0},{0,-M_(0,3),-M_(1,3)},{0,M_(0,2),M_(1,2)},{0,-M_(0,1),-M_(1,1)},{0,M_(0,0),M_(1,0)}});
    
    --Define modules for C^1
    --still need to do
    C_1#0 = R^2;
    C_1#1 = R^(-Columns);
    C_1#2 = R^(-3*Columns);
    C_1#3 = R^{2:-4*deg};
    C_1#4 = 0;
    
    --Define maps for C^1
    (C_1).dd#1 = map(C_1_0,C_1_1,M);
    (C_1).dd#2 = map(C_1_1,C_1_2,matrix{{M_(0,1)*M_(1,2)-M_(1,1)*M_(0,2), M_(0,1)*M_(1,3)-M_(1,1)*M_(0,3), M_(0,2)*M_(1,3)-M_(1,2)*M_(0,3),0},{-M_(0,0)*M_(1,2)+M_(1,0)*M_(0,2), -M_(0,0)*M_(1,3)+M_(1,0)*M_(0,3),0,M_(0,2)*M_(1,3)-M_(1,2)*M_(0,3)},{M_(0,0)*M_(1,1)-M_(1,0)*M_(0,1),0,-M_(0,0)*M_(1,3)+M_(1,0)*M_(0,3), -M_(0,1)*M_(1,3)+M_(1,1)*M_(0,3)},{0,M_(0,0)*M_(1,1)-M_(1,0)*M_(0,1), M_(0,0)*M_(1,2)-M_(1,0)*M_(0,2), M_(0,1)*M_(1,2)-M_(1,1)*M_(0,2)}});
    (C_1).dd#3 = map(C_1_2,C_1_3,matrix{{-M_(0,3),-M_(1,3)},{M_(0,2),M_(1,2)},{-M_(0,1),-M_(1,1)},{M_(0,0),M_(1,0)}});
    
    --Define modules for C^2
    --still need to do
    C_2#0 = R^3;
    C_2#1 = R^{8:-deg};
    C_2#2 = R^{6:-2*deg};
    C_2#3 = R^{1:-4*deg};
    C_2#4 = 0;
   	 
    --Define maps for C^2
    (C_2).dd#1 = map(C_2_0,C_2_1,matrix{{M_(0,0),M_(0,1),M_(0,2),M_(0,3),0,0,0,0},{M_(1,0),M_(1,1),M_(1,2),M_(1,3),M_(0,0),M_(0,1),M_(0,2),M_(0,3)},{0,0,0,0,M_(1,0),M_(1,1),M_(1,2),M_(1,3)}});
    (C_2).dd#2 = map(C_2_1,C_2_2,matrix{{-M_(0,1),-M_(0,2),-M_(0,3),0,0,0},{M_(0,0),0,0,-M_(0,2),-M_(0,3),0},{0,M_(0,0),0,M_(0,1),0,-M_(0,3)},{0,0,M_(0,0),0,M_(0,1),M_(0,2)},{-M_(1,1),-M_(1,2),-M_(1,3),0,0,0},{M_(1,0),0,0,-M_(1,2),-M_(1,3),0},{0,M_(1,0),0,M_(1,1),0,-M_(1,3)},{0,0,M_(1,0),0,M_(1,1),M_(1,2)}});
    (C_2).dd#3 = map(C_2_2,C_2_3,matrix{{M_(0,2)*M_(1,3)-M_(1,2)*M_(0,3)},{-M_(0,1)*M_(1,3)+M_(1,1)*M_(0,3)},{M_(0,1)*M_(1,2)-M_(1,1)*M_(0,2)},{M_(0,0)*M_(1,3)-M_(1,0)*M_(0,3)},{-M_(0,0)*M_(1,2)+M_(1,0)*M_(0,2)},{M_(0,0)*M_(1,1)-M_(0,1)*M_(1,0)}});
    
    --Define modules for C^3
    --still need to do
    apply(4, j-> C_3#j = R^{(binomial(4,j+1)*binomial(1+j,j)):-j*deg});
    C_3#4 = 0;
    
    --Define maps for C^3
    (C_3).dd#1 = map(C_3_0,C_3_1,matrix{{M_(0,1), M_(0,2), M_(0,3), 0,0, 0, M_(1,1), M_(1,2), M_(1,3), 0,0,0}, {-M_(0,0), 0,0, M_(0,2), M_(0,3), 0, -M_(1,0), 0, 0, M_(1,2), M_(1,3),0}, {0, -M_(0,0), 0, -M_(0,1), 0, M_(0,3), 0, -M_(1,0), 0, -M_(1,1), 0, M_(1,3)}, {0,0, -M_(0,0), 0 ,-M_(0,1), -M_(0,2), 0,0, -M_(1,0), 0,-M_(1,1),-M_(1,2)}});
    (C_3).dd#2 = map(C_3_1,C_3_2,matrix{{M_(0,2), M_(0,3), 0,0,M_(1,2), M_(1,3), 0,0,0,0,0,0}, {-M_(0,1), 0, M_(0,3), 0, -M_(1,1), 0, M_(1,3), 0,0,0,0,0}, {0,-M_(0,1), -M_(0,2), 0,0, -M_(1,1), -M_(1,2), 0,0,0,0,0}, {M_(0,0), 0,0,M_(0,3),M_(1,0),0,0,M_(1,3),0,0,0,0},{0, M_(0,0),0,-M_(0,2),0,M_(1,0),0,-M_(1,2),0,0,0,0}, {0,0,M_(0,0), M_(0,1),0,0,M_(1,0),M_(1,1),0,0,0,0}, {0,0,0,0,-M_(0,2), -M_(0,3),0,0,M_(1,2),M_(1,3),0,0}, {0,0,0,0,M_(0,1),0,-M_(0,3),0,-M_(1,1),0,M_(1,3),0}, {0,0,0,0,0,M_(0,1),M_(0,2),0,0,-M_(1,1),-M_(1,2),0}, {0,0,0,0,-M_(0,0),0,0,-M_(0,3),M_(1,0),0,0,M_(1,3)}, {0,0,0,0,0,-M_(0,0), 0, M_(0,2), 0, M_(1,0), 0, -M_(1,2)}, {0,0,0,0,0,0,-M_(0,0), -M_(0,1),0,0,M_(1,0), M_(1,1)}});
    (C_3).dd#3 = map(C_3_2,C_3_3,matrix{{-M_(0,3),-M_(1,3),0,0}, {M_(0,2),M_(1,2),0,0}, {-M_(0,1),-M_(1,1),0,0}, {M_(0,0),M_(1,0),0,0}, {0,-M_(0,3),-M_(1,3),0}, {0,M_(0,2),M_(1,2),0} ,{0,-M_(0,1),-M_(1,1),0}, {0,M_(0,0),M_(1,0), 0}, {0,0, -M_(0,3), -M_(1,3)}, {0,0,M_(0,2),M_(1,2)}, {0,0,-M_(0,1),-M_(1,1)}, {0,0,M_(0,0),M_(1,0)}});
    
    return {C_(-1),C_0,C_1,C_2,C_3};)


---------------------------------- This function is trying to correct a mistake above about calculating the degrees.-----------------------------------------------------
---------------------------------------- It should now work for any homogeneous 2x4 map.


------Below function has degrees fixed so that C_0#0 is S(0,0) (basically twisted every module in the complexes by sum Rows). --------------------

needsPackage "TensorComplexes"

ComplexesList3 = M -> (
    I := {-1,0,1,2,3};
    apply(I, i-> C_i = new ChainComplex);
    R := ring(M);
    apply(I, i-> C_i.ring = R);
    
    Rows := degrees target M;
    Columns := degrees source M;
    
    --Define modules for C^(-1)
    C_(-1)#0 = R^(apply(4, i-> -((Columns)_i- sum Rows)));

    Cmoddegs := apply({1,2,3}, j -> ( flatten apply(multiSubsets(Rows, j), L' -> (apply(subsets(Columns, j+1), L-> (sum L - sum L'-sum Rows))))));
    apply({1,2,3}, j-> C_(-1)#j = R^(-Cmoddegs_(j-1)));
   
    C_(-1)#4 = 0;
    
    --Define maps for C^(-1) = K(M')^*_3
    C_(-1).dd#1 = map(C_(-1)_0,C_(-1)_1,matrix{{M_(0,1), M_(0,2), 0, M_(0,3), 0, 0, M_(1,1), M_(1,2), 0, M_(1,3), 0, 0}, {-M_(0,0), 0, M_(0,2), 0, M_(0,3), 0, -M_(1,0), 0, M_(1,2), 0, M_(1,3), 0},{0,-M_(0,0), -M_(0,1), 0, 0, M_(0,3), 0, -M_(1,0), -M_(1,1), 0, 0, M_(1,3)},{0,0,0,-M_(0,0),-M_(0,1),-M_(0,2),0,0,0,-M_(1,0),-M_(1,1),-M_(1,2)}});
    C_(-1).dd#2 = map(C_(-1)_1,C_(-1)_2,matrix{{M_(0,2), M_(0,3), 0, 0, M_(1,2), M_(1,3), 0,0,0,0,0,0}, {-M_(0,1), 0, M_(0,3), 0, -M_(1,1), 0, M_(1,3), 0,0,0,0,0},{M_(0,0),0,0,M_(0,3),M_(1,0),0,0,M_(1,3),0,0,0,0}, {0,-M_(0,1),-M_(0,2),0,0,-M_(1,1),-M_(1,2),0,0,0,0,0},{0,M_(0,0),0,-M_(0,2),0,M_(1,0),0,-M_(1,2),0,0,0,0}, {0,0,M_(0,0), M_(0,1),0,0,M_(1,0),M_(1,1),0,0,0,0}, {0,0,0,0,-M_(0,2), -M_(0,3),0,0,M_(1,2),M_(1,3),0,0}, {0,0,0,0,M_(0,1),0,-M_(0,3),0,-M_(1,1),0,M_(1,3),0},{0,0,0,0,-M_(0,0),0,0,-M_(0,3),M_(1,0),0,0,M_(1,3)},{0,0,0,0,0,M_(0,1),M_(0,2),0,0,-M_(1,1),-M_(1,2),0}, {0,0,0,0,0,-M_(0,0), 0, M_(0,2), 0, M_(1,0), 0, -M_(1,2)}, {0,0,0,0,0,0,-M_(0,0),-M_(0,1),0,0,M_(1,0), M_(1,1)}});
    C_(-1).dd#3 = map(C_(-1)_2,C_(-1)_3,matrix{{-M_(0,3),-M_(1,3),0,0}, {M_(0,2),M_(1,2),0,0}, {-M_(0,1),-M_(1,1),0,0}, {M_(0,0),M_(1,0),0,0}, {0,-M_(0,3),-M_(1,3),0}, {0,M_(0,2),M_(1,2),0} ,{0,-M_(0,1),-M_(1,1),0}, {0,M_(0,0),M_(1,0), 0}, {0,0, -M_(0,3), -M_(1,3)}, {0,0,M_(0,2),M_(1,2)}, {0,0,-M_(0,1),-M_(1,1)}, {0,0,M_(0,0),M_(1,0)}});
    
    --Define modules for C^0
    C_0#0 = R^1;
    C_0#1 = R^(apply(subsets(Columns,2),L-> -(sum L-sum Rows)));
    Cmoddegs0 := apply({2,3},j-> flatten apply(multiSubsets(Rows,j-1),L'-> apply(subsets(Columns,j+1),L-> (sum L-sum L'-sum Rows))));
    
    apply({2,3}, j-> C_0#j = R^(-Cmoddegs0_(j-2)));
    C_0#4 = 0;
    
    --Define maps for C^0 = K(M')^*_2 -> K(M')_0
    (C_0).dd#1 = map(C_0_0,C_0_1,matrix{{M_(0,0)*M_(1,1)-M_(1,0)*M_(0,1), M_(0,0)*M_(1,2)-M_(1,0)*M_(0,2), M_(0,1)*M_(1,2)-M_(1,1)*M_(0,2), M_(0,0)*M_(1,3)-M_(1,0)*M_(0,3), M_(0,1)*M_(1,3)-M_(1,1)*M_(0,3), M_(0,2)*M_(1,3)-M_(1,2)*M_(0,3)}});
    (C_0).dd#2 = map(C_0_1,C_0_2,matrix{{M_(0,2),M_(0,3),0,0,M_(1,2),M_(1,3),0,0},{-M_(0,1),0,M_(0,3),0,-M_(1,1),0,M_(1,3),0},{M_(0,0),0,0,M_(0,3),M_(1,0),0,0,M_(1,3)},{0,-M_(0,1),-M_(0,2),0,0,-M_(1,1),-M_(1,2),0},{0,M_(0,0),0,-M_(0,2),0,M_(1,0),0,-M_(1,2)},{0,0,M_(0,0),M_(0,1),0,0,M_(1,0),M_(1,1)}});
    (C_0).dd#3 = map(C_0_2,C_0_3,matrix{{-M_(0,3),-M_(1,3),0},{M_(0,2),M_(1,2),0},{-M_(0,1),-M_(1,1),0},{M_(0,0),M_(1,0),0},{0,-M_(0,3),-M_(1,3)},{0,M_(0,2),M_(1,2)},{0,-M_(0,1),-M_(1,1)},{0,M_(0,0),M_(1,0)}});
    
    --Define modules for C^1
    C_1#0 = R^(apply(subsets(Rows,1), L -> -(sum L)));
    C_1#1 = R^(apply(subsets(Columns,1), L -> -(sum L)));
    C_1#2 = R^(apply(subsets(Columns,3), L -> -(sum L-sum Rows)));
    C_1#3 = R^(flatten apply(multiSubsets(Rows,1), L-> (apply(subsets(Columns,4), L' -> -(sum L' - sum L-sum Rows)))));
    C_1#4 = 0;
    
    --Define maps for C^1 = K(M')^*_1 -> K(M')_1
    (C_1).dd#1 = map(C_1_0,C_1_1,M);
    (C_1).dd#2 = map(C_1_1,C_1_2,matrix{{M_(0,1)*M_(1,2)-M_(1,1)*M_(0,2), M_(0,1)*M_(1,3)-M_(1,1)*M_(0,3), M_(0,2)*M_(1,3)-M_(1,2)*M_(0,3),0},{-M_(0,0)*M_(1,2)+M_(1,0)*M_(0,2), -M_(0,0)*M_(1,3)+M_(1,0)*M_(0,3),0,M_(0,2)*M_(1,3)-M_(1,2)*M_(0,3)},{M_(0,0)*M_(1,1)-M_(1,0)*M_(0,1),0,-M_(0,0)*M_(1,3)+M_(1,0)*M_(0,3), -M_(0,1)*M_(1,3)+M_(1,1)*M_(0,3)},{0,M_(0,0)*M_(1,1)-M_(1,0)*M_(0,1), M_(0,0)*M_(1,2)-M_(1,0)*M_(0,2), M_(0,1)*M_(1,2)-M_(1,1)*M_(0,2)}});
    (C_1).dd#3 = map(C_1_2,C_1_3,matrix{{-M_(0,3),-M_(1,3)},{M_(0,2),M_(1,2)},{-M_(0,1),-M_(1,1)},{M_(0,0),M_(1,0)}});
    
    --Define modules for C^2
    C_2#0 = R^(apply(multiSubsets(Rows, 2), L-> -(sum L-sum Rows)));
    C_2#1 = R^(flatten apply(multiSubsets(Rows, 1), L'-> apply(subsets(Columns,1), L-> -(sum L + sum L'-sum Rows))));
    C_2#2 = R^(apply(subsets(Columns,2), L-> -(sum L-sum Rows)));
    C_2#3 = R^{-(sum Columns-sum Rows-sum Rows)};
    C_2#4 = 0;
   	 
    --Define maps for C^2 = K(M')^*_0 -> K(M')_2
    (C_2).dd#1 = map(C_2_0,C_2_1,matrix{{M_(0,0),M_(0,1),M_(0,2),M_(0,3),0,0,0,0},{M_(1,0),M_(1,1),M_(1,2),M_(1,3),M_(0,0),M_(0,1),M_(0,2),M_(0,3)},{0,0,0,0,M_(1,0),M_(1,1),M_(1,2),M_(1,3)}});
    (C_2).dd#2 = map(C_2_1,C_2_2,matrix{{-M_(0,1),-M_(0,2),0,-M_(0,3),0,0},{M_(0,0),0,-M_(0,2),0,-M_(0,3),0},{0,M_(0,0),M_(0,1),0,0,-M_(0,3)},{0,0,0,M_(0,0),M_(0,1),M_(0,2)},{-M_(1,1),-M_(1,2),0,-M_(1,3),0,0},{M_(1,0),0,-M_(1,2),0,-M_(1,3),0},{0,M_(1,0),M_(1,1),0,0,-M_(1,3)},{0,0,0,M_(1,0),M_(1,1),M_(1,2)}});
    (C_2).dd#3 = map(C_2_2,C_2_3,matrix{{M_(0,2)*M_(1,3)-M_(1,2)*M_(0,3)},{-M_(0,1)*M_(1,3)+M_(1,1)*M_(0,3)},{M_(0,0)*M_(1,3)-M_(1,0)*M_(0,3)},{M_(0,1)*M_(1,2)-M_(1,1)*M_(0,2)},{-M_(0,0)*M_(1,2)+M_(1,0)*M_(0,2)},{M_(0,0)*M_(1,1)-M_(0,1)*M_(1,0)}});
    
    --Define modules for C^3
    C_3#0 = R^(apply(multiSubsets(Rows,3), L-> -(sum L-sum Rows)));
    Cmoddegs3 := apply({1,2},j-> flatten apply(multiSubsets(Rows,3-j), L'-> apply(subsets(Columns,j), L-> (sum L + sum L'-sum Rows))));
    apply({1,2}, j-> C_3#j = R^(-Cmoddegs3_(j-1)));
    C_3#3 = R^(apply(subsets(Columns,3), L-> -(sum L-sum Rows)));
    C_3#4 = 0;
    
    --Define maps for C^3 = K(M')_3
    (C_3).dd#1 = map(C_3_0,C_3_1,matrix{{M_(0,0), M_(0,1), M_(0,2),M_(0,3), 0,0, 0, 0,0,0,0,0}, {M_(1,0),M_(1,1), M_(1,2),M_(1,3), M_(0,0), M_(0,1), M_(0,2), M_(0,3),0,0,0,0},{0,0,0,0,M_(1,0),M_(1,1),M_(1,2),M_(1,3),M_(0,0),M_(0,1),M_(0,2),M_(0,3)},{0,0,0,0,0,0,0,0,M_(1,0),M_(1,1),M_(1,2),M_(1,3)}});
    (C_3).dd#2 = map(C_3_1,C_3_2,matrix{{-M_(0,1), -M_(0,2), 0,-M_(0,3),0,0,0,0,0,0,0,0}, {M_(0,0), 0, -M_(0,2), 0, -M_(0,3), 0, 0, 0, 0, 0, 0, 0}, {0, M_(0,0), M_(0,1), 0, 0, -M_(0,3), 0,0,0,0,0,0}, {0,0,0, M_(0,0), M_(0,1), M_(0,2),0,0,0,0,0,0}, {-M_(1,1), -M_(1,2), 0, -M_(1,3),0,0, -M_(0,1), -M_(0,2), 0,-M_(0,3),0,0}, {M_(1,0), 0, -M_(1,2), 0, -M_(1,3), 0, M_(0,0),0,-M_(0,2),0,-M_(0,3),0}, {0, M_(1,0), M_(1,1),0, 0, -M_(1,3), 0, M_(0,0), M_(0,1),0, 0, -M_(0,3)}, {0,0, 0,M_(1,0), M_(1,1), M_(1,2),0,0,0, M_(0,0),M_(0,1), M_(0,2)}, {0,0,0,0,0,0, -M_(1,1), -M_(1,2),0, -M_(1,3),0,0}, {0,0,0,0,0,0,M_(1,0),0,-M_(1,2),0, -M_(1,3),0}, {0,0,0,0,0,0,0,M_(1,0),M_(1,1),0,0,-M_(1,3)}, {0,0,0,0,0,0,0,0,0,M_(1,0),M_(1,1),M_(1,2)}});
    (C_3).dd#3 = map(C_3_2,C_3_3,matrix{{M_(0,2), M_(0,3), 0,0}, {-M_(0,1), 0, M_(0,3),0},{M_(0,0),0,0, M_(0,3)}, {0, -M_(0,1), -M_(0,2), 0},{0, M_(0,0), 0 , M_(0,2)} ,{0,0, M_(0,0), M_(0,1)} ,{M_(1,2), M_(1,3),0,0} ,{-M_(1,1), 0, M_(1,3),0},{M_(1,0),0,0, M_(1,3)},{0,-M_(1,1),-M_(1,2), 0},{0, M_(1,0), 0, M_(1,2)} ,{0,0, M_(1,0), M_(1,1)}});
    
    return {C_(-1),C_0,C_1,C_2,C_3};)



--Test example for function ComplexesList1
R=ZZ/32003[x,y,z]
phi=map(R^{2:1},R^4,matrix{{x,y,z,0},{0,x,y,z}})
ComplexesList1(phi)
C_0 == eagonNorthcott phi
--this is false only because of differences in negatives and columns in different orders
--check homology
apply(4,i-> HH_i C_(-1) ==0)
apply(4,i-> HH_i C_0 ==0)
apply(4,i-> HH_i C_1 ==0)
apply(4,i-> HH_i C_2 ==0)
apply(4,i-> HH_i C_3 ==0)


--Examples for ComplexesList2

--Example where none of the complexes are virtual resolutions
R=ZZ/32003[x_0,x_1,y_0,y_1,Degrees=>{2:{1,0},2:{0,1}}]
phi=map(R^2,R^{4:{-1,-1}},matrix{{x_0*y_0,x_0*y_1,-x_0*y_0,0},{0,-x_1*y_1,x_1*y_0,x_1*y_1}})
isHomogeneous phi
ComplexesList2(phi)
B=intersect(ideal(x_0,x_1),ideal(y_0,y_1))
I=minors(2,phi)
IB=saturate(I,B)
needsPackage "VirtualResolutions"
apply({-1,0,1,2,3},j-> isVirtual(B,C_(j)))
--so all C^i are not virtual resolutions
--we can also see this by looking at the depth condition
needsPackage "Depth"
depth(I,R)
depth(IB,R)

R=ZZ/32003[x_0,x_1,y_0,y_1,Degrees=>{2:{1,0},2:{0,1}}]
phi=map(R^2,R^{4:{-2,-1}},matrix{{x_0^2*y_0,x_0^2*y_1,-x_0^2*y_1,0},{0,-x_1^2*y_1,x_1^2*y_0,x_1^2*y_1}})
isHomogeneous phi
ComplexesList2(phi)
B=intersect(ideal(x_0,x_1),ideal(y_0,y_1))
I=minors(2,phi)
IB=saturate(I,B)
needsPackage "VirtualResolutions"
apply({-1,0,1,2,3},j-> isVirtual(B,C_(j)))
--so all C^i are not virtual resolutions
--we can also see this by looking at the depth condition
needsPackage "Depth"
depth(I,R)
depth(IB,R)

phi=map(R^2,R^{4:{-2,-1}},matrix{{x_0^2*y_1,x_0*x_1*y_0,x_1^2*y_1,0},{0,x_0^2*y_0,x_0*x_1*y_1,x_1^2*y_0}})
isHomogeneous phi
ComplexesList2(phi)
B=intersect(ideal(x_0,x_1),ideal(y_0,y_1))
I=minors(2,phi)
IB=saturate(I,B)
needsPackage "VirtualResolutions"
apply({-1,0,1,2,3},j-> isVirtual(B,C_(j)))
--so all C^i are not virtual resolutions
--we can also see this by looking at the depth condition
needsPackage "Depth"
depth(I,R)
depth(IB,R)

R=ZZ/32003[x_0,x_1,y_0,y_1,z_0,z_1,Degrees=>{2:{1,0,0},2:{0,1,0},2:{0,0,1}}]
phi=map(R^2,R^{4:{-1,-2,0}},matrix{{x_0*y_0^2,x_0*y_0*y_1,x_0*y_1^2,0},{0,x_1*y_0^2,x_1*y_0*y_1,x_1*y_1^2}})
isHomogeneous phi
ComplexesList2(phi)
B=intersect(intersect(ideal(x_0,x_1),ideal(y_0,y_1)),ideal(z_0,z_1))
I=minors(2,phi)
IB=saturate(I,B)
depth(I,R)
depth(IB,R)
en=eagonNorthcott(phi)
en.dd
(C_0).dd


phi=map(R^2,R^{{-1,-2,0},{-2,0,-1},{0,-2,-1},{-1,0,-2}},matrix{{x_0*y_0^2,0,y_0*y_1*z_0,0},{0,x_0*x_1*z_1,0,x_1*z_1^2}})
phi=map(R^2,R^{{-1,-2,0},{-2,0,-1},{0,-2,-1},{-1,0,-2}},matrix{{x_0*y_0^2,0,y_1^2*z_0,0},{0,x_1^2*z_1,0,x_1*z_1^2}})
phi=map(R^2,R^{{-1,-2,0},{0,-1,-2},{-2,-1,0},{0,-2,-1}},matrix{{x_0*y_0^2,0,x_1^2*y_1,0},{0,y_0*z_0^2,0,y_1^2*z_1}})

--Random matrices

phi=map(R^2,R^{4:{-1,-2,-1}},matrix{{random({1,2,1},R),random({1,2,1},R),random({1,2,1},R),random({1,2,1},R)},{random({1,2,1},R),random({1,2,1},R),random({1,2,1},R),random({1,2,1},R)}})


--Examples for ComplexesList3

-- Strategy: First, since the ideal of maximal minors is contained in the ideal I generated by the first row (or any row), 
-- we may concentrate on making sure the first row has the desired property. Our hope is that the ideal of maximal minors might (?) inherit these properties.
-- Secondly, we know that depth(I) <= dimension of minimal primes. So we want to manufacture an ideal with a primary decomposition that contains some power of 
-- the irrelevant ideal B, so that saturation removes this and potentially changes the depth. 
-- So we hope to find a primary ideal P such that P intersect with B^n has depth 1 or 2, but P itself has depth 3.
-- One easy way to do this is to just choose P=0. Then B has depth 2, but B saturated with itself is zero, thus has infinity depth.

R = ZZ/32003[x_0,x_1,y_0,y_1, Degrees => {2:{1,0},2:{0,1}}]
B = intersect(ideal(x_0,x_1),ideal(y_0,y_1))
needsPackage "Depth"
needsPackage "VirtualResolutions"

-- So I'm going to make the first row of phi just the generators of B!
phi = map(R^{{0,-1},{-1,0}}, R^{{-1,-2},{-1,-2},{-1,-2},{-1,-2}}, matrix{{x_0*y_0, x_0*y_1, x_1*y_0,x_1*y_1},{y_0^2, y_0*y_1, y_0*y_1, y_1^2}})
isHomogeneous phi
I = minors(2,phi)
depth(I,R)
IB = saturate(I,B)
depth(IB,R)
-- So this did not do what I expected it to do. Instead of concentrating on the first row, I think I need to work directly with the ideal of maximal minors. See last example for P^1xP^1.


phi = map(R^{{-1,-1},{0,0}}, R^{{-2,-1},{-2,-1},{-1,-2},{-1,-2}}, matrix{{x_0,x_1,y_0,y_1},{x_0*x_1*y_0,x_0*x_1*y_1, x_0*y_0*y_1, x_1*y_0*y_1}})
isHomogeneous phi
ComplexesList3(phi)
I = minors(2,phi)
depth(I,R)
IB = saturate(I,B)
depth(IB,R)
--So, C^i are not virtual nor minimal free resolutions

phi = map(R^{{-1,0},{0,0}},R^{{-2,0},{-1,-1},{-1,-1},{-2,0}},matrix{{x_0,y_0,y_1,x_1},{x_1^2,x_0*y_1,x_1*y_0,x_0^2}})
isHomogeneous phi
ComplexesList3(phi)
en=eagonNorthcott(phi)
apply({-1,0,1,2,3},i-> isHomogeneous C_i)
apply({1,2,3},i-> isHomogeneous (C_1).dd#i)
I = minors(2,phi)
depth(I,R)
IB = saturate(I,B)
depth(IB,R)
--So, C^i are not virtual nor minimal free resolutions    

----------------------------------------------------------------------------------------
--Example of virtual but not minimal free:
phi = map(R^{{2,0},{0,2}},R^4,matrix{{x_0^2,x_0*x_1,x_1^2,0},{0,y_0^2,y_0*y_1,y_1^2}})
isHomogeneous phi
ComplexesList3(phi)
apply({-1,0,1,2,3},i-> isHomogeneous C_i)
I = minors(2,phi)
depth(I,R)
IB = saturate(I,B)
depth(IB,R)
--So, C^i are virtual but not minimal free resolutions
--------------------------------------------------------------------------------------

phi = map(R^{{-1,0},{0,-1}},R^{{-2,-1},{-1,-1},{-1,-1},{-1,-2}},matrix{{x_0*y_0,y_0,y_1,y_0^2},{x_1^2,x_0,x_1,x_1*y_1}})
isHomogeneous phi
ComplexesList3(phi)
apply({-1,0,1,2,3},i-> isHomogeneous C_i)
I = minors(2,phi)
depth(I,R)
IB = saturate(I,B)
depth(IB,R)
--So, C^i are not virtual nor minimal free resolutions
needsPackage "VirtualResolutions"
apply({-1,0,1,2,3},i-> isVirtual(B,C_i))
--indeed they are not virtual

phi = map(R^{{3,0},{0,3}},R^4,matrix{{x_0^3,x_0^2*x_1,x_0*x_1^2,x_1^3},{y_0^3,y_0^2*y_1,y_0*y_1^2,y_1^3}})
isHomogeneous phi
ComplexesList3(phi)
apply({-1,0,1,2,3},i-> isHomogeneous C_i)
I = minors(2,phi)
depth(I,R)
IB = saturate(I,B)
depth(IB,R)
--So, C^i are not virtual nor minimal free resolutions

phi = map(R^{{0,0},{-2,3}},R^{{-2,0},{-2,0},{-2,0},{-2,0}},matrix{{x_0^2,x_0*x_1,x_1^2,0},{y_0^3,y_0^2*y_1,y_0*y_1^2,y_1^3}})
isHomogeneous phi
ComplexesList3(phi)
apply({-1,0,1,2,3},i-> isHomogeneous C_i)
I = minors(2,phi)
depth(I,R)
IB = saturate(I,B)
depth(IB,R)
--So, C^i are not virtual nor minimal free resolutions

---------------------------------------------------------------------------------------------------
--So this next very boring matrix is specifically constructed to have the ideal of maximal minors equal to the irrelevant ideal.
phi = map(R^{{1,0},{0,1}}, R^4, matrix{{x_0,x_1,0,x_0},{0, y_0, y_1, y_0}})
isHomogeneous phi
needsPackage "Depth"
I = minors(2,phi)
depth(I,R)
IB = saturate(I,B)
depth(IB,R)
--So the depth of I is 1, but the saturation of I has depth infinity, as desired!
-------------------------------------------------------------------------------------------------


--Examples on P^1 x P^2

R=ZZ/32003[x_0,x_1,y_0,y_1,y_2,Degrees=>{2:{1,0},3:{0,1}}]
B=intersect(ideal(x_0,x_1),ideal(y_0,y_1,y_2))
needsPackage "Depth"
needsPackage "VirtualResolutions"

--Goal: find homogeneous 2x4 matrices whose ideal of maximal minors has depth 1 or 2 and saturated depth 3

phi = map(R^{{-1,0},{0,-1}},R^{{-2,-1},{-2,-1},{-2,-1},{-2,-1}},matrix{{x_0*y_0,x_1*y_1,x_0*y_2,x_1*y_2},{0,x_0^2,x_0*x_1,x_1^2}})
isHomogeneous phi
ComplexesList3(phi)
apply({-1,0,1,2,3},i-> isHomogeneous C_i)
I = minors(2,phi)
depth(I,R)
IB = saturate(I,B)
depth(IB,R)
--So, C^i are not virtual nor minimal free resolutions

----------------------------------------------------------------------------------------------
phi = map(R^{{2,0},{0,1}},R^4,matrix{{x_0^2,x_0*x_1,x_1^2,0},{0,y_0,y_1,y_2}})
isHomogeneous phi
ComplexesList3(phi)
apply({-1,0,1,2,3},i-> isHomogeneous C_i)
I = minors(2,phi)
depth(I,R)
IB = saturate(I,B)
depth(IB,R)
primaryDecomposition I
primaryDecomposition IB
--depth of I is 2 and depth of IB is 3
--So, C^i are virtual but not minimal free resolutions
--Now, compare virtual resolutions with the minimal free resolutions that they correspond to.
--C_(-1) is a virutal res of cokernel of (C_(-1)).dd#1
M_(-1) = res coker((C_(-1)).dd#1)
C_(-1)
(M_(-1)).dd
(C_(-1)).dd
--Betti numbers of virtual res are larger
--C_0 is a virtual res of the ideal I (really R/I but M2 does this)
M_0 = res I
C_0
(M_0).dd
(C_0).dd
--Betti numbers of virtual res are larger
--Additional note: HH_1 C_0 is the only nonzero homology group, and it is annihilated by B^2.

--C_1 is a virtual res of coker phi
M_1 = res coker(phi)
C_1
(M_1).dd
(C_1).dd
--Betti numbers of virtual res are larger
--C_2 is a virtual res of the cokernel of (C_2).dd#1
M_2 = res coker((C_2).dd#1)
C_2
(M_2).dd
(C_2).dd
--Betti numbers of virtual res are smaller
--C_3 is a virtual res of cokernel of (C_3).dd#1
M_3 = res coker((C_3).dd#1)
C_3
(M_3).dd
(C_3).dd
--Betti numbers are different! C_3 is actually shorter than M_3 and has smaller Betti numbers
---------------------------------------------------------------------------------------------

phi = map(R^{{2,0},{0,1}},R^3,matrix{{x_0^2,x_0*x_1,x_1^2},{y_0,y_1,y_2}})
isHomogeneous phi
I=minors(2,phi)
depth(I,R)
IB=saturate(I,B)
depth(IB,R)
I==IB
primaryDecomposition I
primaryDecomposition IB
--depth of both is 2, so C_i are virtual and free res
F = eagonNorthcott(phi)
M = res I
--same Betti numbers


-- Examples on P^1 x P^1 x P^1 ------------------------

R=ZZ/101[x_0,x_1,y_0,y_1,z_0,z_1,Degrees=>{2:{1,0,0},2:{0,1,0},2:{0,0,1}}]
B=intersect(ideal(x_0,x_1),ideal(y_0,y_1),ideal(z_0,z_1))

L = permutations {x_0*y_0*z_0, x_1*y_0*z_0, x_1*y_1*z_0, x_1*y_0*z_1, x_0*y_0*z_1, x_0*y_1*z_1, x_0*y_1*z_0, x_1*y_1*z_1}
a=random(40320)

phi=map(R^2,R^{4:{-1,-1,-1}},matrix{flatten apply(4,i-> (L_a)_i), flatten apply(4,i->(L_a)_{i+4})})

isHomogeneous(phi)
I=minors(2,phi)
needsPackage "Depth"
depth(I,R)
IB=saturate(I,B)
depth(IB,R)

for a from 0 to 40319 list (if depth(saturate(minors(2,map(R^2,R^{4:{-1,-1,-1}},matrix{flatten apply(4,i-> (L_a)_i), flatten apply(4,i->(L_a)_{i+4})})),B),R)>2 then break a; a)
-- the above code never returned a number, so I think this means that the saturated depth is always \leq 2

--map of random (1,1,1) forms
phi=map(R^2,R^{4:{-1,-1,-1}},matrix{flatten apply(4,i->random({1,1,1},R)),flatten apply(4,i->random({1,1,1},R))})
--this has saturated depth of 3


-- Examples on P^1 x P^1 x P^2 ----------------------

R=ZZ/32003[x_0,x_1,y_0,y_1,z_0,z_1,z_2,Degrees=>{2:{1,0,0},2:{0,1,0},3:{0,0,1}}]
B=intersect(ideal(x_0,x_1),ideal(y_0,y_1),ideal(z_0,z_1,z_2))

phi=map(R^2,R^{4:{-1,-1,-2}},matrix{{x_0*y_0*z_0^2, x_0*y_1*z_0*z_1, x_0*y_0*z_0*z_2, x_0*y_1*z_1*z_2},{x_1*y_0*z_1*z_2, x_1*y_1*z_1^2, x_1*y_0*z_0*z_1, x_1*y_1*z_2^2}})
isHomogeneous(phi)
I=minors(2,phi)
needsPackage "Depth"
depth(I,R)
IB=saturate(I,B)
depth(IB,R)
--depth of both is 1

-- Example on P^1 x P^2 x P^3 -----------------------------

R=ZZ/32003[x_0,x_1,y_0,y_1,y_2,z_0,z_1,z_2,z_3,Degrees=>{2:{1,0,0},3:{0,1,0},4:{0,0,1}}]
B=intersect(ideal(x_0,x_1),ideal(y_0,y_1,y_2),ideal(z_0,z_1,z_2,z_3))

--Different entries for matrix, to be chosen randomly from this list
L111= flatten entries gens B --degree (1,1,1)
L102= flatten entries basis({1,0,2},R) --degree (1,0,2)
L321= flatten entries basis({3,2,1},R) --degree (3,2,1)
L210= flatten entries basis({2,1,0},R)
L120= flatten entries basis({1,2,0},R)
L110= flatten entries basis({1,1,0},R)
L002= flatten entries basis({0,0,2},R)
L001= flatten entries basis({0,0,1},R)

--Make 2x4 matrix with random entries from list
phi=map(R^2,R^{4:{-1,-1,-1}},matrix{flatten apply(4,i-> ((random L)_i)), flatten apply(4,i->(random L)_{i+4})})
phi=map(R^2,R^{4:{-1,0,-2}},matrix{flatten apply(4,i-> ((random L)_i)), flatten apply(4,i->(random L)_{i+4})})
phi=map(R^2,R^{4:{-3,-2,-1}},matrix{flatten apply(4,i-> ((random L)_i)), flatten apply(4,i->(random L)_{i+4})})
L120'=random L120
L210'=random L210
L110'=random L110
L002'=random L002
phi=map(R^{{-2,-1,-2},{-3,-3,0}},R^{4:{-3,-3,-2}},matrix{flatten apply(4,i-> ((L120')_i)),flatten apply(4,i->(L002')_i)})
phi=map(R^{{0,0,-1},{-1,-1,0}},R^{4:{-1,-1,-1}},matrix{flatten apply(4,i-> ((L110')_i)),flatten apply(4,i->(L001)_i)})
phi=map(R^{{0,0,-2},{-1,-1,0}},R^{4:{-1,-1,-2}},matrix{flatten apply(4,i-> ((L110')_i)),flatten apply(4,i->(L002')_i)})

isHomogeneous(phi)
I=minors(2,phi)
needsPackage "Depth"
depth(I,R)
IB=saturate(I,B)
depth(IB,R)
primaryDecomposition I
primaryDecomposition IB

-- 3x4 case
L120'=random L120
L210'=random L210
L002'=random L002
phi=map(R^{{-2,-1,-2},{-1,-2,-2},{-3,-3,0}},R^{4:{-3,-3,-2}},matrix{flatten apply(4,i-> ((L120')_i)), flatten apply(4,i-> (L210')_i), flatten apply(4,i->(L002')_i)})
phi=map(R^3,R^{4:{-1,-1,-1}},matrix{flatten apply(4,i-> ((L')_i)), flatten apply(4,i-> (L')_{i+4}), flatten apply(4,i->(L')_{i+8})})
phi=map(R^3,R^{4:{-1,0,-2}},matrix{flatten apply(4,i-> ((L')_i)), flatten apply(4,i-> (L')_{i+4}), flatten apply(4,i->(L')_{i+8})})
phi=map(R^3,R^{4:{-3,-2,-1}},matrix{flatten apply(4,i-> ((L')_i)), flatten apply(4,i-> (L')_{i+4}), flatten apply(4,i->(L')_{i+8})})

isHomogeneous phi
I=minors(3,phi)
depth(I,R)
IB=saturate(I,B)
depth(IB,R)

--Examples on P^1 x P^3-----------------------------------------------------------------------------

R=ZZ/32003[x_0,x_1,y_0,y_1,y_2,y_3,Degrees=>{2:{1,0},4:{0,1}}]
B=intersect(ideal(x_0,x_1),ideal(y_0,y_1,y_2,y_3))

---------------------------------------------------------------
phi=map(R^{{0,-1},{-3,0}},R^{4:{-3,-1}},matrix{{x_0^3,x_0^2*x_1,x_0*x_1^2,x_1^3},{y_0,y_1,y_2,y_3}})
isHomogeneous(phi)
ComplexesList3(phi)
I=minors(2,phi)
depth(I,R)
IB=saturate(I,B)
depth(IB,R)
primaryDecomposition I
primaryDecomposition IB
apply({-1,0,1,2,3},i->isVirtual(B,C_i))
--depth of I is 2, depth of IB is 3
--So, C^i are virtual but not minimal free resolutions
--Interesting note:
phi2 = map(R^{2:{1,1}},R^{{0,1},3:{1,0}},matrix{{x_0,y_0,y_1,y_2},{x_1,y_1,y_2,y_3}})
--then IB=minors(2,phi2)

--Now, compare virtual resolutions with the minimal free resolutions that they correspond to.
--C_(-1) is a virutal res of cokernel of (C_(-1)).dd#1
M_(-1) = res coker((C_(-1)).dd#1)
C_(-1)
(M_(-1)).dd
(C_(-1)).dd
--These look essentially the same.
--C_0 is a virtual res of the ideal I
M_0 = res I
(M_0).dd
(C_0).dd
--these have same Betti numbers, but maps are slightly different
--C_1 is a virtual res of coker phi
M_1 = res coker(phi)
(M_1).dd
(C_1).dd
--again, same Betti numbers, different maps
--C_2 is a virtual res of the cokernel of (C_2).dd#1
M_2 = res coker((C_2).dd#1)
(M_2).dd
(C_2).dd
--Betti numbers are different! C_2 is actually shorter than M_2
--C_3 is a virtual res of cokernel of (C_3).dd#1
M_3 = res coker((C_3).dd#1)
C_3
(M_3).dd
(C_3).dd
--Betti numbers are different! C_3 is actually shorter than M_3
-------------------------------------------------------------------------------------------------



--Examples on P^1xP^4------------------------------------------------------------------------
R=ZZ/32003[x_0,x_1,y_0,y_1,y_2,y_3,y_4,Degrees=>{2:{1,0},5:{0,1}}]
B= intersect(ideal(x_0,x_1),ideal(y_0,y_1,y_2,y_3,y_4))

phi = map(R^{{4,0},{0,1}},R^5,matrix{{x_0^4,x_0^3*x_1,x_0^2*x_1^2,x_0*x_1^3,x_1^4},{y_0,y_1,y_2,y_3,y_4}})
isHomogeneous phi
I=minors(2,phi)
depth(I,R)
IB=saturate(I,B)
depth(IB,R)
I==IB
primaryDecomposition I
primaryDecomposition IB
-- f-g+1=4, depth I = 2, depth IB = 4, C_i are virtual not exact
F = eagonNorthcott phi
M = res I
--same Betti numbers




--Examples on Hirzebruch surface H_2-------------------------------------------------------------------------
R=ZZ/32003[x_0,x_1,y_0,y_1,Degrees=>{2:{1,0},{-2,1},{0,1}}]
B=intersect(ideal(x_0,x_1),ideal(y_0,y_1))
needsPackage "Depth"

phi = map(R^{{0,-1},{-3,0}},R^{4:{-3,-1}},matrix{{x_0^3,x_0^2*x_1,x_0*x_1^2,x_1^3},{x_0^2*y_0,x_0*x_1*y_0,x_1^2*y_0,y_1}})
isHomogeneous phi
I=minors(2,phi)
depth(I,R)
IB=saturate(I,B)
depth(IB,R)
--both depths are 1

-------------------------------------------------------------------------------------------
phi = map(R^{{1,0},{0,1}},R^{{0,0},{2,0},{0,0},{0,0}},matrix{{x_0,0,x_1,0},{0,y_0,0,y_1}})
isHomogeneous phi
I=minors(2,phi)
depth(I,R)
IB=saturate(I,B)
depth(IB,R)
--C_i are virtual but not exact
ComplexesList3(phi)
M= res I
M.dd
(C_0).dd
---------------------------------------------------------------------------------------------

phi = map(R^{{1,0},{0,1}},R^4,matrix{{x_0,x_1,x_0,x_1},{x_0^2*y_0,y_1,x_1^2*y_0,y_1}})
isHomogeneous phi
I=minors(2,phi)
depth(I,R)
IB=saturate(I,B)
depth(IB,R)
--depth of both is 2, so C_i are not virtual nor exact

phi = map(R^{{1,0},{1,1}},R^4,matrix{{x_0,x_1,x_0,x_1},{x_0^3*y_0,x_0*y_1,x_1*y_1,x_1^3*y_0}})
isHomogeneous phi
I=minors(2,phi)
depth(I,R)
IB=saturate(I,B)
depth(IB,R)
--depth of both is 2

phi = map(R^{{4,0},{0,1}},R^{{2,0},{0,0},{2,0},{0,0}},matrix{{x_0^2,0,x_1^2,0},{y_0,y_1,y_0,y_1}})
isHomogeneous phi
I=minors(2,phi)
depth(I,R)
IB=saturate(I,B)
depth(IB,R)
I==IB
primaryDecomposition I
primaryDecomposition IB
--depth of both is 2

phi = map(R^{{4,0},{0,1}},R^{{2,0},{0,0},{2,0},{0,0}},matrix{{x_0^2,x_0^3*x_1,x_1^2,x_0*x_1^3},{y_0,y_1,y_0,y_1}})
isHomogeneous phi
I=minors(2,phi)
depth(I,R)
IB=saturate(I,B)
depth(IB,R)
I==IB
primaryDecomposition I
primaryDecomposition IB
--depth of both is 2

phi = map(R^{{1,1},{0,1}},R^{{2,0},{0,0},{0,0},{2,0}},matrix{{x_0*y_0,x_0*y_1,x_1*y_1,x_1*y_0},{y_0,0,y_1,0}})
isHomogeneous phi
I=minors(2,phi)
depth(I,R)
IB=saturate(I,B)
depth(IB,R)
I==IB
primaryDecomposition I
primaryDecomposition IB
--depth of both is 2

phi = map(R^{{4,0},{0,2}},R^{{2,0},{2,0},{2,0},{0,0}},matrix{{x_0^2,x_0*x_1,x_1^2,0},{0,x_0*x_1*y_0^2,y_0*y_1,y_1^2}})
isHomogeneous phi
I=minors(2,phi)
depth(I,R)
IB=saturate(I,B)
depth(IB,R)
I==IB
primaryDecomposition I
primaryDecomposition IB
--depth of both is 2

phi = map(R^{{4,0},{0,2}},R^{{2,0},{2,0},{2,0},{0,0}},matrix{{x_0^2,x_0*x_1,x_1^2,x_0^2*x_1^2},{y_0*y_1,x_0*x_1*y_0^2,y_0*y_1,y_1^2}})
isHomogeneous phi
I=minors(2,phi)
depth(I,R)
IB=saturate(I,B)
depth(IB,R)
I==IB
primaryDecomposition I
primaryDecomposition IB
--depth of both is 2

phi = map(R^{{4,0},{0,2}},R^{{0,0},{1,0},{2,0},{3,0}},matrix{{x_0^4,x_0^3,x_0^2,x_0},{x_1^4*y_0^2,x_1*y_0*y_1,y_0*y_1,x_1*y_0^2}})
isHomogeneous phi
I=minors(2,phi)
depth(I,R)
IB=saturate(I,B)
depth(IB,R)
I==IB
primaryDecomposition I
primaryDecomposition IB
--depth of both is 1

phi = map(R^{{3,0},{-1,1}},R^{{0,0},{1,0},{0,0}},matrix{{x_0^3,x_0*x_1,x_1^3},{x_1*y_0,0,x_1*y_0}})
isHomogeneous phi
I=minors(2,phi)
depth(I,R)
IB=saturate(I,B)
depth(IB,R)
I==IB
primaryDecomposition I
primaryDecomposition IB
--depth of both is 1 (need first to be 1 and second ot be 2)


---Examples on P^2xP^5------------------------------------------------------------------------
R=ZZ/32003[x_0,x_1,x_2,y_0,y_1,y_2,y_3,y_4,y_5,Degrees=>{3:{1,0},6:{0,1}}]
B=intersect(ideal(x_0,x_1,x_2),ideal(y_0,y_1,y_2,y_3,y_4,y_5))

--Graph of the embedding P^2-->P^5 of O(2)
phi = map(R^{{2,0},{0,1}},R^6,matrix{{x_0^2,x_0*x_1,x_0*x_2,x_1^2,x_1*x_2,x_2^2},{y_0,y_1,y_2,y_3,y_4,y_5}})
isHomogeneous phi
I=minors(2,phi)
depth(I,R)
IB=saturate(I,B)
depth(IB,R)
I==IB
primaryDecomposition I
primaryDecomposition IB
-- f-g+1=5, depth I = 3, depth IB = 5, so C_i are virtual but not exact
F = eagonNorthcott phi
M = res I
--Betti numbers of the EN are actually larger than those of min free res of I


-------------------------------------------------------------------------------------------


--Example on H_1 x P^4---------------------------------------------------------------------
-- This is in our paper ----------------

needsPackage "Depth"
R=ZZ/32003[x_0,x_1,x_2,x_3,y_0,y_1,y_2,y_3,y_4,Degrees=>{{1,0,0},{-1,1,0},{1,0,0},{0,1,0},5:{0,0,1}}]
B=intersect(ideal(x_0,x_2),ideal(x_1,x_3),ideal(y_0,y_1,y_2,y_3,y_4))

phi = map(R^{{0,0,-1},{-1,-1,0}},R^{5:{-1,-1,-1}},matrix{{x_0*x_3,x_2*x_3,x_0^2*x_1,x_0*x_1*x_2,x_1*x_2^2},{y_0,y_1,y_2,y_3,y_4}})
isHomogeneous phi
I=minors(2,phi)
depth(I,R)
IB=saturate(I,B)
depth(IB,R)
I==IB
primaryDecomposition I
primaryDecomposition IB
I=minors(1,phi)
depth(I,R)
IB=saturate(I,B)
depth(IB,R)

en=eagonNorthcott phi
en.dd
prune HH en

basis({2,1},R)


--------- Graph of degree d > 2 Veronese ------------------------------------------------
needsPackage "Depth"

-- d=3 -----------
R=ZZ/32003[x_0,x_1,y_0,y_1,y_2,y_3,Degrees=>{2:{1,0},4:{0,1}}]
B=intersect(ideal(x_0,x_1),ideal(y_0,y_1,y_2,y_3))
phi=map(R^{{0,-1},{-3,0}},R^{4:{-3,-1}},matrix{{x_0^3,x_0^2*x_1,x_0*x_1^2,x_1^3},{y_0,y_1,y_2,y_3}})
isHomogeneous(phi)
ComplexesList3(phi)
I=minors(2,phi)
depth(I,R)
IB=saturate(I,B)
depth(IB,R)
primaryDecomposition I
Q=oo_0
primaryDecomposition IB
apply({-1,0,1,2,3},i->isVirtual(B,C_i))
--depth of I is 2, depth of IB is 3
--So, C^i are virtual but not minimal free resolutions
--Interesting note:
phi2 = map(R^{2:{1,1}},R^{{0,1},3:{1,0}},matrix{{x_0,y_0,y_1,y_2},{x_1,y_1,y_2,y_3}})
--then IB=minors(2,phi2)
netList entries gens gb I
netList entries gens gb IB
netList entries gens gb Q



-- d=4 ------------
R=ZZ/32003[x_0,x_1,y_0,y_1,y_2,y_3,y_4,Degrees=>{2:{1,0},5:{0,1}}]
B= intersect(ideal(x_0,x_1),ideal(y_0,y_1,y_2,y_3,y_4))

phi = map(R^{{4,0},{0,1}},R^5,matrix{{x_0^4,x_0^3*x_1,x_0^2*x_1^2,x_0*x_1^3,x_1^4},{y_0,y_1,y_2,y_3,y_4}})
isHomogeneous phi
I=minors(2,phi)
depth(I,R)
IB=saturate(I,B)
depth(IB,R)
I==IB
primaryDecomposition I
Q=oo_0
primaryDecomposition IB
-- f-g+1=4, depth I = 2, depth IB = 4, C_i are virtual not exact
F = eagonNorthcott phi
M = res I
--same Betti numbers
phi2 = map(R^{2:{1,1}},R^{{0,1},4:{1,0}},matrix{{x_0,y_0,y_1,y_2,y_3},{x_1,y_1,y_2,y_3,y_4}})
J=minors(2,phi2)
IB==J
netList entries gens gb I
netList entries gens gb IB
netList entries gens gb Q
