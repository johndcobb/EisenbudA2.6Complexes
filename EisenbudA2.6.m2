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

--Function for rings that are Multigraded
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
	    --if j==1 then apply(subsets(Columns,j+1),L-> (sum L)) else (
	   --flatten apply(multiSubsets(Rows,j-1),L'->(apply(subsets(Columns,j+1),L->(sum L-sum L')))))
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

-- This function is trying to correct a mistake above about calculating the degrees.

ComplexesList3 = M -> (
    I := {-1,0,1,2,3};
    apply(I, i-> C_i = new ChainComplex);
    R := ring(M);
    apply(I, i-> C_i.ring = R);
    
    Rows := degrees target M;
    Columns := degrees source M;
    
    --Define modules for C^(-1)
    
    C_(-1)#0 = R^(apply(subsets(Columns,1), L -> sum L));

    Cmoddegs := apply({1,2,3}, j -> ( flatten apply(multiSubsets(Rows, j), L' -> (apply(subsets(Columns, j+1), L-> sum L - sum L')))));
    apply({1,2,3}, j-> C_(-1)#j = R^(Cmoddegs_(j-1)));
   
    C_(-1)#4 = 0;
    
    --Define maps for C^(-1)
    C_(-1).dd#1 = map(C_(-1)_0,C_(-1)_1,matrix{{M_(0,0), M_(0,1), M_(0,2), M_(0,3), 0, 0, 0, 0, 0, 0, 0, 0}, {M_(1,0), M_(1,1), M_(1,2), M_(1,3), M_(0,0), M_(0,1), M_(0,2), M_(0,3), 0 ,0 ,0 ,0},{0,0,0,0,M_(1,0),M_(1,1), M_(1,2),M_(1,3),M_(0,0),M_(0,1),M_(0,2),M_(0,3)},{0,0,0,0,0,0,0,0,M_(1,0),M_(1,1),M_(1,2),M_(1,3)}});
    C_(-1).dd#2 = map(C_(-1)_1,C_(-1)_2,matrix{{-M_(0,1), -M_(0,2), -M_(0,3),0,0,0,0,0,0,0,0,0}, {M_(0,0), 0, 0, -M_(0,2), -M_(0,3), 0, 0, 0, 0, 0, 0, 0}, {0, M_(0,0), 0, M_(0,1), 0, -M_(0,3), 0,0,0,0,0,0}, {0,0, M_(0,0), 0, M_(0,1), M_(0,2),0,0,0,0,0,0}, {-M_(1,1), -M_(1,2), -M_(1,3), 0,0,0, -M_(0,1), -M_(0,2), -M_(0,3),0,0,0}, {M_(1,0), 0,0, -M_(1,2), -M_(1,3), 0, M_(0,0),0,0,-M_(0,2), -M_(0,3),0}, {0, M_(1,0), 0, M_(1,1), 0, -M_(1,3), 0, M_(0,0), 0, M_(0,1), 0, -M_(0,3)}, {0,0, M_(1,0), 0, M_(1,1), M_(1,2),0,0, M_(0,0), 0,M_(0,1), M_(0,2)}, {0,0,0,0,0,0, -M_(1,1), -M_(1,2), -M_(1,3), 0,0,0}, {0,0,0,0,0,0,M_(1,0),0,0,-M_(1,2), -M_(1,3),0}, {0,0,0,0,0,0,0,M_(1,0),0,M_(1,1),0,-M_(1,3)}, {0,0,0,0,0,0,0,0,M_(1,0),0,M_(1,1),M_(1,2)}});
    C_(-1).dd#3 = map(C_(-1)_2,C_(-1)_3,matrix{{M_(0,2), M_(0,3), 0,0}, {-M_(0,1), 0, M_(0,3),0}, {0, -M_(0,1), -M_(0,2), 0}, {M_(0,0),0,0, M_(0,3)}, {0, M_(0,0), 0 , M_(0,2)} ,{0,0, M_(0,0), M_(0,1)} ,{M_(1,2), M_(1,3),0,0} ,{-M_(1,1), 0, M_(1,3),0} , {0,-M_(1,1), -M_(1,2), 0} ,{M_(1,0),0,0, M_(1,3)}, {0, M_(1,0), 0, M_(1,2)} ,{0,0, M_(1,0), M_(1,1)}});
    
    --Define modules for C^0
    C_0#0 = R^{sum Rows};
    C_0#1 = R^(apply(subsets(Columns,2),L-> sum L));
    Cmoddegs := apply({2,3},j-> flatten apply(multiSubsets(Rows,j-1),L'->apply(subsets(Columns,j+1),L->sum L-sum L')));
    
    apply({2,3}, j-> C_0#j = R^(Cmoddegs_(j-2)));
    C_0#4 = 0;
    
    --Define maps for C^0
    (C_0).dd#1 = map(C_0_0,C_0_1,matrix{{M_(0,0)*M_(1,1)-M_(1,0)*M_(0,1), M_(0,0)*M_(1,2)-M_(1,0)*M_(0,2), M_(0,0)*M_(1,3)-M_(1,0)*M_(0,3), M_(0,1)*M_(1,2)-M_(1,1)*M_(0,2), M_(0,1)*M_(1,3)-M_(1,1)*M_(0,3), M_(0,2)*M_(1,3)-M_(1,2)*M_(0,3)}});
    (C_0).dd#2 = map(C_0_1,C_0_2,matrix{{M_(0,2),M_(0,3),0,0,M_(1,2),M_(1,3),0,0},{-M_(0,1),0,M_(0,3),0,-M_(1,1),0,M_(1,3),0},{0,-M_(0,1),-M_(0,2),0,0,-M_(1,1),-M_(1,2),0},{M_(0,0),0,0,M_(0,3),M_(1,0),0,0,M_(1,3)},{0,M_(0,0),0,-M_(0,2),0,M_(1,0),0,-M_(1,2)},{0,0,M_(0,0),M_(0,1),0,0,M_(1,0),M_(1,1)}});
    (C_0).dd#3 = map(C_0_2,C_0_3,matrix{{-M_(0,3),-M_(1,3),0},{M_(0,2),M_(1,2),0},{-M_(0,1),-M_(1,1),0},{M_(0,0),M_(1,0),0},{0,-M_(0,3),-M_(1,3)},{0,M_(0,2),M_(1,2)},{0,-M_(0,1),-M_(1,1)},{0,M_(0,0),M_(1,0)}});
    
    --Define modules for C^1
    --still need to do
    C_1#0 = target M;
    C_1#1 = source M;
    C_1#2 = R^(apply(subsets(Columns,3), L -> sum L));
    C_1#3 = R^(flatten apply(multiSubsets(Rows,1), L-> (apply(subsets(Columns,4), L' -> sum L - sum L'))));
    C_1#4 = 0;
    
    --Define maps for C^1
    (C_1).dd#1 = map(C_1_0,C_1_1,M);
    (C_1).dd#2 = map(C_1_1,C_1_2,matrix{{M_(0,1)*M_(1,2)-M_(1,1)*M_(0,2), M_(0,1)*M_(1,3)-M_(1,1)*M_(0,3), M_(0,2)*M_(1,3)-M_(1,2)*M_(0,3),0},{-M_(0,0)*M_(1,2)+M_(1,0)*M_(0,2), -M_(0,0)*M_(1,3)+M_(1,0)*M_(0,3),0,M_(0,2)*M_(1,3)-M_(1,2)*M_(0,3)},{M_(0,0)*M_(1,1)-M_(1,0)*M_(0,1),0,-M_(0,0)*M_(1,3)+M_(1,0)*M_(0,3), -M_(0,1)*M_(1,3)+M_(1,1)*M_(0,3)},{0,M_(0,0)*M_(1,1)-M_(1,0)*M_(0,1), M_(0,0)*M_(1,2)-M_(1,0)*M_(0,2), M_(0,1)*M_(1,2)-M_(1,1)*M_(0,2)}});
    (C_1).dd#3 = map(C_1_2,C_1_3,matrix{{-M_(0,3),-M_(1,3)},{M_(0,2),M_(1,2)},{-M_(0,1),-M_(1,1)},{M_(0,0),M_(1,0)}});
    
    --Define modules for C^2
    --still need to do
    
    C_2#0 = R^(apply(multiSubsets(Rows, 2), L-> sum L));
    C_2#1 = R^(flatten apply(multiSubsets(Rows, 1), L'-> apply(subsets(Columns,1), L-> sum L + sum L')));
    C_2#2 = R^(apply(subsets(Columns,2), L-> sum L));
    C_2#3 = R^{sum Columns};
    C_2#4 = 0;
   	 
    --Define maps for C^2
    (C_2).dd#1 = map(C_2_0,C_2_1,matrix{{M_(0,0),M_(0,1),M_(0,2),M_(0,3),0,0,0,0},{M_(1,0),M_(1,1),M_(1,2),M_(1,3),M_(0,0),M_(0,1),M_(0,2),M_(0,3)},{0,0,0,0,M_(1,0),M_(1,1),M_(1,2),M_(1,3)}});
    (C_2).dd#2 = map(C_2_1,C_2_2,matrix{{-M_(0,1),-M_(0,2),-M_(0,3),0,0,0},{M_(0,0),0,0,-M_(0,2),-M_(0,3),0},{0,M_(0,0),0,M_(0,1),0,-M_(0,3)},{0,0,M_(0,0),0,M_(0,1),M_(0,2)},{-M_(1,1),-M_(1,2),-M_(1,3),0,0,0},{M_(1,0),0,0,-M_(1,2),-M_(1,3),0},{0,M_(1,0),0,M_(1,1),0,-M_(1,3)},{0,0,M_(1,0),0,M_(1,1),M_(1,2)}});
    (C_2).dd#3 = map(C_2_2,C_2_3,matrix{{M_(0,2)*M_(1,3)-M_(1,2)*M_(0,3)},{-M_(0,1)*M_(1,3)+M_(1,1)*M_(0,3)},{M_(0,1)*M_(1,2)-M_(1,1)*M_(0,2)},{M_(0,0)*M_(1,3)-M_(1,0)*M_(0,3)},{-M_(0,0)*M_(1,2)+M_(1,0)*M_(0,2)},{M_(0,0)*M_(1,1)-M_(0,1)*M_(1,0)}});
    
    --Define modules for C^3
    --still need to do
    C_3#0 = R^(apply(multiSubsets(Rows,3), L-> sum L));
    Cmoddegs := apply({1,2},j-> flatten apply(multiSubsets(Rows,3-j), L'-> apply(subsets(Columns,j), L-> sum L + sum L')));
    apply({1,2}, j-> C_3#j = R^(Cmoddegs_(j-1)));
    C_3#3 = R^(apply(subsets(Columns,3), L-> sum L));
    C_3#4 = 0;
    
    --Define maps for C^3
    (C_3).dd#1 = map(C_3_0,C_3_1,matrix{{M_(0,1), M_(0,2), M_(0,3), 0,0, 0, M_(1,1), M_(1,2), M_(1,3), 0,0,0}, {-M_(0,0), 0,0, M_(0,2), M_(0,3), 0, -M_(1,0), 0, 0, M_(1,2), M_(1,3),0}, {0, -M_(0,0), 0, -M_(0,1), 0, M_(0,3), 0, -M_(1,0), 0, -M_(1,1), 0, M_(1,3)}, {0,0, -M_(0,0), 0 ,-M_(0,1), -M_(0,2), 0,0, -M_(1,0), 0,-M_(1,1),-M_(1,2)}});
    (C_3).dd#2 = map(C_3_1,C_3_2,matrix{{M_(0,2), M_(0,3), 0,0,M_(1,2), M_(1,3), 0,0,0,0,0,0}, {-M_(0,1), 0, M_(0,3), 0, -M_(1,1), 0, M_(1,3), 0,0,0,0,0}, {0,-M_(0,1), -M_(0,2), 0,0, -M_(1,1), -M_(1,2), 0,0,0,0,0}, {M_(0,0), 0,0,M_(0,3),M_(1,0),0,0,M_(1,3),0,0,0,0},{0, M_(0,0),0,-M_(0,2),0,M_(1,0),0,-M_(1,2),0,0,0,0}, {0,0,M_(0,0), M_(0,1),0,0,M_(1,0),M_(1,1),0,0,0,0}, {0,0,0,0,-M_(0,2), -M_(0,3),0,0,M_(1,2),M_(1,3),0,0}, {0,0,0,0,M_(0,1),0,-M_(0,3),0,-M_(1,1),0,M_(1,3),0}, {0,0,0,0,0,M_(0,1),M_(0,2),0,0,-M_(1,1),-M_(1,2),0}, {0,0,0,0,-M_(0,0),0,0,-M_(0,3),M_(1,0),0,0,M_(1,3)}, {0,0,0,0,0,-M_(0,0), 0, M_(0,2), 0, M_(1,0), 0, -M_(1,2)}, {0,0,0,0,0,0,-M_(0,0), -M_(0,1),0,0,M_(1,0), M_(1,1)}});
    (C_3).dd#3 = map(C_3_2,C_3_3,matrix{{-M_(0,3),-M_(1,3),0,0}, {M_(0,2),M_(1,2),0,0}, {-M_(0,1),-M_(1,1),0,0}, {M_(0,0),M_(1,0),0,0}, {0,-M_(0,3),-M_(1,3),0}, {0,M_(0,2),M_(1,2),0} ,{0,-M_(0,1),-M_(1,1),0}, {0,M_(0,0),M_(1,0), 0}, {0,0, -M_(0,3), -M_(1,3)}, {0,0,M_(0,2),M_(1,2)}, {0,0,-M_(0,1),-M_(1,1)}, {0,0,M_(0,0),M_(1,0)}});
    
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
phi=map(R^2,R^{4:{-1,-1}},matrix{{x_0^2,x_0*x_1,x_1^2,0},{0,y_1^2, y_0*y_1, y_0}})
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
needsPackage "Depth"
R = ZZ/32003[x_0,x_1,y_0,y_1, Degrees=>{2:{1,0},2:{0,1}}]
phi = random(R^2,R^{4:{-2,-1}})
isHomogeneous phi
B= intersect(ideal(x_0,x_1),ideal(y_0,y_1))
I = minors(2,phi)
IB = saturate(I,B)
depth(I,R)
depth(IB,R)
phi
 -- {-7942x_0^2y_0+369x_0x_1y_0+4869x_1^2y_0+2334x_0^2y_1+15514x_0x_1y_1-9803x_1^2y_1, 12308x_0^2y_0+12911x_0x_1y_0-13124x_1^2y_0-1228x_0^2y_1-5026x_0x_1y_1+3622x_1^2y_1, 6806x_0^2y_0-6858x_0x_1y_0-9466x_1^2y_0+10827x_0^2y_1-4943x_0x_1y_1+6699x_1^2y_1,  11955x_0^2y_0+14173x_0x_1y_0-13805x_1^2y_0-5617x_0^2y_1-12087x_0x_1y_1-13331x_1^2y_1},
 --  {8608x_0^2y_0+5473x_0x_1y_0+2716x_1^2y_0+700x_0^2y_1+9965x_0x_1y_1+5982x_1^2y_1, 891x_0^2y_0+14979x_0x_1y_0-5272x_1^2y_0-14379x_0^2y_1-11418x_0x_1y_1-10759x_1^2y_1,  10605x_0^2y_0-4716x_0x_1y_0-5556x_1^2y_0-2379x_0^2y_1-8399x_0x_1y_1+3520x_1^2y_1, -2701x_0^2y_0-4132x_0x_1y_0-2413x_1^2y_0-2196x_0^2y_1-15978x_0x_1y_1+8942x_1^2y_1 }

-- Upon reading Daniel's email, I think I  have come up with more interesting examples of homogeneous maps.
R = ZZ/32003[x_0,x_1,y_0,y_1, Degrees => {2:{1,0},2:{0,1}}]
phi = map(R^{{1,1},{0,0}}, R^{{2,1},{2,1},{1,2},{1,2}}, matrix{{x_0,x_1,y_0,y_1},{x_0*x_1*y_0,x_0*x_1*y_1, x_0*y_0*y_1, x_1*y_0*y_1}})
isHomogeneous phi
-- I think this IS a homogeneous map, but the function is stupid!
ComplexesList3(phi)


