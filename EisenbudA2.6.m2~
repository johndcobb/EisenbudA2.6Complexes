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
C(Matrix) := M -> (
    I := {-1,0,1,2,3};
    apply(I, i-> C_i = new ChainComplex);
    R := ring(M);
    apply(I, i-> C_i.ring = R);
    
    --Define modules for C^(-1)
    apply(4, j-> C_(-1)#j = R^{(binomial(4,j+1)*binomial(1+j,j)):(j+1)})
    C_(-1)#4 = 0
    
    --Define maps for C^(-1)
    --C.dd#0 = matrix{{M_(0,1), }}
    
    --Define modules for C^0
    C_0#0 = R^1
    apply({1,2,3}, j-> C_0#j = R^{(binomial(4,j+1)*binomial(j,j-1)):(j+1)})
    C_0#4 = 0
    
    --Define maps for C^0
    (C_0).dd#1 = matrix{{M_(0,0)*M_(1,1)-M_(1,0)*M_(0,1), M_(0,0)*M_(1,2)-M_(1,0)*M_(0,2), M_(0,0)*M_(1,3)-M_(1,0)*M_(0,3), M_(0,1)*M_(1,2)-M_(1,1)*M_(0,2), M_(0,1)*M_(1,3)-M_(1,1)*M_(0,3), M_(0,2)*M_(1,3)-M_(1,2)*M_(0,3)}}
    (C_0).dd#2 = matrix{{M_(0,2),M_(0,3),0,0,M_(1,2),M_(1,3),0,0},{-M_(0,1),0,M_(0,3),0,-M_(1,1),0,M_(1,3),0},{0,-M_(0,1),-M_(0,2),0,0,-M_(1,1),-M_(1,2),0},{M_(0,0),0,0,M_(0,3),M_(1,0),0,0,M_(1,3)},{0,M_(0,0),0,-M_(0,2),0,M_(1,0),0,-M_(1,2)},{0,0,M_(0,0),M_(0,1),0,0,M_(1,0),M_(1,1)}}
    (C_0).dd#3 = matrix{{-M_(0,3),-M_(1,3),0},{M_(0,2),M_(1,2),0},{-M_(0,1),-M_(1,1),0},{M_(0,0),M_(1,0),0},{0,-M_(0,3),-M_(1,3)},{0,M_(0,2),M_(1,2)},{0,-M_(0,1),-M_(1,1)},{0,M_(0,0),M_(1,0)}}
    
    --Define modules for C^1
    C_1#0 = R^2
    C_1#1 = R^{4:1}
    C_1#2 = R^{4:3}
    C_1#3 = R^{2:4}
    C_1#4 = 0
    
    --Define maps for C^1
    (C_1).dd#1 = M
    (C_1).dd#2 = matrix{{M_(0,1)*M_(1,2)-M_(1,1)*M_(0,2), M_(0,1)*M_(1,3)-M_(1,1)*M_(0,3), M_(0,2)*M_(1,3)-M_(1,2)*M_(0,3),0},{-M_(0,0)*M_(1,2)+M_(1,0)*M_(0,2), -M_(0,0)*M_(1,3)+M_(1,0)*M_(0,3),0,M_(0,2)*M_(1,3)-M_(1,2)*M_(0,3)},{M_(0,0)*M_(1,1)-M_(1,0)*M_(0,1),0,-M_(0,0)*M_(1,3)+M_(1,0)*M_(0,3), -M_(0,1)*M_(1,3)+M_(1,1)*M_(0,3)},{0,M_(0,0)*M_(1,1)-M_(1,0)*M_(0,1), M_(0,0)*M_(1,2)-M_(1,0)*M_(0,2), M_(0,1)*M_(1,2)-M_(1,1)*M_(0,2)}}
    (C_1).dd#3 = matrix{{-M_(0,3),-M_(1,3)},{M_(0,2),M_(1,2)},{-M_(0,1),-M_(1,1)},{M_(0,0),M_(1,0)}}
    
    --Define modules for C^2
    C_2#0 = R^3
    C_2#1 = R^{8:1}
    C_2#2 = R^{6:2}
    C_2#3 = R^{1:4}
    C_2#4 = 0
	 
    --Define maps for C^2
    (C_2).dd#1 = matrix{{M_(0,0),M_(0,1),M_(0,2),M_(0,3),0,0,0,0},{M_(1,0),M_(1,1),M_(1,2),M_(1,3),M_(0,0),M_(0,1),M_(0,2),M_(0,3)},{0,0,0,0,M_(1,0),M_(1,1),M_(1,2),M_(1,3)}}
    (C_2).dd#2 = matrix{{-M_(0,1),-M_(0,2),-M_(0,3),0,0,0},{M_(0,0),0,0,-M_(0,2),-M_(0,3),0},{0,M_(0,0),0,M_(0,1),0,-M_(0,3)},{0,0,M_(0,0),0,M_(0,1),M_(0,2)},{-M_(1,1),-M_(1,2),-M_(1,3),0,0,0},{M_(1,0),0,0,-M_(1,2),-M_(1,3),0},{0,M_(1,0),0,M_(1,1),0,-M_(1,3)},{0,0,M_(1,0),0,M_(1,1),M_(1,2)}}
    (C_2).dd#3 = matrix{{M_(0,2)*M_(1,3)-M_(1,2)*M_(0,3)},{-M_(0,1)*M_(1,3)+M_(1,1)*M_(0,3)},{M_(0,1)*M_(1,2)-M_(1,1)*M_(0,2)},{M_(0,0)*M_(1,3)-M_(1,0)*M_(0,3)},{-M_(0,0)*M_(1,2)+M_(1,0)*M_(0,2)},{M_(0,0)*M_(1,1)-M_(0,1)*M_(1,0)}}
    
    --Define modules for C^3
    
    --Define maps for C^3
    
    )
