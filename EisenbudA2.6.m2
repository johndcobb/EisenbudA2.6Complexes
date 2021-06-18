--Goal: define a function which takes a ring R and map phi: R^f-->R^g with f
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


--2nd Attempt: Constructing C^i explicitly
restart
--Define a function that outputs a list of the free modules in C^i by giving
--pairs (a,b) that correspond to the terms S_a \otimes \wedge^b F, where
--S=symmetricAlgebra(G). Recall that C^i: K(phi')^*_{f-g-i} \to K(phi')_i
--and we will let (-a,b) correspond to S^*_a \otimes \wedge^b F.

L1 = (f,g,i)->(apply(i+1,j->{i-j,j}))
