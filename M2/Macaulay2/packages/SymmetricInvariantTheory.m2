load-- -*- coding: utf-8 -*-
newPackage(
        "SymmetricInvariantTheory",
        Version => "1.5", 
        Date => "May 17, 2017",
        Authors => {{Name => "Jonathan Niño", 
                  Email => "ja.nino937@uniandes.edu.co", 
                  HomePage => "http://www.uniandes.edu.co"}},
        Headline => "Methods for the Efficient Compution of Invariants for Permutation Groups.",
        DebuggingMode => true,
	PackageExports => {"SymmetricCharacterTable","SpechtModule","SpechtPolynomials"}
	
        )

export {"generatePermutationGroup"}
export {"secondaryInvariants"}
export {"SecondaryInvariant"}
export {"secondaryInvariant"}
export {"evaluateSecondaryInvariant"}
export {"representationMultiplicity"}
export {"testMultiplicity"}
export {"testGraphPermutations"}
export {"val","root","sons","numSon"}
export {"printSpechtPolynomial"}
export {"testStraigh"}



-----
-- This method codes 
-----
generatePermutationGroup = method()
generatePermutationGroup List := gens -> (
 
 group:= new MutableList;
 permGroup := tree(#(gens#0)) ;
 permGroup = PermutationTree{permGroup};
 
 r:=0;
 for i to #gens-1 do(
     added:= addPermutation(permGroup,gens#i);  
     if(added) then (
	 group#r = gens#i;
	 r= r+1;
	 ); 
 );
 frontier := new MutableList from group;
 
 while(#frontier!= 0) do
 (
     newFrontier := new MutableList;
     k:=0;
     for i to #frontier-1 do(
     	 for j to #gens -1 do (
    		perm:= (frontier#i)_(gens#j);
		if(addPermutation(permGroup,perm)) then (
		    
		       newFrontier#k = perm;
		       group#r= perm;
		       k=k+1;
		       r=r+1;
		);
	 
     	 );
     );
     frontier= newFrontier;
 );
 toList group
     
)


representationMultiplicity = method(TypicalValue => ZZ)
representationMultiplicity(List, ZZ):=  (group, row)->(
    charTable := irreducibleCharacters (#(group#0));
    cardinalities:= new MutableHashTable;
    for i to #group-1 do(
    	
	parti2:= cycleStructure(group#i);
	ind:= getIndexPartition(charTable,parti2);
	
	--print(group#i,parti2,ind);
	if(cardinalities#?ind) then 
	(cardinalities#ind = cardinalities#ind+1) 
	else cardinalities#ind = 1; 	
    );
    
    mult:= 0;
    inds:= keys(cardinalities);
    --print(inds);
    
    
    for i to #inds-1 do(
	mult= mult+cardinalities#(inds#i)*getEntry(charTable,row,inds#i);	
    	--print(mult,inds#i,cardinalities#(inds#i),getEntry(charTable,row,inds#i));
    );
    --error "Debug";
    mult/(#group)
        
)

-----
-- This method codes 
-----
PermutationTree = new HeaderType of BasicList

-----
-- This method codes 
-----
isIn = method()
isIn (PermutationTree,List) := (group, perm) ->(
    
     perm2:= apply(perm,i->(i-1));
     isNode(group#0,perm2)
)

-----
-- This method codes 
-----
addPermutation = method()
addPermutation(PermutationTree, List):= (group,perm)-> (
    
    perm2:= apply(perm, i->(i-1));
    addNode(group#0,perm2)    
)


------
-- Tree
------

-- A tree data structure was implemented to store a list permutations.
-- This structure allows to find in O(n) if a permutation belongs to the list.
-- It also allows to store lists in this time.
-- This data structure is used in the algorithm that calculates a group given a list
-- of generators.

Tree = new Type of MutableHashTable

-- Constructors

tree = method()
tree ZZ := (numSons)->(
    tr:= new Tree;
    tr#root = node(0,numSons);
    tr#length=0;
    tr#numSon= numSons;
    tr
)

-- Methods


------
-- Retrieves the root node of the tree.
------
getRoot = method()
getRoot(Tree):= (tr)->(
   tr#root
)

------
-- Checks whether there is node in the path given by the list ind.
------
isNode = method()
isNode(Tree, List) := (tr, ind)  -> (
    fin:= true;
    nod:= getRoot(tr);
    for i to ind#-1 when fin do(
    	 if isSon(nod,ind#i) then(
	     nod=getSon(nod,ind#i);
	 )
     	 else (fin = false);
    );
    fin
)

------
-- Adds a node to the tree at the given path. If there is already a node in the path it
-- does not change the tree and returns false. Otherwise it returns true.
------
addNode = method()
addNode(Tree, List):= (tr, ind)-> (
    fin:= false;
    nod:= getRoot(tr);
    for i to #ind-1 do(
    	 if isSon(nod,ind#i) then(
	     nod1:=getSon(nod,ind#i);
	     nod=nod1;
	 )
     	 else (
	     fin = true;
	     newNod:=node(0,tr#numSon);
	     addSon(nod,newNod,ind#i);
	     nod= newNod; 
	 );
    );
    if(fin) then tr#length = tr#length +1;
    fin
)


------
-- Node
------

-- This objects represents the nodes that form the tree
-- It has a list of sons which is a list of nodes. Also each node can store a value.

Node = new Type of MutableHashTable

-- Constructors

node = method()
node (Thing,ZZ) := (ele,numSons) -> (
    
    nod:= new Node;
    nod#value = ele;
    nod.sons = new MutableList from apply (toList(1..numSons),i-> Nothing);  
    nod  
) 

--Methods

------
-- Checks wheter the node has a son in the position ind
------
isSon = method()
isSon(Node,ZZ):= (nod, ind)->(
    val:= instance((nod#sons)#ind, Node);
    val
)

------
-- Adds a son to the node parent in the position ind.
------
addSon = method()
addSon(Node,Node,ZZ):= (parent, son, ind)->(
    added:= false;
    if(not isSon(parent,ind)) then (
    	(parent#sons)#ind = son;
	added = true;	
    );
    added
)

------
-- Gets the son at position ind
------
getSon = method()
getSon(Node,ZZ):= (nod, ind)->(  
    (nod#sons)#ind
)

------
-- Sets the value of the node
------
setElement = method()
setElement(Node,Thing):= (nod,element) -> (
    
    nod#val = element;
)

------
-- Retrieves the value store at the node.
------
getElement Node := (nod) -> (
    node#val
    )


SecondaryInvariant = new Type of MutableList;
secondaryInvariant = method()
secondaryInvariant(List,TableauList,YoungTableau):=(vect,standard,tableauS)->(
    
    secondaryInvariant := new SecondaryInvariant;
    j:= 0;
    for i to #vect-1 do(
    	if(not vect#i == 0) then (
	     secondaryInvariant#j = (vect#i,spechtPolynomial(tableauS,getTableau(standard,i)));   
	    j= j+1;
	);
    	
    );
    secondaryInvariant  
)

secondaryInvariant(List,TableauTupleList,YoungTableauTuple):=(vect,standard,tableauS)->(
    
    secondaryInvariant := new SecondaryInvariant;
    j:= 0;
    for i to #vect-1 do(
    	if(not vect#i == 0) then (
	     secondaryInvariant#j = (vect#i,spechtPolynomial(tableauS,getTableau(standard,i)));   
	    j= j+1;
	);
    	
    );
    secondaryInvariant  
)

secondaryInvariant(SpechtPolynomial):= specht ->(
    new SecondaryInvariant from {(1,specht)}
    )

evaluateSecondaryInvariant = method()
evaluateSecondaryInvariant(SecondaryInvariant,PolynomialRing):= (secondInvariant,R)->(
    
    pol:= 0_R;
    for i to #secondInvariant -1 do(
	
	pol = pol + secondInvariant#i#0*evaluateSpechtPolynomial(secondInvariant#i#1,R);
	);
    pol
    )
    




secondaryInvariants=method(TypicalValue => List)
secondaryInvariants(List,PolynomialRing):=(generatingPermutations,R)-> (

n := numgens(R);
p:=partitions(n);
m:= 0;
total:=0;
timeStamp1:= cpuTime();
group:=generatePermutationGroup(generatingPermutations);
Sec:=new MutableList from (n!)//#group:0;

timeStamp2:= cpuTime();
print("Generate group");
print(timeStamp2-timeStamp1);
for i to #p-1 do(
	timeStamp1 = cpuTime();
	multiplicity:= representationMultiplicity(group,i);
	
	timeStamp2 = cpuTime();
	print("Calculate representation multiplicity");
	print(timeStamp2-timeStamp1);
	print(p#i,"Rank",multiplicity);
    	
	
	m2:=m;
	if  multiplicity!=0 then (
	    
	    timeStamp1 = cpuTime();
	    standard:=standardTableaux(p#i);
	    total= total+multiplicity*standard#length;
	    
	    print("Total:",total);
	    timeStamp2 = cpuTime();
	    print("Ambient Dimension",standard#length);
	    print(timeStamp2-timeStamp1);
	    
	    print("SpechtPolynomials");
	    timeStamp1 = cpuTime();
	    --spechtPolynomials:=generateHigherSpechtPolynomials(p#i,standard,R);
	    timeStamp2 := cpuTime();
	    print(timeStamp2-timeStamp1);
	    if(multiplicity!= standard#length) then (
	    	V:=(coefficientRing R)^(standard#length);
		--print(timeStamp2-timeStamp1);
	   	for j to #generatingPermutations-1 do(
	    	    timeStamp1 = cpuTime();
		    matrixRep:= matrixRepresentation(generatingPermutations#j,standard);
		    testMatrixRepresentation(generatingPermutations#j,standard,R);
		    --print(matrixRep);
		    timeStamp2:= cpuTime();
		    print("Matrix representation",generatingPermutations#j);
		    print(timeStamp2-timeStamp1);
		    
		    timeStamp1 = cpuTime();
		    V=intersect(V,ker(matrixRep-id_(source(matrixRep))));
		    timeStamp2 = cpuTime();
		    print("Calculate kernel and intersect vector spaces");
		    print(timeStamp2-timeStamp1);
	   
		    );    
		timeStamp1 = cpuTime();
	    	gen:=generators(V);
	       	testInvariance(generatingPermutations,gen,standard,R);
		if(not multiplicity==numColumns(gen)) then (
		    print(multiplicity,numColumns(gen));
		    error  "Secondary invariants do not match"
		    
		    );
	    	for j to numRows(gen)-1 do(
	    	    for k to numColumns(gen)-1 do(
	    	    	col:= flatten entries gen_{k};
		    	Sec#m = col;
	    	    	Sec#m = secondaryInvariant(col,standard,getTableau(standard,j));
		    	m=m+1;
			--print(Sec#(m-1),m);
	    	    	);    
		    );
	    	timeStamp2 = cpuTime();
		print("Save polynomials");
		print(timeStamp2-timeStamp1);
		)
	    	
	    else (
		timeStamp1 = cpuTime();
		for j to standard#length-1 do(
	    	    for k to standard#length-1 do(
		   	Sec#m = secondaryInvariant(spechtPolynomial(getTableau(standard,j),getTableau(standard,k)));
	           	m=m+1;
		--	print(Sec#(m-1),m,"Complete");
	    	    	);
		    );
		timeStamp2= cpuTime();
		print("Save polynomials 2");
		print(timeStamp2-timeStamp1);
		);
	    	
	    );
	    --print("Saved polynomials:", m-m2);
    );
Sec
)

testInvariance = method()
testInvariance(List,Matrix,TableauList,PolynomialRing):= (lista,polynomials,standard,R)->(
    
    for i to #lista-1 do(
	for j to numColumns polynomials -1 do (
	    polynomial:= vectorToPolynomial(polynomials_{j},standard,R);
	    if permutePolynomial(R,lista#i,polynomial) != polynomial then (
		print(polynomial,lista#i);
	    	error "El polinomio no es invariante";
		);
	    );
	);
    true
)



vectorToPolynomial = method()
vectorToPolynomial(Matrix,TableauList,PolynomialRing) := (vector, stand, R)->(
   
   polynomial:= 0_R; 
   for i to numRows vector -1 do (
       if vector_(i,0)!= 0 then (
	    y := youngTableau(stand#partition,stand#matrix^{i});
	    polynomial = polynomial + vector_(i,0)*generateSpechtPolynomial(y,R);
	   );
       );
   value polynomial
) 


testMultiplicity = method()
testMultiplicity(List) := generatingPermutations->(
    n := #generatingPermutations#0;
    p:= partitions n;
    total:= 0;
    group:=generatePermutationGroup(generatingPermutations);
    
    for i to #p-1 do(
    	multiplicity:= representationMultiplicity(group,i);
	stand:= standardTableaux p#i;
	print("Ambient", p#i,"Dimension",stand#length,"Rank", multiplicity);
	total = total + multiplicity*stand#length;
	);
    print(total, n!/#group);
    total == n!/#group
    ) 

----
--Change the algorithms that make the list of tableaux according to this findings.
----

---
    
 testGraphPermutations = method()
 testGraphPermutations(PolynomialRing):=(R)->(
     G:= {{5,1,8,3,4,0,7,6,2,9},{4,0,1,2,3,7,8,9,5,6}};
     --testMultiplicity(G);
     secondaryInvariants(G,R)
     )
 
 
 printSpechtPolynomial = method()
 printSpechtPolynomial(YoungTableau,YoungTableau, PolynomialRing):= (S,T,R) -> (
     
     print monomialGenerator(S,T,R);
     factor(generateHigherSpechtPolynomialRobust(S,T,R))
     )


testStraigh = method()
testStraigh (PolynomialRing) := (R) -> (
    
    n:= numgens R;
    p := partitions n; 
    for i to #p-1 do( 
    	standard:= standardTableaux(p#i);
	perm := permutations n;
    	for j to #perm -1 do(
	    testMatrixRepresentation(perm#j,standard,R);
	    );
    	);
    true
    )


testStraigh (PolynomialRing,Partition) := (R,p) -> (
    
    n:= numgens R;
    	standard:= standardTableaux(p);
	perm := permutations n;
    	for j to #perm -1 do(
	    testMatrixRepresentation(perm#j,standard,R);
	    );
    true
    )