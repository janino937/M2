load-- -*- coding: utf-8 -*-
newPackage(
        "SpechtPolynomials",
        Version => "1.5", 
        Date => "Apr 5, 2019",
        Authors => {{Name => "Jonathan Niño", 
                  Email => "ja.nino937@uniandes.edu.co", 
                  HomePage => "http://www.uniandes.edu.co"}},
        Headline => "Methods for the Efficient Compution of Invariants for Permutation Groups.",
        DebuggingMode => true,
	PackageExports => {"SymmetricCharacterTable","SpechtModule","WreathSpechtModule"}
	
        )
    
export {"generateHigherSpechtPolynomialRobust"}
export {"generateSpechtPolynomial"}
export {"schurPolynomial"}
export {"permutePolynomial"}
export {"mapiPolynomial"}
export {"generateHigherSpechtPolynomial"}
export {"higherSpechtPolynomials"}
export {"monomialGenerator"}
export {"characterRepresentationMonomial"}
export {"evaluateSpechtPolynomial"}
export {"SpechtPolynomial"}
export {"spechtPolynomial"}
export{"testStraighteningAlgorithm"}
export {"tStraighteningAlgorithm"}
export {"testMatrixRepresentation"}
-----
-- This method codes 
-----
permutePolynomial = method()
permutePolynomial(PolynomialRing,List,Thing) := (R,perm, poly)->(
    genList:= apply(perm,i->R_(i) );
    F := map(R,R,matrix{genList});
    F(poly)
)

-----
-- This method codes 
-----
generateSpechtPolynomial=method()
generateSpechtPolynomial(YoungTableau,PolynomialRing):=(tableau, R)->(
    numCols:= tableau#partition#0;
    polyn := 1_R;
    for i to numCols-1 do(
    	col:= getColumn(tableau,i);
	polyn = polyn *(vandermondeDiscriminant(col,R));
	
    );
    polyn  
)

generateHigherSpechtPolynomial = method()
generateHigherSpechtPolynomial(YoungTableau,YoungTableau,PolynomialRing) := (S,T,R)->(
      generateSpechtPolynomial(T,R)*mapiPolynomial(S,T,R)
      --error "generating polynomials";
)

generateHigherSpechtPolynomial(YoungTableauTuple,YoungTableauTuple,PolynomialRing) := (S,T,R)-> (
    
    pol := 1_R;
    monomial := monomialGenerator(S,T,R);
    for i to #S-1 do(
	if(sum toList S#i#partition != 0) then (
	pol = pol*generateHigherSpechtPolynomialRobust(monomial#i,T#i,R);
	);
    );
    
    pol = pol*characterRepresentationMonomial(T,R) ;
    pol
    )


-- Returns the monomial which corresponds to the character representation component of
-- the irreducible representation
characterRepresentationMonomial = method()
characterRepresentationMonomial(YoungTableauTuple,PolynomialRing) := (T,R) -> (
    monomial:= 1_R;
    for i from 1 to #T-1 do(
	for j to sum toList T#i#partition -1 do(
	    monomial = monomial*R_(T#i#j)^i
	    );
	
	);
    monomial
    )




-----
-- This method codes 
-----
higherSpechtPolynomials = method(TypicalValue => Matrix)
higherSpechtPolynomials (TableauList, PolynomialRing) := ( standard,R)-> (
    
    sol := new MutableHashTable;
    for i to standard#length -1 do (
    	for j to standard#length -1 do(
            sol#(i,j) = generateHigherSpechtPolynomial(getTableau(standard,i),getTableau(standard,j),R);
        );
    );
    sol
)

higherSpechtPolynomials (Partition , PolynomialRing) := (parti, R)-> (
    
    standard := standardTableaux parti;
    sol := new MutableHashTable;
    for i to standard#length -1 do (
    	for j to standard#length -1 do(
            sol#(i,j) = generateHigherSpechtPolynomial(getTableau(standard,i),getTableau(standard,j),R);
        );
    );
    sol
)


higherSpechtPolynomials(TableauTupleList,PolynomialRing):= (standard, R)-> (
    
    sol := new MutableHashTable;
    for i to standard#length -1 do (
    	for j to standard#length -1 do(
            sol#(i,j) = generateHigherSpechtPolynomial(getTableauTuple(standard,i),getTableauTuple(standard,j),R);
        );
    );
    sol 
    
    )

--
-- Gives the list of higher specht polynomials which correspond to the irreducible
-- partition indexed by the partition tuple list.
--

higherSpechtPolynomials(PartitionTuple,PolynomialRing):=(parti,R)-> (
    
      sol := new MutableHashTable;
      standard := standardTableauTuples parti;
      for i to standard#length -1 do (
    	for j to standard#length -1 do(
            sol#(i,j) = generateHigherSpechtPolynomial(getTableauTuple(standard,i),getTableauTuple(standard,j),R);
        );
    );
    sol 
    
     
)

schurPolynomial = method()
schurPolynomial(Partition, PolynomialRing, List) := (parti, R, labels)-> (
    
    ans:= 1_R;
    if #parti>0 then (	
 	
	semistandard:= semistandardTableaux(parti,#labels);
	ans= 0_R;
	for k to semistandard#length-1 do(
	     mono:= 1_R;
	     for l to sum toList parti -1 do(
		  mono = mono*R_(labels#(semistandard#matrix_(k,l)));
		  );
	     --print(mono);
	     --printTableau(getTableau(semistandard,k));
	     ans = ans+mono;
	     );
      );
      ans
  )

-----
-- This is the division of the HigherSpechtPolynomial over SpechtPolynomial
----
mapiPolynomial = method()
mapiPolynomial(YoungTableau,YoungTableau,PolynomialRing):=(S,T,R)->(
    
    degreesTab := indexTableau(S);
    rowPermutations :=  generalizedTableaux(degreesTab);
    --printTableaux(rowPermutations);
    sumPolynomial := 0_R;
    for i to rowPermutations#length-1 do(
	
	indTableau := getTableau(i,rowPermutations);
	sign := orderColumnsTableau(indTableau);
	--printTableau(indTableau);
	fact:= 1_R;
	for j to (indTableau#partition#0)-1 do(
	    columnS:= getColumn(indTableau,j);
	    columnT:= getColumn(T,j);
	    
	    diffe:= new MutableList from {};
	    l:=0;
	    for k to #columnS-1 do(
		
		if(columnS#k-k>0) then (
		   diffe#l= columnS#k-k;
		   l=l+1;
		   );
		);
	   -- print toList diffe;
	    parti:= new Partition from reverse toList diffe;
	    --print columnS;
	    --print(parti);
	    schur:=schurPolynomial(parti,R,columnT);
	    fact = fact*schur;
	    );
	--printTableau(indTableau);
	--print(fact);	     
	sumPolynomial = sumPolynomial+sign*fact;
    );
    sumPolynomial
)

-----
-- This method codes 
-----
vandermondeDiscriminant=method()
vandermondeDiscriminant(List,PolynomialRing):=(lista,R)->(
    polyn:=1_R;
    for i to #lista-1 do(
    	for j from i+1 to #lista-1 do(
	    polyn = polyn*Product(R_(lista#j)-R_(lista#i))
        );
    );
    polyn
)


generateHigherSpechtPolynomialRobust = method(TypicalValue => Matrix)
generateHigherSpechtPolynomialRobust (YoungTableau,YoungTableau, PolynomialRing) := (S,T,R)-> (

    fc:= columnStabilizer T;
    fr:= rowStabilizer T;
    --print ("Stabilizers ok");
    mono:= monomialGenerator(S,T,R);
    --print(mono);
    poly:= 0_R;
    for i to #fr-1 do(
        for j to #fc-1 do(
            comp:=(fc#j)_(fr#i);
            --print (fc#j,fr#i, comp);
            --print poly;
            poly=poly+signPermutation(cycleStructure(fc#j))*(permutePolynomial(R,comp,mono));
                    
            );
            --print poly;
        );
        --poly = poly/(coefficient((monomials poly )_(0,0),poly));
	poly
        
)

generateHigherSpechtPolynomialRobust (Thing,YoungTableau, PolynomialRing) := (monomial,T,R)-> (

    
    fc:= columnStabilizer ( T,numgens R) ;
    fr:= rowStabilizer (T,numgens R);
    --print ("Stabilizers ok");
    mono:= monomial;
    --print(mono);
    poly:= 0_R;
    for i to #fr-1 do(
        for j to #fc-1 do(
            comp:=(fc#j)_(fr#i);
            --print (fc#j,fr#i, comp);
            --print poly;
            poly=poly+signPermutation(cycleStructure(fc#j))*(permutePolynomial(R,comp,mono));
                    
            );
            --print poly;
        );
        --poly = poly/(coefficient((monomials poly )_(0,0),poly));
	poly
        
)



SpechtPolynomial = new Type of MutableHashTable;
spechtPolynomial = method()



spechtPolynomial(YoungTableau, YoungTableau):= (tableauS,tableauT)->(
    
    specht := new SpechtPolynomial;
    specht#0 = tableauS;
    specht#1 = tableauT;
    specht
)
evaluateSpechtPolynomial = method()
evaluateSpechtPolynomial(SpechtPolynomial,PolynomialRing) := (specht,R) ->
(
    generateHigherSpechtPolynomial(specht#0,specht#1,R)
    )



-----
-- This method codes 
-----
monomialGenerator =method()
monomialGenerator (YoungTableau, YoungTableau, PolynomialRing) :=  (tableauS, tableauT, R) -> (
    
    prod:= 1_R;
    if(numgens R == sum(toList tableauS#partition) and numgens R == sum(toList tableauT#partition) and tableauS#0 == tableauT#0 ) then(
        
        rec:= new MutableList;
        base:= new MutableList;
	
        
        rec#(sum(toList tableauS#partition)-1)=0;
        ind:=0;
        for i to (tableauS#partition#0)-1 do (
            col1 := getColumn(tableauS,i);
            col2 := getColumn(tableauT,i);
            if(#col1 == #col2) then (
                for j from 0 to #col1-1 do (
                    rec#ind = col1#(-j-1);
                    base#ind = col2#(-j-1);
                    ind= ind+1;
                );
            ) else error "YoungTableaux dimensions do not match";
        );
    	--print("First loop ok");
        ind = 0;
        m := 0;
	--print(toList rec);
	--print(toList base);
        while m < sum(toList tableauS#partition) do(
            for i to #rec -1 do(
                if(rec#i == m) then (
                    m = m+1;
                    prod = prod*R_(base#i)^ind;
                    )
            );
            ind = ind +1;
        );
    ) else
    (
        error "The numbers of generators of the ring do not match the size of the tableau";
    );
    prod
)

-- Generates the monomial from the tableau tuples  S and T

monomialGenerator (YoungTableauTuple, YoungTableauTuple, PolynomialRing) :=  (tableauS, tableauT, R) -> (
    r:=#tableauS;
    prod:=new MutableList;
    rec:= new MutableList;
    base:= new MutableList;
    expo:= new MutableList;
    
	     
        rec#((numgens R)-1)=0;
        prod#(#tableauS-1)=0;
	ind:=0;
	for k to #(tableauS)-1 do (
	        
	    numCols:= 0;
	    if sum toList tableauS#k#partition != 0 then numCols = tableauS#k#partition#0;
	    for i to (numCols)-1 do (
            	col1 := getColumn(tableauS#k,i);
            	col2 := getColumn(tableauT#k,i);
            	if(#col1 == #col2) then (
                    for j from 0 to #col1-1 do (
                    	rec#ind = col1#(-j-1);
                    	base#ind = col2#(-j-1);
                    	ind= ind+1;
                    	);
            	    ) else error "YoungTableaux dimensions do not match";
            );
	);
    	--print("First loop ok");
        ind = 0;
        m := 0;
       	
	print(toList rec);
	print(toList base);
        
	expo#((numgens R)-1)=0;
	
	while m < numgens R do(
            
	    for i to #rec -1 do(
                if(rec#i == m) then (
                    m = m+1;
                    expo#i = ind;
                    )
            );
            ind = ind +1;
        );
    	ini:=0;
    	for i to #tableauS -1 do (
	    prod#i = 1_R;
	    for j from ini to ini+sum(toList tableauS#i#partition)-1 do (
	    	    prod#i = prod#i*R_(base#j)^(r*expo#j);	
		); 
	    ini = ini+sum(toList tableauS#i#partition);   
	);
    toList prod
)



testMatrixRepresentation = method()
testMatrixRepresentation(List,TableauList,PolynomialRing):= (perm,standard,R)-> (
    
    for i to standard#length-1 do (
    	perm2 := perm_(flatten entries standard#matrix^{i});
    	
	polynomial := value (generateSpechtPolynomial(youngTableau(standard#partition,perm2),R));
	y:= youngTableau(standard#partition,perm2);
	--printTableau(y);
	lineal := straighteningAlgorithm y;
	ini := 0;
	suma:=0_R;
	for j to #lineal -1 do (
	    suma = suma + lineal#j#1*value (generateSpechtPolynomial(lineal#j#0,R)); 
	    );
	if (suma != polynomial) then (
	    print (perm2);
	    printTableau(getTableau(standard,i));
	    error ("Straightening Algorithm is not calculating the correct polynomial");
	    )
	);
    	true
    )


testStraighteningAlgorithm = method()
testStraighteningAlgorithm(Sequence,MutableList,PolynomialRing):= (tableau,lineal,R)->(
    	original := value (generateSpechtPolynomial(tableau#0,R))*tableau#1;
	suma:= 0_R;
	for j to #lineal-1 do (
	    suma = suma + lineal#j#1*value (generateSpechtPolynomial(lineal#j#0,R)); 
	    );
	if (suma != original) then (
	    printTableau(tableau);
	    error ("Straightening Algorithm is not calculating the correct polynomial");
	    );
    	true
    );

testStraighteningAlgorithm(Sequence,List,PolynomialRing):= (tableau,lineal,R)->(
    	original := value (generateSpechtPolynomial(tableau#0,R))*tableau#1;
	suma:= 0_R;
	for j to #lineal -1 do (
	    suma = suma + lineal#j#1*value (generateSpechtPolynomial(lineal#j#0,R)); 
	    );
	if (suma != original) then (
	    printTableau(tableau);
	    print(suma);
	    print(original);
	    error ("Straightening Algorithm is not calculating the correct polynomial");
	    );
    	true
    );

tStraighteningAlgorithm = method(TypicalValue=> List)
tStraighteningAlgorithm(YoungTableau,PolynomialRing):= (tableau,R) ->(
    
    tableauOriginal:= youngTableau(tableau);
    printTableau(tableauOriginal);   
    sign:= orderColumnsTableau(tableau);
    printTableau(tableauOriginal);
    tableaux:= new MutableList from {(tableau, sign)};
    length:= 1;
    level:= 0;
    while firstRowDescent(tableaux#0#0)<(tableau#partition#0,0)  do( 
	
	print("Level",level);
	printTableau(tableaux#0);
	garnir:= garnirElement(tableaux#0);
	--print(length);
	testStraighteningAlgorithm(tableaux#0,garnir,R);
	newTableaux:= new MutableList from (length-1+#garnir):0;
	i := 1;
	k := 0;
	j := 0;
	   while(i < length or j < #garnir) do(
	   -- print(i,j,k);
	    if (j == #garnir) or ( i < length and columnDominance(tableaux#i,garnir#j) < 0) then (
		
		newTableaux#k = tableaux#i;
		print("Not new");
		printTableau(tableaux#i);
		i=i+1;
		k=k+1;
		) 
	    else if (i == #tableaux) or (j < #garnir and columnDominance(tableaux#i,garnir#j)> 0) then (
		newTableaux#k = garnir#j;
	       	print("new");
		printTableau(garnir#j);
		j=j+1;
		k=k+1;
		
		)
	    else (
		printTableau(tableaux#i);
		printTableau(garnir#j);
		print("Mix");
		coef:= tableaux#i#1+garnir#j#1;
		if ( coef!= 0 ) then (
		    newTableaux#k= (garnir#j#0,coef);
		    printTableau(newTableaux#k);
		   
		    k = k+1;
		    
		    
		    )
	    	else print("Saved", level);
		i = i+1;
		j = j+1;
	    	);
	    );
	length= k;
	level = level+1;
	tableaux = apply(toList (0..k-1), i-> newTableaux#i);
	testStraighteningAlgorithm((tableauOriginal,1),tableaux,R);    	
	
	); 
    tableaux 
    )


