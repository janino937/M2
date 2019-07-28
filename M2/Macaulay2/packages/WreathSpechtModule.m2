load-- -*- coding: utf-8 -*-
newPackage(
        "WreathSpechtModule",
        Version => "1.5", 
        Date => "Apr 6, 2017",
        Authors => {{Name => "Jonathan Niño", 
                  Email => "ja.nino937@uniandes.edu.co", 
                  HomePage => "http://www.uniandes.edu.co"}
                  },
        Headline => "Methods for the Efficient Compution of Invariants for Permutation Groups.",
        DebuggingMode => true,
	PackageExports => {"SpechtModule"})
		


export {"PartitionTuple"}		
export {"partitionTuple"}
export {"partitionSize"}
export {"partitionTuples"}
export {"YoungTableauTuple"}
export {"youngTableauTuple"}
export {"TableauTupleList"}
export {"tableauTupleList"}
export {"shape"}
export {"tableauToList"}
export {"setPartitions"}
export {"toSetPartition"}
export {"standardTableauTuples"}
export {"naturalStandardTableauTuples"}
export {"matrixRepresentationWreath"}
export {"addTableauTuple"}
export {"getTableauTuple"}
export {"conjugacyClassSize"}
---
--YoungTableau
---y

-- YoungTableau: A new type that efficiently represents a filling of a Young Tableau.
-- The implementation is done in top of the type MutableHashTables.
-- Its local variables are
--     Partition: The partition that gives the shape of the graph. For example the partition 
--{1,2,2} of 5 would give rise to a Young Tableau whows first rows are of length 2 and
-- the last if of length 1.
--    Index: An object for implementing walks on the Young Tableau. The index consist of
--   three numbers (r,c,i) where r represents the row of the element, c corresponds to the
--  the column and i corresponds to the position of the element if the Tableau is read
--  by rows.
-- The numbers are saved as elements in the hast table whos keys are given by the number i
-- in the index above.     
---   



--Constructors


PartitionTuple = new Type of List
partitionTuple = method()
partitionTuple List := lst -> (
    for i to #lst -1 do(
	if class lst#i =!= Partition then error "Array elements are not Partitions";
	);
    new PartitionTuple from lst
    )
	 
partitionSize = method()
partitionSize PartitionTuple := parti -> (
    s:= 0;
    for i to #parti-1 do(
	s = s+sum toList parti#i;    
    );
s
) 


-------
-- Methods
-------

partitionTuples = method()
partitionTuples (ZZ,ZZ) := (n,r) -> (
        
    comps:=compositions(r,n);
    len:= 0;
    result:= {};
    for i to #comps-1 do(
	
	comp:= comps#i;
	partiProducts:={partitionTuple({})};
	for j to r-1 do(
    
	    parti:= reverse partitions comp#j;
	    partiProductsTemp:= new MutableList;	    
	    len:=0;
	    for k to #partiProducts-1 do (
	    	
		for l to #parti-1 do(
		    partiProductsTemp#len = append(partiProducts#k,parti#l);
		    len = len+1;
		    );
		);
	    partiProducts = toList partiProductsTemp;
	    );
	result =join(result ,partiProducts);
	);
    result
    )


conjugacyClassSize = method()
conjugacyClassSize PartitionTuple := p-> (
    
    n:= partitionSize p;
    prod:=1;
    r:=#p;
    for i to r -1 do(
	
	if(#(p#i) != 0) then (
	    p2 := differentElementsInPartition(p#i);
    	    base := keys(p2);
    	    for j to #(base)-1 list prod do (prod = prod*((base#j)^(p2#(base#j)))*(p2#(base#j))!);
    	    );
	
	);
    
    numCycles:= sum (0..(#p-1), i-> #(p#i)) ;
    (r)^(n - numCycles)*(n)!//prod	
    ) 

YoungTableauTuple = new Type of List
youngTableauTuple = method(TypicalValue => YoungTableauTuple)
youngTableauTuple List := lst -> (
    for i to #lst -1 do(
	if class lst#i != YoungTableau then error "Array elements are not 
	Partitions";
	);
    new YoungTableauTuple from lst
)

youngTableauTuple (PartitionTuple,List):= (parti,lst) -> (
    
    suma:= 0;
    result := new MutableList;
    for i to #parti-1 do(
	partSize:= sum toList parti#i;
	y := youngTableau(parti#i,lst_{suma..suma+partSize-1}); 
	result#i=y;
	suma = suma+partSize;
	);
    new YoungTableauTuple from result
    )


shape = method()
shape YoungTableauTuple := tableau -> (

    partitionTuple apply(tableau, tab-> tab#partition) 
    );
    
------
-- Methods for object tableau
------


printTableau YoungTableauTuple := tableau ->(
  matrixArray := new MutableList;
  for r to #tableau-1 do(  
    matrix:= mutableMatrix(QQ,#(tableau#r#partition),tableau#r#partition#0);
    for i to numRows (matrix) -1 do(
    	row:= getRow(tableau,i);
	for j to #row-1 do(
	    matrix_(i,j)= row#j;    
	);	
    );
    matrixArray#r = matrix; 
  );
    print(toList matrixArray)
)





------
-- TableauList
------

   
--  This object represents a list of young tableaus. The tableaus are store in an d times n
-- mutable matrix where d is a bound for the numbers of tableaus and n is the size of the
-- Its variables are
-- Matrix: The matrix that stores the tableau
-- Partition: The partition that gives the shape of the Young diagram
-- Length: The numbers of Young Tableus store in the list.

--An advantege of this storages methods is that the tableau is represented as the permutation
-- that would be necessary to get that tableau.

-- This is useful to calculate things like the Specht polynomials.


-- Constructors

TableauTupleList = new Type of MutableHashTable
tableauTupleList = method()
tableauTupleList PartitionTuple := p-> (
lista := new TableauTupleList;
lista#partition = p;
lista#matrix = mutableMatrix(ZZ, (partitionSize p)!,partitionSize p);
lista#length = 0;
lista
)

tableauTupleList (PartitionTuple,ZZ) :=( p,n)-> (
lista := new TableauTupleList;
lista#partition = p;
lista#matrix = mutableMatrix(ZZ,n ,partitionSize p);
lista#length = 0;
lista
)


-- Methods

------
-- Prints the young diagrams that are store in the list.
------

printTableaux(TableauTupleList):= lista -> (
    
    result:= new MutableList;
    for k to lista#length-1 do(
	tableau1:= getTableau(lista,k);
	
	matrix1:= mutableMatrix(QQ,#(tableau1#partition),tableau1#partition#0);
    	l:= new MutableList;
	for r to #tableau1 do(
	for i to numRows (matrix1)-1 do(
    	    row:= getRow(tableau1,i);
	    for j to #row-1 do(
	    	matrix1_(i,j)= row#j;    
		);	
    	    );
	l#r = matrix1;
	);
    	result#k = toList l;
    );
    print("");
    print(toList result);
)

------
-- Adds a tableau to the list    .
------

addTableauTuple = method()
addTableauTuple(TableauTupleList, YoungTableauTuple):= (tableaux, tableau) ->(
   scan(0..sum(partitionSize tableaux#partition)-1, i-> (tableaux#matrix)_(tableaux#length,i) = tableau#i);
   tableaux#length = tableaux#length+1;
   tableaux
)

addTableauTuple(TableauTupleList,List):= (tableaux,tableau)->(
   scan(0..(partitionSize tableaux#partition)-1, i-> (tableaux#matrix)_(tableaux#length,i) = tableau#i);
   tableaux#length = tableaux#length+1;
   tableaux
    )

------
-- Retrieves a tableau from the list
------
getTableauTuple = method()
getTableauTuple(TableauTupleList,ZZ) := (tableaux, n) -> (
    youngTableauTuple(tableaux#partition,flatten entries tableaux#matrix^{n})
   ) 


naturalStandardTableauTuples = method()
naturalStandardTableauTuples (PartitionTuple):= p -> (
    
    siz:= product(0..#p-1,i-> hookLengthFormula(p#i));
    nums:= 0..(partitionSize p);
    tableaux  := tableauTupleList(p,siz);
    tableauFactors := apply(0..#p-1,i-> (standardTableaux p#i));
    
    tabs:= {{}};
    suma:=0;
    for r to #p-1 do (
	tabs2:= new MutableList;
	len:= 0;
	if(tableauFactors#r#length != 0) then(
	for i to #tabs -1 do (
	    
	    for j to tableauFactors#r#length-1 do (
		row:=  changeLabels(flatten entries tableauFactors#r#matrix^{j},toList (suma..(suma+sum toList p#r -1)));
		tabs2#len = join(tabs#i,row);
		len=len+1;
		);
	    );
	tabs= toList tabs2;
       	);
	print(r,tabs);
	suma = suma+sum toList p#r;
	);
    tableaux#matrix = matrix(tabs);
    tableaux#length = siz;
    tableaux 
    )


standardTableauTuples= method()
standardTableauTuples (PartitionTuple) := parti ->
(
    composition:= apply(toList(0..#parti-1), i-> sum toList parti#i);
    transversals:= setPartitions(composition);
    naturals:= naturalStandardTableauTuples(parti);
    tableaux:= tableauTupleList(parti,naturals#length*#transversals);
    for i to #transversals -1 do(
	
	for j to naturals#length-1 do(
	     addTableauTuple(tableaux,(flatten transversals#i)_(toList flatten entries naturals#matrix^{j}));
	    );
	);
    tableaux
)

setPartitions  = method(TypicalValue => TableauList)
setPartitions(List) := composition->(
    size:=sum composition;
    nums:= toList (0..(size-1));
    partis := subsets(nums,composition#0);
    partis = apply(0..#partis-1, i-> {partis#i});
    for c from 1 to #composition-1 do(
	
	partsInter := new MutableList;
	len:=0;
	for i to #partis-1 do (
	    
	    pool := toList set(nums) - set(flatten partis#i);
	    s:= subsets(pool,composition#c);
	    
	    for j to #s-1 do(
	    	partsInter#len = append(partis#i,s#j);  	
		len = len+1;
		);
	    
	    );
	partis = toList partsInter; 
	);
    partis
)


setPartitions(PartitionTuple) := parti->(
    composition:= apply(toList(0..#parti-1), i-> sum toList parti#i);
    size:=sum composition;
    nums:= toList (0..(size-1));
    partis := subsets(nums,composition#0);
    partis = apply(0..#partis-1, i-> {partis#i});
    for c from 1 to #composition-1 do(
	
	partsInter := new MutableList;
	len:=0;
	for i to #partis-1 do (
	    
	    pool := toList set(nums) - set(flatten partis#i);
	    s:= subsets(pool,composition#c);
	    
	    for j to #s-1 do(
	    	partsInter#len = append(partis#i,s#j);  	
		len = len+1;
		);
	    
	    );
	partis = toList partsInter; 
	);
    partis
)


toSetPartition = method()
toSetPartition(List, PartitionTuple):=(perm ,parti ) -> (
    	
    composition:= apply(toList(0..#parti-1), i-> sum toList parti#i);
    result:= new MutableList;
    suma:= 0;
    for i to #composition-1 do(
	result#i = sort perm_{suma..(suma-1+composition#i)};
	suma = suma+composition#i;
	);
    toList result
    )


toBarCode = method()
toBarCode(List, PartitionTuple):=(perm ,parti ) -> (
    	
    composition:= apply(toList(0..#parti-1), i-> sum toList parti#i);
    result:= new MutableList;
    suma:= 0;
    for i to #composition-1 do(
	result#i =  perm_{suma..(suma-1+composition#i)};
	suma = suma+composition#i;
	);
    toList result
    )


matrixRepresentationWreath = method()
matrixRepresentationWreath(Sequence,PartitionTuple)  := (seq,parti) -> (
    
    transversals:= setPartitions(parti);
    len:= #transversals*product(0..(#parti-1),i-> hookLengthFormula(parti#i));
    resultMatrix:= mutableMatrix(CC,len,len);
    
    for i to #transversals-1 do (
	
	cycle := seq#0_(flatten transversals#i);
	perm:= seq#1_(flatten transversals#i);
	nonZeroBlock:= toSetPartition(perm,parti);
	perm = (inversePermutation flatten nonZeroBlock)_perm;
	suma:= 0;
        permParts:= toBarCode (perm, parti) ;
	localMatrix:= matrix (CC,{{1}});
	for j to #parti-1 do (
	    localPerm:= apply(permParts#j,i-> i -suma);
	    suma = suma+ sum toList parti#j;
	    if(#(permParts#j) != 0) then (
	    	localMatrix = localMatrix**matrixRepresentation(localPerm,standardTableaux parti#j);
	    	);
	    );
	cycleParts:= toBarCode(cycle,parti);
	
	cycleRepNumber:= 1;
	for j from 1 to #parti -1 do (
	    
	    cycleRepNumber = cycleRepNumber* product(0..(#(cycleParts#j)-1),(k)-> (cycleParts#j#k)^j );
	 );   
	
       	localMatrix = cycleRepNumber*matrix(CC,entries localMatrix);
        block:= position(transversals, x->x== nonZeroBlock);
	for j to numRows localMatrix-1 do(
	    for k to numColumns localMatrix-1 do (
		resultMatrix_(j+(numRows localMatrix)*i,k+(numColumns localMatrix)*block)=localMatrix_(j,k);
		);
	    );
      	);
    	matrix(resultMatrix)
    )

          