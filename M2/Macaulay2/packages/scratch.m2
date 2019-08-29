
path = append(path,"~/M2/M2/Macaulay2/packages")

loadPackage("SpechtModule",FileName => "~/M2/M2/Macaulay2/packages/SpechtModule.m2",Reload => true)
loadPackage("SpechtModule",FileName => "~/SpechtModule.m2",Reload => true
loadPackage("SpechtModule",Reload => true)
charac = characterTable 5
p1 = new Partition from {1,1,1,1,1}
p2 = new Partition from {2,1,1,1}
charac_(p1,p2)


y = youngTableau( p ,{2,3,4,0,1})
e = spechtModuleElement(y,1)
sortColumnsTableau e
e
g = garnirElement (y,1)
e = straighteningAlgorithm (y,1) 
y= youngTableau( p ,{1,2,0,4,3})
g = garnirElement (y,1)
e = straighteningAlgorithm (y) 


p = new Partition from {3,2}
stan = standardTableaux p
permutation = {1,2,3,4,0}
perm2 = permutation_(flatten entries stan#matrix^{0})

y2 =  youngTableau (p,perm2)
garnirElement y2
straighteningAlgorithm y2

M =matrixRepresentation ({1,2,3,4,0},stan)
M1 =matrixRepresentation ({4,1,2,3,0},stan)
M * M2
p2 = conjugacyClass {1,2,3,4,0}
charac_(p,p2)


sortColumnsTableau y2
y2







p = new Partition from {3,2,2,1}
y = youngTableau( p ,{1,0,2,3,4,5,6,7})
sortColumnsTableau y
y

sort keys e
stan = standardTableaux p  

characterTable 4


------
-- Methods for object tableau
------

changeFilling = method()

-- Assume that the initial values were then numbers from 0 to n-1
-- The labels are given in increasing order

changeFilling(List,YoungTableau):= (labels,tableau)-> (
    tab := youngTableau(tableau);
    tab#values = labels;
    tab
    )


sortPermutationSign = method()
sortPermutationSign(List,List):= (original,sortedList) -> (
    
    sign:= 1;
    
    for i to tableau#partition#0-1 do(
	column:=tableau_i;
	(lista,signColumn):=bubbleSort(column); 
	
	for j to #column-1 do(
	    
	    tableau_(j,i)=lista#j;
	    );
	
	sign = sign*signColumn;
	);
    sign
    )


YoungTableau ? YoungTableau := (tableau1,tableau2)-> (
    
    rowDescentOrder(tableau1,tableau2)
    )


--SpechtModuleTerm = new Type of List

--coefficient SpechtModuleTerm := term -> term#1

--tabloid = method()
--tabloid SpechtModuleTerm := term -> term#0

--net SpechtModuleTerm := term ->(
    
    if coefficient term  == 0 then 0 
    else if coefficient term == 1 then net tabloid term
    else if coefficient term == -1 then "- " | net tabloid term
    else coefficient term | " " |net tabloid term    

)


bubbleSort = method()
bubbleSort(List):= lista ->(
    
    lista = new MutableList from lista;
    sign:=1;
    sorted:= false;
    ini:=0;
    while not sorted do (
	
	sorted= true;
     	if(ini>0) then ini = ini-1;
	for i from ini to #lista-2 do(
	    if(lista#i>lista#(i+1)) then(
		sorted = false;
		temp := lista#i;
		lista#i = lista#(i+1);
		lista#(i+1)= temp;
		sign=sign*(-1);
		);
	    if(sorted) then(
		ini = ini+1;
		
		);   
	    
	    );
	);
    (toList lista, sign) 
    )

bubbleSort(List, MethodFunction):= (lista,compare) ->(
    
    lista = new MutableList from lista;
    sign:=1;
    sorted:= false;
    ini:=0;
    while not sorted do (
	
	sorted= true;
     	if(ini>0) then ini = ini-1;
	for i from ini to #lista-2 do(
	    if compare(lista#i,lista#(i+1))>0 then(
		sorted = false;
		temp := lista#i;
		lista#i = lista#(i+1);
		lista#(i+1)= temp;
		sign=sign*(-1);
		);
	    if(sorted) then(
		ini = ini+1;
		
		);   
	    
	    );
	);
    (toList lista, sign) 
    )

----
--Given an ordered list and a value it returns the index of the value in the list.
----

binarySearch = method(TypicalValue => ZZ)
binarySearch(TableauList,YoungTableau,ZZ):=(standard,val,ini)->(
    
    a := ini;
    b := standard#length;
    c:=a;
    fin:=false;
    if flatten tableauToList(val) == flatten entries standard#matrix^{c} then (
	
	fin = true
	);
    while b-a>1 and  not fin do(
	c= (b+a)//2;
	--print(a,b,c);
	if flatten tableauToList(val) == flatten entries standard#matrix^{c} then (
	    a = c;
	    b = c;
	    fin = true
	    )
	else if flatten tableauToList(val) < flatten entries standard#matrix^{c} then (
	    b = c;
	    )
	else(
	    a = c;
	    );
	
	);
    if not fin then c = -1;
    c
    )
    
   
    for i to standard#length-1 do (
    	perm2 := perm_(flatten entries standard#matrix^{i});
    	y:= youngTableau(standard#partition,perm2);
	--printTableau(y);
	lineal := straighteningAlgorithm y;
	ini := 0;
	for j to #lineal -1 do (
	    
	    ind:= binarySearch(standard,lineal#j#0,ini);
	    --print(lineal#j#0,ind);
	    --printTableau(lineal#j#0);
	    mat_(ind,i)= lineal#j#1;
	    ini = ind+1;
	    );
	);
    matrix(mat)


-----
-- This method codes 
-----
irreducibleSpechtRepresentation = method()
irreducibleSpechtRepresentation(Partition, PolynomialRing) := (parti, R)-> (
    
    lista := new MutableList;
    n:=sum(toList parti);
    perms := permutations(toList(1..n));
    for i to #perms-1 do(
	lista#i = matrixRepresentation(perms#i,parti,R)
    );
    toList(lista)
)

columnDominance(Sequence,Sequence):= (tableau1,tableau2) -> (
    
    ans:= 0;
    if(firstRowDescent tableau1#0 < firstRowDescent tableau2#0) then (
	
	ans=-1;
	)
    else if ( firstRowDescent tableau1#0 > firstRowDescent tableau2#0) then (
	
	ans = 1;
	
	)
    else (
	
	ans = lexicographicalOrder(tableau1#0,tableau2#0)
	
	);
    ans
    )


lexicographicalOrder = method()
lexicographicalOrder(YoungTableau, YoungTableau):=(tableau1,tableau2) ->(
    
    ans:= 0;
    if(toList tableau1#partition != toList tableau2#partition) then
    	error "The tableaus don't have the same partition";
    for i to #(tableau1#partition)-1 when ( ans == 0) do (
    
    	for j to tableau1#partition#i-1 when (ans == 0) do (
	    
	    if tableau1_(i,j) < tableau2_(i,j) then
	    	(ans=-1)
	    else if tableau1_(i,j) > tableau2_(i,j) then
	    	(ans = 1); 
		
	    );
	    	
    	);
	
    ans
    
    )


-----
-- This method codes 
----- 
comparePartitions = method(TypicalValue => ZZ)
comparePartitions(Partition,Partition):=(p,q)->(
ans:=1;
if #p!=#q then ans=0
else ( 
 	for i from 0 to #p-1 do(
		if p#i!=q#i then(ans=0; break )
	);
);
ans
)

-----
-- This method returns all permutations in n letters that permute the entries of
-- column and fixes the entries in all the other columns
-----
columnPermutations = method(TypicalValue =>List)
columnPermutations(YoungTableau,ZZ):= (tableau,col) -> (
    col= tableau_col;
    perms:= permutations(col);
    n := sum(toList tableau#partition);
    apply(perms, p-> extendPermutation(n,p)) 
)


-----
-- This method codes 
-----
rowPermutations = method(TypicalValue =>List)
rowPermutations(YoungTableau,ZZ):= (tableau, row) -> (
    row= tableau^row;
    perms:= permutations(row);
    n := sum(toList tableau#partition);
    apply(perms, p-> extendPermutation(n,p))
)

P:= new MutableList;
   ind:= 0;
   for i from 0 to #L-1 do(
      for j from 0 to #M-1 do(
         P#ind=(L#i)_(M#j);
         ind= ind+1;
      );
   );
    toList P

-----
-- A method which gives a partition as a multiset
-- TODO: Implement with the class MultiSet.
-----
differentElementsInPartition(Partition) := p -> ( 
exponent := new MutableHashTable;
    val := p#0;
    exponent#val = 1;
    for i from 1 to #p-1 do(
        if p#i == val then exponent#val = exponent#val +1
        else (  
                val =p#i;
                exponent#val =1;
            )    
    );
    exponent
)


-----
-- This method codes 
-----
factorial = method(TypicalValue => ZZ)
factorial(ZZ) := n->(if n ==0 then 1 else n*factorial(n-1))

-----
-- A method which gives a partition as a multiset
-- TODO: Implement with the class MultiSet.
-----
differentElementsInPartition = method(TypicalValue => MutableHashTable)
differentElementsInPartition(Partition) := p -> ( 
exponent := new MutableHashTable;
    val := p#0;
    exponent#val = 1;
    for i from 1 to #p-1 do(
        if p#i == val then exponent#val = exponent#val +1
        else (  
                val =p#i;
                exponent#val =1;
            )    
    );
    exponent
)


-----
--  
-----
rowStructure = method(TypicalValue => MutableMatrix)
rowStructure(TableauList):= (tableaux)->(
    M:= mutableMatrix(ZZ, tableaux#length, sum(toList tableaux#partition));
    for i to tableaux#length-1 do (
        r := 0;
        for j to #(tableaux#partition)-1 when (tableaux#partition)#j > 1 do(
            for k to (tableaux#partition)#j-1 do(
                M_(i,(tableaux#matrix)_(i,r+k)-1) = j+1;
            );
            r = r+(tableaux#partition)#j;
        );
    );
    M
)



if(isLastIndex(tableau)) then 
    (
	--Case that the we need to find the only possible number 
        row = (tableau#index)#0;
	col = (tableau#index)#1;
	if(col==0) then (rowNumbers = tally(getRow(original,row)));
	nextIndex(rowNumbers);
	element = getElement(rowNumbers);
	if(notInColumn(tableau,element)) then(
            
	    tableau = addElement(tableau,element);
            tableaux = addTableau(tableaux,tableau);
       )
    ) else
    (
	row = (tableau#index)#0;
	col = (tableau#index)#1;
	if(col==0) then (rowNumbers = tally(getRow(original,row)));
	--change name of row basis
	
	while nextIndex(rowNumbers) != (-1) do (
	    element= getElement(rowNumbers);
            if(notInColumn(tableau,element)) then
            (
		
                tableauNuevo := youngTableau(tableau);
		addElement(tableauNuevo,element);
		rowNumbers2 := tally(rowNumbers);
		--setIndex(rowNumbers2,0);
		rowNumbers2#element = rowNumbers2#element-1;
                tableaux =   recursiveGeneralizedTableaux(original,rowNumbers2,tableauNuevo,tableaux);
            );
        );  
    );
    tableaux

	for j to #(composition#basis)-1 do(
	    k:= (composition#basis)#j;
	    maxNumberOfTableaus = maxNumberOfTableaus//factorial(composition#k);
	       
	);	
    );


------
-- Given a YoungTableau, it iterates its index so that it seats at the next position in the
--tableau. This assumes that the tableau if been read by rows.
------
nextIndex YoungTableau  := tableau->(
    l := tableau#index;
    p := tableau#partition;
    if(p#(l#0)-1==(l#1)) then (l= {l#0+1,0,l#2+1})
    else l = {l#0,l#1+1,l#2+1};
    tableau#index = l;
    tableau
)


------
-- Checks if the index is at the last position in the tableau.
------
isLastIndex = method(TypicalValue => Boolean)
isLastIndex(YoungTableau) := tableau -> (
    l:=tableau#index;
    l#2 ==sum(toList tableau#partition)-1
)

------
-- This method adds an element to the tableau in the position where the index is located
-- and sets the index to the next position.
------
addElement = method(TypicalValue => Boolean)
addElement(ZZ,YoungTableau) := (tableau, n) -> (
    i := tableau#index#2;
    tableau#values#i = n;
    tableau = nextIndex(tableau);
    tableau
)



addElement = method()
addElement (YoungTableau,MutableHashTable,ZZ) := (tableau,ind,e)-> (
    tableau#values#(ind#index) = e;
    p := tableau#partition;
    if p#(ind#row)-1==(ind#column)  then (
	ind#row = ind#row+1;
	ind#column = 0;
	ind#index = ind#index+1)
    else (
	ind#column = ind#column+1;
	ind#index = ind#index+1
	);
    tableau
    )


recursiveSemistandardTableaux(ZZ,YoungTableau,TableauList,HashTable):= (maxNumber, tableau, tableaux,ind) -> (
    if(ind#index == sum toList tableau#partition - 1) then 
    (
	maximum:=maxPossibleNumbersSemistandard(tableau,ind,maxNumber);
	for i from max(previousElementInRow(tableau,ind),0,previousElementInColumn(tableau,ind)+1) to maximum do(
           tableau#values#(ind#index)= i;
           tableaux = addTableau(tableaux,tableau);
	   );
       
    ) else
    (
	newInd:= nextIndex (ind,tableau#partition);
	maximum= maxPossibleNumbersSemistandard(tableau,ind,maxNumber);
        for i from max(previousElementInRow(tableau,ind),0 ,previousElementInColumn(tableau,ind)+1) to maximum do(
        
             
	     tableau#values#(ind#index)= i;
	    -- print(tableauNuevo#index);
	     recursiveSemistandardTableaux(maxNumber,tableau,tableaux,newInd);
        );  
    );
    tableaux
)

recursiveTabloids(List,YoungTableau , TableauList,HashTable):= (numbers, tableau, tableaux,ind) -> (
    if(ind#index == sum toList tableau#partition - 1) then 
    (
       --print(numbers);
       if previousElementInRow(tableau,ind)< numbers#0 then
       ( 
           tableau#values#(ind#index) = numbers#0;
           addTableau(tableaux,tableau);
	   --print net tableau
       )
    ) else
    (
	maximum:= maxPossibleNumber(tableau,ind);
	newInd:= nextIndex (ind,tableau#partition);
      for i from 0 to #numbers-1 when (numbers#i < maximum+1)  do (
        
            if(numbers#i>previousElementInRow(tableau,ind)) then
            (
                --tableauNuevo := youngTableau(tableau);
		
		tableau#values#(ind#index) = numbers#i;
		numbers2 := delete(numbers#i,numbers);
		--print net tableau;
                recursiveTabloids(numbers2,tableau,tableaux,newInd);
            );
        );  
    );
    tableaux
)

recursiveStandardTableaux(List,YoungTableau,TableauList,HashTable):= (numbers, tableau, tableaux,ind) -> (
    if(ind#index == sum toList tableau#partition - 1) then 
    (
       if (previousElementInRow(tableau,ind) < numbers#0) and (previousElementInColumn(tableau,ind) < numbers#0) then
       ( 
           tableau#values#(ind#index) = numbers#0;
           addTableau(tableaux,tableau);
       )
    ) else
    (
	maximum:= maxPossibleNumberStandard(tableau,ind);
        newInd:= nextIndex (ind,tableau#partition);
	for i from 0 to #numbers-1 when (numbers#i < maximum+1)  do (
        
            if(numbers#i>previousElementInRow(tableau,ind) and numbers#i>previousElementInColumn(tableau,ind) ) then
            (
                --tableauNuevo := youngTableau(tableau);
		tableau#values#(ind#index)= numbers#i;
		numbers2 := delete(numbers#i,numbers);
                recursiveStandardTableaux(numbers2,tableau,tableaux,newInd);
            );
        );  
    );
    tableaux
)

------
-- Changes the index to the given index.
------
setIndex(List, YoungTableau) := (L,tableau)->(
    tableau#index = L;
    tableau
)

printTableau = method()
printTableau (YoungTableau,ZZ) := (tableau,n) ->(
    matrix:= mutableMatrix(QQ,#(tableau#partition),tableau#partition#0);
    for i to numRows (matrix) -1 do(
    	row:= getRow(tableau,i);
	for j to #row-1 do(
	    matrix_(i,j)= row#j;    
	);	
    );
    print("");
    print(matrix,n);
)


------
-- Prints two young diagrams . 
------
printTableau(YoungTableau, YoungTableau):= (tableau1, tableau2)-> (
    matrix1:= mutableMatrix(QQ,#(tableau1#partition),tableau1#partition#0);
    for i to numRows (matrix1)-1 do(
    	row:= getRow(tableau1,i);
	for j to #row-1 do(
	    matrix1_(i,j)= row#j;    
	);	
    );
    matrix2:= mutableMatrix(QQ,#(tableau2#partition),tableau2#partition#0);
    for i to numRows (matrix2)-1 do(
    	row:= getRow(tableau2,i);
	for j to #row-1 do(
	    matrix2_(i,j)= row#j;    
	);	
    );
    print("");
    print(matrix1,matrix2);
    
    
    )


next = method()
next YoungTableau:= tableau -> (
    
    ind:= tableau#index;
    ans:= tableau#values#(ind#2);
    nextIndex(tableau);
    )
