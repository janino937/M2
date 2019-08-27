laodload-- -*- coding: utf-8 -*-
newPackage(
        "SpechtModule",
        Version => "1.5", 
        Date => "May 17, 2017",
        Authors => {{Name => "Jonathan Niño", 
                  Email => "ja.nino937@uniandes.edu.co", 
                  HomePage => "http://www.uniandes.edu.co"},
                  {Name => "Juanita Duque", 
                  Email => "a.duque10@uniandes.edu.co", 
                  HomePage => "http://www.uniandes.edu.co"}},
        Headline => "Methods for the Efficient Compution of Invariants for Permutation Groups.",
        DebuggingMode => true
        )
		
		
export {"YoungTableau"}
export {"youngTableau"}
export {"tableauToList"}
export {"listToTableau"}

export {"TableauList"}
export {"tableauList"}
export {"addTableau"}
export {"toListOfTableaux"}

export {"tabloids"}
export {"standardTableaux"}
export {"semistandardTableaux"}
export {"rowPermutationTableaux"}

export {"indexTableau"}

export {"changeFilling"}

export {"hookLengthFormula"}
export {"cycleDecomposition"}
export {"conjugacyClass"}

export {"matrixRepresentation"}

export {"readingWord"}
export {"wordToTableau"}

export {"extendedPermutations"}
export {"directProductOfPermutations"}

export {"columnStabilizer"}
export {"rowStabilizer"}

export {"signPermutation"}

export {"combinations"}
export {"garnirElement"}
export {"orderColumnsTableau"}
export {"cardinalityOfConjugacyClass"}
export {"differentElementsInPartition"}


export{"multinomial"}
export {"straighteningAlgorithm"}

export {"firstRowDescent"}
export {"columnDominance"}

export {"permutationsFixColumn"}
export {"permutationsFixRow"}
export {"productPermutationsList"}
export {"permutationSign"}
export {"rowDescentOrder"}
export {"sortColumnsTableau"}
export {"sortColumn"}

export {"SpechtModuleTerm"}
export {"SpechtModuleElement"}

protect \ {row,column}
---
--YoungTableau
---

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

YoungTableau = new Type of MutableHashTable
youngTableau = method(TypicalValue => YoungTableau)
youngTableau Partition := p -> (
    tableau:= new YoungTableau;
    tableau#partition = p;
    tableau#values = new MutableList from ((sum toList p):0) ;
    tableau
)

youngTableau(Partition,List):= (p,L)->(
    if(sum toList p != #L) then error " Partition size does not match with the length of the list L";
    tableau:= new YoungTableau;
    tableau#partition =p;
    tableau#values = new MutableList from L;
    tableau
)

youngTableau(YoungTableau):= (tableau)->(
    t:= new YoungTableau; 
    for i to #keys(tableau)-1 do t#((keys(tableau))#i) = tableau#((keys(tableau))#i);
    t#values = new MutableList from tableau#values; 
    t      
)

youngTableau(Partition,MutableList):= (p,L)->(
    if(sum toList p != #L) then error " Partition and List size do not match";
    tableau:= new YoungTableau;
    tableau#partition =p;
    tableau#values = L;
    tableau
)

youngTableau(Partition,MutableMatrix):= (p,L)->(
    if(numRows L != 1 ) then error "expected a matrix with one row";
    if(sum toList p != # (flatten entries L )) then error "Partition and List size do not match";
    tableau:= new YoungTableau;
    tableau#partition =p;
    tableau#values = new MutableList from flatten entries L;
    tableau
)

youngTableau(Partition,Sequence):=(p,L)->(
    if(sum toList p != #L) then error " Partition and List size do not match ";
    tableau:= new YoungTableau;
    tableau#partition =p;
    tableau#values = new MutableList from toList L;
    tableau
)

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

------
-- Gives a representation of the Young Tableau as a list of the rows in the
-- diagram.
------
tableauToList = method(TypicalValue => MutableList)
tableauToList(YoungTableau):= (tableau)->(
    
    n:= #(tableau#partition);
    d:=0;
    s:= apply(n,i->(d=d+tableau#partition#i;d));
    s = prepend(0,s);
    L := apply(n,i->(toList tableau#values)_{(s#i..(s#(i+1))-1)}); 
    L
)

listToTableau = method(TypicalValue => YoungTableau)
listToTableau List := l -> (
    
    parti := new Partition from apply (l,i->#i);
    youngTableau(parti,flatten l)
    )

------
-- Gets the element in the position (i,j) of the young diagram.
-- i: row
-- j: column 
------

YoungTableau_Sequence:= (tableau,pos) -> (
    if #pos != 2 then error "expected a sequence of length two"
    
else(
    (i,j) := pos;
    ans:= 0;
    if(i < #(tableau#partition)) then (
        
        if(j < tableau#partition#i) then ( 
            ind := sum (toList tableau#partition)_{0..(i-1)};
            ans = tableau#values#(ind+j);
        )
        else (error "Index out of bounds ");
    
    )
    else( error "Index out of bounds" );
    ans  
    )

)


------
-- Sets the element in the position (i,j) of the young diagram.
-- i: row
-- j: column 
------
YoungTableau_Sequence = (tableau,pos,e)->(
    (i,j):=pos;
    if(i < #(tableau#partition)) then (
        if(j < tableau#partition#i) then ( 
            ind := sum (toList tableau#partition)_{0..(i-1)};
            tableau#values#(ind+j)= e;
        )
        else (error "Index out of bounds ");
    
    )
    else( error "Index out of bounds" );
    e
    
    )

------
-- Gives a list of all the elements in the row i 
------
YoungTableau^ZZ := (tableau,i) -> (
    ans:=0;
    if i < #(tableau#partition) then (
        ind := sum (toList tableau#partition)_{0..(i-1)};
    	ans = (toList tableau#values)_{(ind..(ind + (tableau#partition#i)-1))};   
    )
    else error "Index out of bounds";
    ans
    )

------
-- Gives a list of all the elements in the column i 
------
YoungTableau_ZZ := (tableau,i) -> (
    ans:= 0;
    if -1< i and i < tableau#partition#0 then (
        ind:= 0;
        ans = new MutableList;
        for j to #(tableau#partition)-1 when (tableau#partition#j > i) do(
            ans#j = tableau#values#(ind+i);
            ind = ind+(tableau#partition#j);
        );
        ans = toList ans;
	ans
    )
)


------
-- A method to give a graphical representation of a Young diagram. This method saves the
-- diagram in a mutable matrix and then prints the matrix. 
------
net YoungTableau := tableau ->(
    l := tableauToList tableau;
    corner := #(tableau#partition) ;
    tableauNet:= "|" ;
    for i to corner-2 do tableauNet = tableauNet || "|"; 
    
    for i to (tableau#partition#0)-1 do ( 
	column:= tableau_i;
	columnString := " "|column#0;
	for j from 1 to #column-1 do columnString = columnString|| " "|column#j;
	for j from #column to corner -1 do columnString = columnString || " |" ;
    	corner = #column;
	tableauNet = tableauNet|columnString;
	);
    columnString := " |";
    for i to corner-2 do columnString= columnString || " |"; 
    tableauNet = tableauNet | columnString;
    tableauNet
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

TableauList = new Type of MutableHashTable
tableauList = method(TypicalValue => TableauList)

tableauList Partition :=    p-> (
lista := new TableauList;
lista#partition = p;
lista#matrix = mutableMatrix(ZZ,multinomial(sum(toList p),p),sum(toList p));
lista#length = 0;
lista
)


tableauList (Partition,ZZ) :=    (p,n)-> (
lista := new TableauList;
lista#partition = p;
lista#matrix = mutableMatrix(ZZ,n,sum(toList p));
lista#length = 0;
lista
)



-- Methods

------
-- Prints the young diagrams that are store in the list.
------

toListOfTableaux = method()
toListOfTableaux TableauList := tableaux -> (
    apply(tableaux#length,i-> youngTableau(tableaux#partition,tableaux#matrix^{i}))
    )

------
-- Adds a tableau to the list    .
------
addTableau = method(TypicalValue => ZZ)
addTableau(TableauList,YoungTableau):= (tableaux,tableau) ->(
   scan(0..sum(toList tableau#partition)-1, i-> (tableaux#matrix)_(tableaux#length,i) = tableau#values#i);
   tableaux#length = tableaux#length+1;
   tableaux
)

addTableau(TableauList,List):= (tableaux,tableau) -> (
    scan(0..sum(toList tableaux#partition)-1, i-> (tableaux#matrix)_(tableaux#length,i) = tableau#i);
   tableaux#length = tableaux#length+1;
   tableaux
    )

net TableauList := tableaux -> (
    net toListOfTableaux tableaux
    )

------
-- Retrieves a tableau from the list
------

TableauList_ZZ := (tableaux,n) -> (
     youngTableau(tableaux#partition,flatten entries tableaux#matrix^{n})
    ) 

-- Methods

------
-- Given a tableau with an index, it gets the element thats to the right of the element
-- that the index is pointing to. In case there is no such element (for example when the
-- index points to first element in a row, it return 0)
------
previousElementInRow = method(TypicalValue => ZZ)
previousElementInRow(YoungTableau,HashTable):= (tableau,ind)->(
    
    e := -1;
    if ind#column!=0 then e = tableau#values#(ind#index-1);
    e
)

------
-- Given a tableau with an index, it gets the element thats to above of the element
-- that the index is pointing to. In case there is no such element (for example when the
-- index points to an element in the first row, it return 0).
------
previousElementInColumn = method(TypicalValue => ZZ)
previousElementInColumn(YoungTableau,HashTable):= (tableau,ind)->(
    e:=-1;
    p:= tableau#partition;
    if ind#row!=0 then e = tableau#values#(ind#index-p#(ind#row-1));
    e
)

nextIndex = method()
nextIndex (HashTable,Partition)  := (ind,p)->(
    
    if p#(ind#row)-1==(ind#column)  then (
	ind = hashTable {row => ind#row+1,column => 0, index => ind#index+1 })
    else (
	ind = hashTable {row => ind#row,column => ind#column+1, index => ind#index+1 }
	);
    ind
)

------
-- This method is used in the method that generates the list of tableaux. Given
-- a tableau which has been partially filled with numbers, this method calculates
-- the maximum number which could be put in the next empty slot, so that a valid standard
-- tableau with those numbers exists. 

-- Specifically, this method checks the number of slots that havent been filled in a column.
-- and sums the number of elements which have already been filled in that row.

 
------
maxPossibleNumber = method(TypicalValue => ZZ)
maxPossibleNumber(YoungTableau,HashTable):= (tableau,ind) ->(
  s:=sum(toList tableau#partition)-(tableau#partition)#(ind#row);
  s= s+ind#column;
  s
)



-----
-- Method that generates the list of all tabloids of a given partition.
-- A filling of young diagram is a tableau if it is increasing in rows.
-- The number of tableaux is given by the multinomial coefficient associated to the partition
-- nC(p_1,p_2,..,p_k).
-----
tabloids = method(TypicalValue => TableauList)
tabloids(Partition) := p->(
    size:= multinomial p;
    tableaux :=tableauList(p,size);
    if(size!= 0) then(
    nums := toList(0..sum toList p - 1);
    tableau:= youngTableau(p);
    ind := hashTable {row=> 0, column => 0, index => 0};
    recursiveTabloids(nums,tableau,tableaux,ind);
    );
    tableaux
)


-----
-- A method that calculates the tableaus recursively. In each step the algorith tries filling
-- the tableau with a number in the list of numbers. Then it calls the method again to fill
-- next slot in the tableau this time removing the element that was previoulsy added to the
-- tableau.
-- In this way the method effectively goes through all posible fillings of the tableau.
-- TODO find a way to put the list of numbers and the tableau as a global variable.
-----

--- No need to create a new tableau in each step, just use parameter accumulation
recursiveTabloids = method(TypicalValue => TableauList)

recursiveTabloids(List,YoungTableau , TableauList,HashTable):= (numbers, tableau, tableaux,ind) -> (
    maximum:= maxPossibleNumber(tableau,ind);
    newInd:= nextIndex (ind,tableau#partition);
    for i from 0 to #numbers-1 when (numbers#i < maximum+1)  do (
        
            if(numbers#i>previousElementInRow(tableau,ind)) then
            (
                --tableauNuevo := youngTableau(tableau);
		
		tableau#values#(ind#index) = numbers#i;
		numbers2 := delete(numbers#i,numbers);
		--print net tableau;
                if newInd#index == sum toList tableau#partition then addTableau(tableaux,tableau)
		else recursiveTabloids(numbers2,tableau,tableaux,newInd);
            );
        );  
    tableaux
    )



------
-- This method is used in the method that generates the list of standard tableaux. Given
-- a tableau which has been partially filled with numbers, this method calculates
-- the maximum number which could be put in the next empty slot, so that a valid standard
-- tableau with those numbers exists. 

-- Specifically it counts the numbers of elements in the subdiagram with positions (i,j)
-- Since the element put at this position must be the smallest of all elements in ths diagram.
-- This gives a very good bound on the elements that can go in here.
------
maxPossibleNumberStandard = method(TypicalValue => ZZ)
maxPossibleNumberStandard(YoungTableau,HashTable):= (tableau,ind) ->(
  s:=sum(toList tableau#partition);
  for i from ind#row to #(tableau#partition)-1 when (tableau#partition#i > ind#column ) do (    
     s = s - (tableau#partition#i)+ind#column;
  );
  --s = s+1;
  s
)



-----
-- Method that generates the list of all standard tableaux of a given partition.
-- A filling of young diagram is a tableau if it is increasing in rows and decrasing in
-- columns
-----
standardTableaux = method(TypicalValue => TableauList)
standardTableaux(Partition) := p->(
    size:=sum(toList p);
    tableaux :=tableauList(p,hookLengthFormula(p));
    if size != 0 then(
    nums := toList(0..size-1);
    tableau:= youngTableau(p);
    ind := hashTable {row=> 0, column => 0, index => 0};
    recursiveStandardTableaux(nums,tableau,tableaux,ind);
    );
    tableaux
)

-----
-- A method that calculates the tableaus recursively. In each step the algorith tries filling
-- the tableau with a number in the list of numbers. Then it calls the method again to fill
-- next slot in the tableau this time removing the element that was previoulsy added to the
-- tableau.
-- In this way the method effectively goes through all posible fillings of the tableau.
-- TODO find a way to put the list of numbers and the tableau as a global variable.
-----
recursiveStandardTableaux = method(TypicalValue => TableauList)
recursiveStandardTableaux(List,YoungTableau,TableauList,HashTable):= (numbers, tableau, tableaux,ind) -> (
    maximum:= maxPossibleNumberStandard(tableau,ind);
        newInd:= nextIndex (ind,tableau#partition);
	for i from 0 to #numbers-1 when (numbers#i < maximum+1)  do (
        
            if(numbers#i>previousElementInRow(tableau,ind) and numbers#i>previousElementInColumn(tableau,ind) ) then
            (
                --tableauNuevo := youngTableau(tableau);
		tableau#values#(ind#index)= numbers#i;
		numbers2 := delete(numbers#i,numbers);
                if newInd#index == sum toList tableau#partition then addTableau(tableaux,tableau) 
		else recursiveStandardTableaux(numbers2,tableau,tableaux,newInd);
            );
        );
    tableaux  
)


maxPossibleNumbersSemistandard = method(TypicalValue => ZZ)
maxPossibleNumbersSemistandard(YoungTableau,HashTable,ZZ):= (tableau,ind,n)-> (
    
  s:=n;
  s = s - #(tableau_(ind#column))+ind#row;
  --s = s+1;
  s
    )

semistandardTableaux = method(TypicalValue => TableauList)
semistandardTableaux(Partition,ZZ) := (p,n)->(
    size:=sum(toList p);
    tableaux :=tableauList(p,n^size);
    if size!=0 then (
    nums := toList(0..size-1);
    tableau:= youngTableau(p);
    ind := hashTable {row=> 0, column => 0, index => 0};
    recursiveSemistandardTableaux(n,tableau,tableaux,ind);
    );
    tableaux
)

-----y
-- A method that calculates the tableaus recursively. In each step the algorith tries filling
-- the tableau with a number in the list of numbers. Then it calls the method again to fill
-- next slot in the tableau this time removing the element that was previoulsy added to the
-- tableau.
-- In this way the method effectively goes through all posible fillings of the tableau.
-- TODO find a way to put the list of numbers and the tableau as a global variable.
-----
recursiveSemistandardTableaux = method(TypicalValue => TableauList)
recursiveSemistandardTableaux(ZZ,YoungTableau,TableauList,HashTable):= (maxNumber, tableau, tableaux,ind) -> (
    newInd:= nextIndex (ind,tableau#partition);
    maximum:= maxPossibleNumbersSemistandard(tableau,ind,maxNumber);
    for i from max(previousElementInRow(tableau,ind),0 ,previousElementInColumn(tableau,ind)+1) to maximum do(   
	tableau#values#(ind#index)= i;
	-- print(tableauNuevo#index);
	if newInd#index == sum toList tableau#partition then tableaux = addTableau(tableaux,tableau)
	    else recursiveSemistandardTableaux(maxNumber,tableau,tableaux,newInd);
        );
    tableaux
    )


readingWord = method()
readingWord YoungTableau := tableau -> (
    
    flatten apply (tableau#partition#0, i-> reverse tableau_i)
    )

wordToTableau = method()
wordToTableau (Partition,List) := (p,word)->(
    
    conj := conjugate p;
    suma := 0;
    tableau := youngTableau p;
    for i to #conj-1 do(
	scan(conj#i, j -> tableau_((conj#i)-1-j,i)=word#(suma+j));
	suma = suma+conj#i;
	);
    tableau
    )
    

-----
-- This method calculates i(S) for a given tableau
-----
indexTableau = method()
indexTableau(YoungTableau):= tableau -> (
    
    word := readingWord tableau;
    ind := 0;
    m:=0;
    index := new MutableList;
    while m < sum(toList tableau#partition) do(
        for i to #word -1 do(
            if(word#i == m) then (
                m = m+1;
                index#i = ind;
                )
        );
            ind = ind +1;
        );
    wordToTableau (tableau#partition,toList index)
)



-----
-- Method that generates the list of all row permutations of a tableau that result in no repeated number
-- in any column.
-- An index tableau can have repetitions of the numbers in its slots.
-- The method calculates all the different tableaus that can be obtained by permuting the
-- elements in the rows, in such a way that all elements in the columns are different.
-----
rowPermutationTableaux = method()
rowPermutationTableaux(YoungTableau) := (tableau)->(
    --Assuming all tableaus have size greater or equal to one.
    size:=sum(toList tableau#partition);	
    numbers:= apply (#(tableau#partition), i -> new MutableHashTable from tally tableau^i);
    maxTableaux:=product(numbers, tal->  multinomial( tally values tal));
    --scan (numbers, i-> print new HashTable from i);
    --print maxTableaux;
    tableaux :=tableauList(tableau#partition,maxTableaux);
    newTableau:= youngTableau(tableau#partition,size:(-1));
    --setIndex({0,0,0},newTableau);
    recursiveRowPermutationTableaux((#tableau#partition-1,0),numbers,newTableau,tableaux);
    tableaux
)

-----
-- A method that calculates the tableaus recursively. In each step the algorithm tries filling
-- the tableau with a number in the list of numbers. Then it calls the method again to fill
-- next slot in the tableau this time removing the element that was previoulsy added to the
-- tableau.
-- In this way the method effectively goes through all posible fillings of the tableau.
-- TODO find a way to put the list of numbers and the tableau as a global variable.
-----
recursiveRowPermutationTableaux = method(TypicalValue => TableauList)
recursiveRowPermutationTableaux(Sequence, List,YoungTableau,TableauList):= (pos,numbers, tableau, tableaux) -> (
    element:=0; 
    (row,col):= pos;
    nextPos := (0,0);
    if col + 1 == tableau#partition#row then nextPos = (row-1,0) else nextPos = (row,col+1);
    --print nextPos;
    for j in keys(numbers#row) do (
	if not any (tableau_col, i-> i == j) then (
	    tableau_(row,col)=j;
	   -- print net tableau;
	    numbers#row#j = numbers#row#j-1;
	    if(numbers#row#j == 0 ) then remove (numbers#row, j);
	    if nextPos#0 == -1 then addTableau(tableaux,tableau) else recursiveRowPermutationTableaux(nextPos,numbers,tableau,tableaux);
	    if numbers#row#?j then numbers#row#j = numbers#row#j+1 else numbers#row#j = 1;
	    tableau_(row,col)=-1;
	    );
	);   
)



-----
-- This method calculates the hook length formula for partitions 
-----
hookLengthFormula = method(TypicalValue =>ZZ)
hookLengthFormula Partition := parti -> (
    
    prod := (sum toList parti)!;
    conj:= conjugate parti;
   
   for i to #parti-1 do (
       for j to parti#i-1 do(
	   prod = prod//(parti#i-j+conj#j-i-1);
	   );
       
       );
        prod
)


cycleDecomposition = method()
cycleDecomposition List := perm ->(
    visited:= new MutableList;
    for i to #perm-1 do (visited#i = 0);
    
    ind:= 0;
    visited#(ind) = 1;
    cycles:= {};
    while ind<#perm do (
        newInd:= perm#(ind);
        cycle := while newInd != ind list newInd do(
            visited#(newInd) = 1;
            newInd = perm#(newInd);
        );
    	cycle = prepend(ind,cycle);
    	cycles = append(cycles,cycle);
        
        for i from ind to #perm-1 when visited#i==1 do 
        (
            ind = i;
        );
        ind = ind+1;
        visited#(ind) = 1;
    );
    cycles
)

conjugacyClass = method()
conjugacyClass List := perm -> (
    
    cycles:= cycleDecomposition perm;
    new Partition from (reverse sort apply (cycles, c -> #c))
    )


-----
-- Methods for calculating the multinomial 
-----
multinomial = method(TypicalValue => ZZ)
multinomial(Tally) := (p)->(
    n:= sum p;
    r:= n!;
    r// product (keys p, i-> (i!)^(p#i))
  )

multinomial( List) := (c)->(
    r:= (sum c)!;
    for i to #c-1 do r = r//((c#i)!);  
    r
  )

multinomial Partition := p -> (
    multinomial toList p
    )    
 


-----
-- This method extends the permutations from a subset of (1,...n) to all the permutations of
-- (1,...n) by fixing all letters that are not in the subset 
-----
extendPermutation = method(TypicalValue => List)
extendPermutation(ZZ, List) := (n,per) -> (
    numbers := sort(per);
    j := 0;
    result := new MutableList;
    result#(n-1) = 0;
    for i from 0 to n-1 do (
        if(j < #per and i == numbers#j) then 
        (
	    result#(i) = per#j;
            j = j+1;
        )
        else result#(i) = i;
    );
    result = toList result;
    result
)

extendedPermutations = method()
extendedPermutations(ZZ,List ):= (n,numbers) -> (
    perms:= permutations(numbers);
    apply(perms, p-> extendPermutation(n,p)) 
    )


-----
-- Direct product 
-----
directProductOfPermutations = method(TypicalValue =>List)
directProductOfPermutations(List,List):= (A,B) ->(
   flatten apply(A, a->apply(B,b->a_b))   
)

-----
-- This method codes 
-----
columnStabilizer=method(TypicalValue => List)
columnStabilizer(YoungTableau):= (tableau) ->(
    n:= sum toList tableau#partition;
    stab:=extendedPermutations(n,tableau_0);
    for i from 1 to tableau#partition#0-1 do(
	stab=directProductOfPermutations(stab,extendedPermutations(n,tableau_i));
	);
    stab
)

-----
-- This method codes 
-----
rowStabilizer=method(TypicalValue => List)

rowStabilizer(YoungTableau):= (tableau) ->(
    n:= sum toList tableau#partition;
    stab:=extendedPermutations(n,tableau^0);
    for i from 1 to #tableau#partition-1 do(
	stab=directProductOfPermutations(stab,extendedPermutations(n,tableau^i));
	);
    stab
)


permutationSign =method(TypicalValue=>ZZ)
permutationSign Partition := p -> (
    
    tal := tally toList p;
    product(keys tal, i->(-1)^((i+1)*tal#i))
)

permutationSign List := p -> (
    
    permutationSign conjugacyClass p
    )




----
-- Garnir elements:
----

--- 
--Given two list that represent two columns with a row descent, this method calculate 
-- all of the permutations that appear in the associated Garnir element. This turn out to be
-- in bijection with n-combinations of n+m letters.

-- The algorithm assumes that the lists are in ascending order.
---


combinations = method()
combinations(ZZ,ZZ):= (n,m)->(
    combs:=tabloids new Partition from {m,n-m};
    apply (combs#length, i-> flatten entries combs#matrix^{i})	
)   


SpechtModuleElement = new Type of List 

SpechtModuleTerm = new Type of List

coefficient SpechtModuleTerm := term -> term#1

tabloid = method()
tabloid SpechtModuleTerm := term -> term#0

net SpechtModuleTerm := term ->(
    
    if coefficient term  == 0 then 0 
    else if coefficient term == 1 then net tabloid term
    else if coefficient term == -1 then "- " | net tabloid term
    else coefficient term | " " |net tabloid term    

)

ZZ * SpechtModuleTerm := (c,term) ->(
    new SpechtModuleTerm from {tabloid term, c*coefficient term}
    )

SpechtModuleElement + SpechtModuleElement := (A,B)-> (
    A
    )

net SpechtModuleElement := e -> (
    netElement :=  net {};
    if #e > 0 then netElement = net e#0;
    for i from 1 to #e-1 do (
	if coefficient e#i >0 then netElement = netElement | " + " | net e#i
	else if coefficient e#i < 0 then netElement = netElement | " - " | net ((-1)*e#i);
	--print netElement;
	);
    netElement
    )

---
straighteningAlgorithm = method(TypicalValue=> List)
straighteningAlgorithm(YoungTableau):= (tableau) ->(
    
    sign:= orderColumnsTableau(tableau);
    tableaux:= new MutableList from {(tableau, sign)};
    length:= 1;
    level:= 0;
    while firstRowDescent(tableaux#0#0)<(tableau#partition#0,0)  do( 
	
	--printTableau(tableaux#0#0);
	garnir:= garnirElement(tableaux#0);
	--print(length);
	newTableaux:= new MutableList from (length-1+#garnir):0;
	
	i := 1;
	k := 0;
	j := 0;
	while(i < length or j < #garnir) do(
	   -- print(i,j,k);
	    if (j == #garnir) or ( i < length and columnDominance(tableaux#i,garnir#j) < 0) then (
		
		newTableaux#k = tableaux#i;
		i=i+1;
		k=k+1;
		) 
	    else if (i == #tableaux) or (j < #garnir  and columnDominance(tableaux#i,garnir#j)> 0) then (
		newTableaux#k = garnir#j;
		j=j+1;
		k=k+1;
		)
	    else (
		coef:= tableaux#i#1+garnir#j#1;
		if ( coef!= 0 ) then (
		    newTableaux#k= (garnir#j#0,coef);
		    k = k+1;
		    );
	    	--else print("Saved", level);
		i = i+1;
		j = j+1;
	    	);
	    );
	length= k;
	level = level+1;
	tableaux = apply(toList (0..k-1), i-> newTableaux#i);    	
	); 
    tableaux 
    )

garnirElement = method()
garnirElement(SpechtModuleTerm):= (term) -> (
    tableau:= tabloid term;
    (a,b):= firstRowDescent tableau;
    ans:=  term;
    if (a,b) != (-1,-1) then ( 
    	conju:= conjugate tableau#partition;
    	combs:= combinations(conju#a+1,b+1);
    	--print(a,b);
	AB:= (tableau_(a+1))_{0..b}|(tableau_(a))_{b..conju#a-1};
     	--print(AB);
	ans = apply (drop(combs,1),comb->(
	    newTableau:= youngTableau(tableau);
	   --print(comb);
	    for j to b do(
		newTableau_(j,a+1)= AB#(comb#j);
	    	);
	    for j from b+1 to conju#a do (  
	    	newTableau_(j-1,a) = AB#(comb#j);
		);
	    --print net newTableau;
	    sign:=sortColumnsTableau(newTableau);
	    --print net newTableau;
	    new SpechtModuleTerm from {newTableau,-(coefficient term) *sign*permutationSign(conjugacyClass(comb))}
      	    ));
	);
    
    --print(ans);
    ans= sort(ans);
    new SpechtModuleElement from ans
    )

sortColumnsTableau = method()
sortColumnsTableau YoungTableau := tableau -> (
    product(tableau#partition#0,i->sortColumn(tableau,i))
    )

sortColumn = method()
sortColumn (YoungTableau,ZZ) := (tableau,i) -> (
    col:= tableau_i;
    sortedCol := sort col;
    scan (#col, j->(tableau_(j,i)= sortedCol#j));
    index := hashTable apply (#sortedCol,i-> sortedCol#i => i);
    permutation:= apply(col,a->index#a );
    --error "test";
    permutationSign(permutation)
    )


SpechtModuleTerm ? SpechtModuleTerm := (term1,term2)-> rowDescentOrder(term1#0,term2#0)

rowDescentOrder = method()
rowDescentOrder(YoungTableau,YoungTableau):= (tableau1,tableau2)-> (
    
    ans:= 0;
    if(firstRowDescent tableau1 < firstRowDescent tableau2) then (
	
	ans= symbol <;
	)
    else if ( firstRowDescent tableau1 > firstRowDescent tableau2) then (
	
	ans = symbol >;
	
	)
    else (
	
	ans = toList tableau1#values ? toList tableau2#values
	
	);
    
    ans
    
    )


firstRowDescent= method()
firstRowDescent YoungTableau := tableau -> (
    
    parti := conjugate(tableau#partition);
    (a,b):= (#parti,0);
    if not any(#parti,i->(b = i;any(parti#i-1, j-> (a = j;tableau_(j,i)>tableau_(j,i+1))))) then
    	(a,b) = (-1,-1);
    (a,b)
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
    




cardinalityOfConjugacyClass = method(TypicalValue => ZZ)
cardinalityOfConjugacyClass(Partition) := p -> (
    p2 := differentElementsInPartition(p);
    base := keys(p2);
    prod := 1;
    for i to #(base)-1 list prod do (prod = prod*((base#i)^(p2#(base#i)))*(p2#(base#i))!);
    (sum toList p)!//prod
)






-----
-- This method codes 
-----

matrixRepresentation = method()
matrixRepresentation(List,TableauList) := (perm,standard)-> ( 
    
    mat := mutableMatrix(QQ,standard#length,standard#length);
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
)
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

end


p = new Partition from {3,2}
y = youngTableau( p ,{2,3,4,0,1})
sortColumnsTableau y
y
new SpechtModuleTerm from {y,2}
stan = standardTableaux p  

p = new Partition from {2,1}
y = youngTableau( p ,{1,0,2})
sortColumnsTableau y
y
term = new SpechtModuleTerm from {y,1}
garnirElement term 
stan = standardTableaux p  