-- -*- coding: utf-8 -*-
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
		

export {"CharacterTable"}
export {"characterTable"}
		
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
export {"sortColumnsTableau"}
export {"cardinalityOfConjugacyClass"}


export{"multinomial"}
export {"straighteningAlgorithm"}

export {"SpechtModuleElement"}
export {"spechtModuleElement"}
export {"toVector"}

export {"permutationMatrix"}
export {"permutePolynomial"}

export {"vandermondeDeterminant"}
export {"spechtPolynomial"}
export {"indexMonomial"}
export {"higherSpechtPolynomial"}

export {"spechtPolynomials"}
export {"higherSpechtPolynomials"}



export {"productPermutationsList"}
export {"permutationSign"}
export {"rowDescentOrder"}
export {"sortColumn"}
export {"firstRowDescent"}
export {"schurPolynomial"}
export {"generalizedVandermondeMatrix"}
export {"Robust","AsExpression","GenerateGroup"}
export {"generatePermutationGroup"}
--export {"representationMultiplicity"}
export {"secondaryInvariants"}
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



CharacterTable = new Type of MutableHashTable

--------------------
-- Constructors
--------------------
characterTable = method(TypicalValue => CharacterTable)
characterTable ZZ := n -> (
    
    charTables := new MutableHashTable;
    
    
    
    
    for i from 1 to n do (
	
	 
	charTable := new CharacterTable;
	partis := partitions i;
	charTable#index = hashTable apply(#partis, i-> partis#i => i);
    	charTable#length = #(partis);
    	charTable#degree = i;
    	charTable#values = mutableMatrix(ZZ,charTable#length,charTable#length);
    	charTables#i = charTable;
	--print("ok");
	y:= partitions(i);
	for j  to #y-1 do (
	    
	    for k from j to #y-1 do (
		val:= calculateNumberOfEquals(y#(j),y#(k),charTables);
		--print("ok");
		(charTables#i)_(j,k)=val;
	    );
	);
        --print("Table",i);
    	--print((charTables#i)#values);	
    ); 
   charTable := reduceCharacterTable(charTables#n);
   charTable#values = matrix charTable#values;
   charTable
)

    
       
	


CharacterTable_Sequence:=(charTable,seq)-> (
    if #seq != 2 then error "expected a sequence of length 2";
    (a,b) := seq;
    if(class a === Partition) then (
	if sum toList a != charTable#degree then (error "expected a partition of size "|charTable#degree)
	else a=charTable#index#a)
    else (if class a =!= ZZ then error "expected argument 1 to be a partition or an integer");	
     
     if(class b === Partition) then (
	if sum toList b != charTable#degree then (error "expected a partition of size "|charTable#degree)
	else b=charTable#index#b)
    else if class b =!= ZZ then error "expected argument 2 to be a partition or an integer";
    charTable#values_(a,b)
    )

-- Method to modify the entries of the character table.
-- Inputs:
--     a:ZZ or Partition
--    	the index of the row
--     b:ZZ or Partition
--    	  the index of the column
--     val:ZZ
--       the value to put in the method
--     charTable:CharacterTable
--    	 the character table

CharacterTable_Sequence = (charTable,seq,e)-> (
    if #seq != 2 then error "expected a sequence of length 2";
    (a,b) := seq;
    if(class a === Partition) then (
	if sum toList a != charTable#degree then (error "expected a partition of size "|charTable#degree)
	else a=charTable#index#a)
    else (if class a =!= ZZ then error "expected argument 1 to be a partition or an integer");	
     
     if(class b === Partition) then (
	if sum toList b != charTable#degree then (error "expected a partition of size "|charTable#degree)
	else b=charTable#index#b)
    else if class b =!= ZZ then error "expected argument 2 to be a partition or an integer";
    charTable#values_(a,b)=e;
    e
    )



-- This method calculates the inner product of characters
-- The characters are presented as rows of the character table
-- To calculate the inner product it is necessary to calculate the size of the conjugaci classes of S_n
-- Inputs
--    n:ZZ
--    	  The degree of the symmetric group. It is used to calculate the partitions of n
--    C:MutableMatrix
--    	  The firts character. It is represented as a mutable matrix with a single row.
--    X:MutableMatrix
--    	  THe second character.
-- Outputs
--    :ZZ
--    	The inner product of characters C and X.	  

innerProduct = method(TypicalValue => ZZ)
innerProduct(ZZ,MutableMatrix,MutableMatrix) := (n,C,X) -> (
    prod:=0;
    p:=partitions(n);
    prod = sum apply( numColumns(C),i -> C_(0,i)*(X_(0,i))*(cardinalityOfConjugacyClass(p#(i))));
    prod//(n)!
)


net CharacterTable := charTable -> (
    net(charTable#values)
    )


-- This method applies Gram-Schmidt to the table of permutation characters.
-- This method uses the fact that a permutation module consists of a direct sum
-- of a copy of the irreducible Specht module S^\lambda and some copies of
-- Specht modules S^\mu such that \mu> \lambda in lexicographical order
-- Finally, since the irreducible characters are an orthonormal basis of the space of
-- characters of S_n, by applying Gram-Schmitd in lexicograhical order the character table
-- is obtained.
-- Inputs
--    charTable:CharacterTable
--    	  The character table containing the characters of the permutation modules of S_n
-- Outputs
--    :CharacterTable
--    	Returns the character table of irreducible characters of S_n.	  
reduceCharacterTable = method(TypicalValue => CharacterTable)
reduceCharacterTable CharacterTable  := charTable -> (
    for i to charTable#length-1 do(
    
        for j to  i-1 do(
            
            c := innerProduct(charTable#degree,(charTable#values)^{i},(charTable#values)^{j});
            for k to charTable#length-1 do(
		val:= charTable_(i,k)-c*charTable_(j,k);
                charTable_(i,k)=val;
            );
     );
    	
    );
   
    charTable
)



-- This method calculates recursively the entry of the character of the permutation module M^\lambda (partition 1) of
-- the conjugacy class K index by the partition \mu (partition2).
-- Inputs
--    partition1:Partition
--    	  A partition that indexes the character M^\lambda
--    partition2:Partition
--    	  A partition that indexes the conjugacy class K    	
-- Outputs
--    :ZZ
--      The value of the permutation character  
calculateNumberOfEquals = method(TypicalValue => ZZ )
calculateNumberOfEquals(Partition, Partition,MutableHashTable):= (partition1, partition2,charTables)->(
    
    z:=0;
    if(sum(toList partition1) == sum(toList partition2)) then (
    	if #partition1 == 1 then (z = 1;)
	else ( 
    	    border:= partition2#0;
	    partition2 = drop(partition2,1);
	    for i to #partition1-1 when partition1#i>=border do(
	    	c:= new MutableList from partition1;
		c#i = c#i-border;
	        newPartition := new Partition from reverse sort toList c;
		if(newPartition#(-1) == 0)
		    then (newPartition = drop(newPartition,-1););
		if(#newPartition == 0)
		    then (z= z+ 1;)
		else(
		    
		    --print(newPartition);
		    --print(partition2);
		    currentTableNumber:=sum(toList newPartition);
		    z = z+(charTables#currentTableNumber)_(newPartition,partition2);
		    --print("ok");
		    --print(z);
		);
		
	    );
	    
	);    
    ) else error "Partition dimensions do not match";
    z
)




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




------
-- Gives a representation of the Young Tableau as a list of the rows in the
-- diagram.
------
tableauToList = method(TypicalValue => List)
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

YoungTableau == YoungTableau := (S,T) -> (
    
    toList S#partition == toList T#partition and toList S#values == toList T#values
    )


entries YoungTableau := tableau -> toList tableau#values

numcols YoungTableau := tableau -> tableau#partition#0

numrows YoungTableau := tableau -> #tableau#partition

size YoungTableau := tableau -> sum toList tableau#partition

------
-- A method to give a graphical representation of a Young diagram. This method saves the
-- diagram in a mutable matrix and then prints the matrix. 
------
net YoungTableau := tableau ->(
    l := tableauToList tableau;
    corner := #(tableau#partition) ;
    tableauNet:= "|" ;
    for i to corner-2 do tableauNet = tableauNet || "|"; 
    
    for i to numcols tableau-1 do ( 
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
lista#matrix = mutableMatrix(ZZ,multinomial(p),sum(toList p));
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
    apply(tableaux#length,i-> youngTableau(tableaux#partition,flatten entries tableaux#matrix^{i}))
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

getRow = method()
getRow (TableauList,ZZ) := (tableaux,i)-> flatten entries tableaux#matrix^{i}

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
  s:=(size tableau)-(tableau#partition)#(ind#row);
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
    
    flatten apply (numcols tableau, i-> reverse tableau_i)
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
    newTableau:= youngTableau(tableau#partition,toList ( size:(-1) ) );
    --setIndex({0,0,0},newTableau);
    recursiveRowPermutationTableaux((#tableau#partition-1,0),numbers,newTableau,tableaux);
    toListOfTableaux tableaux
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


SpechtModuleElement = new Type of HashTable 

spechtModuleElement = method()
spechtModuleElement (YoungTableau, QQ) := (tableau,coef)-> (
    new SpechtModuleElement from hashTable {partition => tableau#partition, 
	values => new MutableHashTable from hashTable {toList tableau#values => coef}} 
)

spechtModuleElement (YoungTableau, ZZ) := (tableau,coef)-> (
    new SpechtModuleElement from hashTable {partition => tableau#partition, 
	values => new MutableHashTable from hashTable {toList tableau#values => coef}} 
)

spechtModuleElement YoungTableau := tableau -> spechtModuleElement(tableau,1)

spechtModuleElement (Partition, MutableHashTable):= (p,v) ->(
    new SpechtModuleElement from hashTable {partition => p, values => v}
    )

netTerm = method()
netTerm (YoungTableau,ZZ) := (tableau,coef)-> (
    
    if coef  == 0 then 0 
    else if coef == 1 then net tableau
    else if coef == -1 then "- " | net tableau
    else coef | " " |net tableau    
    )

QQ * SpechtModuleElement := (c,element) ->(
     spechtModuleElement (element#partition, new MutableHashTable from applyValues (new HashTable from element#values,v-> if c!= 0 then v * c else continue))
    )

ZZ * SpechtModuleElement := (c,element) ->(
    spechtModuleElement (element#partition, new MutableHashTable from applyValues (new HashTable from element#values,v-> if c!= 0 then v * c else continue))
    )



--first SpechtModuleElement := A -> new SpechtModuleTerm from {first keys(A),first values(A)}

--last SpechtModuleElement := A -> new SpechtModuleTerm from {last keys(A),last values(A)}

trim SpechtModuleElement := A -> scan (keys(A#values), tabloid -> if A#tabloid == 0 then remove (A#values,tabloid))



SpechtModuleElement + SpechtModuleElement := (A,B)-> (
     if(A#partition===B#partition) then (
     	 v := merge(A#values,B#values,(i,j)->(if i+j != 0 then i+j else continue));
	spechtModuleElement(A#partition,v)
     ) else error "The elements do not belong to the same SpechtModule"
     
    )

SpechtModuleElement - SpechtModuleElement := (A,B)-> (
     A +(-1)*B
    )

terms SpechtModuleElement:= A -> (
    apply(keys A#values, tabloid-> (youngTableau(A#partition,tabloid),A#values#tabloid))
    )

List SPACE SpechtModuleElement:= (perm,element)->(
    vals := applyKeys(new HashTable from element#values, t->(
	    perm_t));
    spechtModuleElement(element#partition,new MutableHashTable from vals)
    )

net SpechtModuleElement := A -> (
    netElement :=  net {};
    tabloids := sort apply(keys A#values, t->  youngTableau(A#partition,t));
    if #tabloids > 0 then (
	t := first tabloids ; 
	netElement = netTerm(t,A#values#(toList t#values));
    for t in drop(tabloids,1)  do (
	if A#values#(toList t#values) >0 then netElement = netElement | " + " | netTerm (t,A#values#(toList t#values))
	else if A#values#(toList t#values) < 0 then netElement = netElement | " - " | netTerm (t,-(A#values#(toList t#values)));
	--print netElement;
	);
    );
    netElement
    )

straighteningAlgorithm = method(TypicalValue=> SpechtModuleElement)
straighteningAlgorithm(SpechtModuleElement) := (element)->(
    sortColumnsTableau(element); 
    notStandard := select(1, terms element, t-> firstRowDescent(t#0) > (-1,-1));
    while #notStandard != 0  do( 
	notStandard = first notStandard;
	garnir:= garnirElement(notStandard);
	--print net (notStandard,garnir);
	--error "Stop";
	element = element - garnir;
	--print net element;
	notStandard = select(1, terms element, t-> firstRowDescent(t#0) > (-1,-1)); 	
	); 
    element 
)



straighteningAlgorithm(YoungTableau,ZZ):= (tableau,coef) ->(
    
    element := spechtModuleElement (tableau,coef);
    straighteningAlgorithm(element)
    )
 

straighteningAlgorithm(YoungTableau):= tableau -> straighteningAlgorithm(tableau,1)


garnirElement = method()

garnirElement(YoungTableau,ZZ,ZZ,ZZ):= (tableau,coef,a,b)-> (
    if(a >= #tableau#partition or b>=tableau#partition#a-1) then 
    error "Index out of bounds" else (
    	ans := {spechtModuleElement(tableau,coef)};
	if (a,b) >= (0,0) then ( 
    	conju:= conjugate tableau#partition;
    	combs:= combinations(conju#b+1,a+1);
    	--print(a,b);
	AB:= (tableau_(b+1))_{0..a}|(tableau_(b))_{a..conju#b-1};
     	--print(AB);
	ans = apply (combs,comb->(
	    --print(comb);
	    newTableau:= youngTableau tableau;
	    for j to a do(
		newTableau_(j,b+1)= AB#(comb#j);
	    	);
	    for j from a+1 to conju#b do (  
	    	newTableau_(j-1,b) = AB#(comb#j);
		);
	    --print net newTableau;
	    sign:=sortColumnsTableau(newTableau);
	    --print net newTableau;
	    spechtModuleElement (newTableau, (coef) *sign*permutationSign(conjugacyClass(comb)))
      	    ));
    	
	);
    --error "Stop";
    --print(ans);
    sum ans	
	)
    )

garnirElement(YoungTableau,ZZ):= (tableau,coef) -> (
    newTableau := youngTableau tableau;
    ans:=  {spechtModuleElement(newTableau,coef)};
    (a,b):= firstRowDescent newTableau;
    garnirElement(tableau,coef,a,b)
    )

garnirElement(YoungTableau) := tableau -> garnirElement(tableau,1)

sortColumnsTableau = method()
sortColumnsTableau YoungTableau := tableau -> (
    product(tableau#partition#0,i->sortColumn(tableau,i))
    )

sortColumnsTableau SpechtModuleElement := element ->
(
    scan (keys element#values, t -> (
	    y := youngTableau(element#partition,t);
	    coef := element#values#t;
	    remove(element#values,t);
	    sign:= sortColumnsTableau(y);
	    if(element#values#?(entries y)) then element#values#(entries y) = element#values#(entries y)+sign*coef
	    else element#values#(entries y) = coef*sign;
	     )   
	);
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

rsortList = method()
rsortList List := l -> (
    sortedList := rsort l;
    index := hashTable apply (#sortedList,i-> sortedList#i => i);
    permutation:= apply(l,a->index#a);
    --error "test";
    (l,permutationSign(permutation))
    )

sortList = method()
sortList List := l -> (
    sortedList := sort l;
    index := hashTable apply (#sortedList,i-> sortedList#i => i);
    permutation:= apply(l,a->index#a);
    --error "test";
    (l,permutationSign(permutation))
    )


--SpechtModuleTerm ? SpechtModuleTerm := (term1,term2)-> rowDescentOrder(term1#0,term2#0)

YoungTableau ? YoungTableau := (tableau1,tableau2)-> rowDescentOrder(tableau1,tableau2)

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
    if not any(#parti,i->(b = i; any(parti#i, j-> (a = j;i+1 < tableau#partition#j and tableau_(j,i)>tableau_(j,i+1))))) then
    	(a,b) = (-1,-1);
    (a,b)
    )


toVector = method()
toVector (SpechtModuleElement,HashTable):= (element,index) -> (
    ans:=mutableMatrix (QQ,1,#index);
    scan(keys element#values, t-> ans_(0,index#t)= element#values#t);
    matrix ans
    )

toVector (SpechtModuleElement) := element -> (
    stan:= standardTableaux element#partition;
    index:= hashTable apply (stan#length,i->(flatten entries stan#matrix^{i} => i ));
    toVector(element,index)
    )






cardinalityOfConjugacyClass = method(TypicalValue => ZZ)
cardinalityOfConjugacyClass(Partition) := p -> (
    tal := tally(toList p);
    base := keys(tal);
    prod := product ( base, n-> ( n^(tal#n) ) * (tal#n)! );
    (sum toList p)!//prod
)



matrixRepresentation = method()
matrixRepresentation(List,TableauList) := (permutation,standard)-> ( 
    
   index:= hashTable apply (standard#length,i->(flatten entries standard#matrix^{i} => i ));
   transpose matrix apply(standard#length,i->(
	   element:= spechtModuleElement(standard_i);
	   {toVector (straighteningAlgorithm (permutation element), index )})
       )
 
)

matrixRepresentation(TableauList) := (standard)-> (
    hashTable apply(permutations sum toList standard#partition, perm-> perm=> matrixRepresentation(perm,standard))
    )

matrixRepresentation(List,Partition) := (permutation, parti)->(
    standard := standardTableaux parti;
    matrixRepresentation(permutation,standard)
    )

matrixRepresentation(Partition) := (parti)->(
    standard := standardTableaux parti;
    matrixRepresentation(standard)
    )


permutationMatrix = method()
permutationMatrix(List,PolynomialRing) := (permutation,R)->(
    generatorList:= apply(permutation,i->R_(i) );
    map(R,R,matrix{generatorList})
)

permutePolynomial = method()
permutePolynomial (List, RingElement) := (permutation,polynomial)-> (
    if(isPolynomialRing ring polynomial) then
    (permutationMatrix(permutation,ring polynomial)) polynomial
    
    else error "argument is not a polynomial"
)

permutePolynomial(List,Product) := (permutation,polynomial) -> (
    new Product from apply (toList polynomial,f-> permutePolynomial(permutation,f))
    )

permutePolynomial(List,Sum) := (permutation,polynomial) -> (
    new Sum from apply (toList polynomial,f-> permutePolynomial(permutation,f))
    )

permutePolynomial(List,Power) := (permutation,polynomial) -> (
    new Power from {permutePolynomial(permutation,polynomial#0),polynomial#1}
    )

vandermondeDeterminant = method(Options => {AsExpression => false})
vandermondeDeterminant(List,PolynomialRing):= o-> (lista,R)->(
    variables := apply(lista,i-> R_i);
    if o.AsExpression then product flatten apply (#lista, i->toList apply( (i+1)..(#lista-1),j-> new Power from {(variables#j-variables#i),1} ) )
    else product flatten apply (#lista, i->toList apply( (i+1)..(#lista-1),j-> (variables#j-variables#i) ) )
    )

spechtPolynomial = method()
spechtPolynomial ( YoungTableau, PolynomialRing ) := (tableau, R)-> (
    product (numcols tableau, i->vandermondeDeterminant(tableau_i,R))
    )

spechtPolynomials = method()
spechtPolynomials (Partition,PolynomialRing):= (partition,R)-> (
    standard:= standardTableaux partition;
    firstPolynomial:= spechtPolynomial(standard_0,R);
    hashTable apply (standard#length, i-> getRow(standard,i) => permutePolynomial(getRow(standard,i) , firstPolynomial) )
    )

indexMonomial = method()
indexMonomial(YoungTableau, YoungTableau, PolynomialRing) := (S,T,R) -> (
    ind := indexTableau S;
    monomial:= 1_R;
    if(toList S#partition == toList T#partition) then (
    	monomial = product(size S, i -> R_((entries T)#i)^( (entries ind)#i) )
    	) else error "tableaux 1 and 2 do not have the same shape";
    monomial
    )

higherSpechtPolynomial = method(Options => {AsExpression => false , Robust => true})
higherSpechtPolynomial(YoungTableau, YoungTableau, PolynomialRing) := o-> (S,T,R)->(
    if toList S#partition != toList T#partition then error "tableau shapes of S and T do not match";
    ans:= R_0;
    
    if(o.Robust) then (
	monomial := indexMonomial(S,T,R);
    	sym:= sum (rowStabilizer T, sigma-> permutePolynomial(sigma,monomial));
    	polynomial:= sum (columnStabilizer T, tau -> permutationSign(tau)*permutePolynomial(tau,sym))*hookLengthFormula(S#partition)//(numgens R)!;
	if o.AsExpression then ans = factor polynomial else ans = polynomial 
    	)
    else (
	
	rowPermutations := rowPermutationTableaux indexTableau S;
	ans = sum(rowPermutations, tab -> product apply (numcols S, i->determinant generalizedVandermondeMatrix(T_i,tab_i,R)));
	);
    ans
   )


    
higherSpechtPolynomials = method(Options => {AsExpression => false , Robust => true})
higherSpechtPolynomials(Partition,PolynomialRing):= o-> (partition,R) -> (
    
    standard:= standardTableaux partition;
    hashTable apply(standard#length, i-> getRow(standard,i) => higherSpechtPolynomials(standard_i,standard,R, Robust => o.Robust, AsExpression => o.AsExpression))
    )

higherSpechtPolynomials(YoungTableau,PolynomialRing):= o->(S,R)-> (
    standard:= standardTableaux S#partition;
    higherSpechtPolynomials(S,standard,R,AsExpression => o.AsExpression, Robust => o.Robust)
    )


higherSpechtPolynomials(YoungTableau,TableauList,PolynomialRing):= o->(S,standard,R)-> (
    firstPolynomial:= higherSpechtPolynomial(S,standard_0,R,Robust => o.Robust, AsExpression => o.AsExpression);
    hashTable apply (standard#length, i-> getRow(standard,i)=> permutePolynomial(getRow(standard,i),firstPolynomial))
    )

higherSpechtPolynomials PolynomialRing := o-> R -> (
     partis := partitions numgens R;
     hashTable apply(partis,p-> p=> higherSpechtPolynomials(p,R,Robust => o.Robust, AsExpression => o.AsExpression))
    )

generalizedVandermondeMatrix = method()
generalizedVandermondeMatrix(List,List,PolynomialRing):= (indices, exponents, R) -> (
    if #indices != #exponents then error "number of indices and exponents does not match";
    M := matrix apply (exponents, e-> apply (indices, i-> (R_i)^e));
    M
    )

schurPolynomial = method(Options => {AsExpression => false, Strategy=>"determinant"})
schurPolynomial(List,List,PolynomialRing) := o->(indices, exponents, R) -> (
    ans:= 1_R;
    sgn:= 1;
    if #indices != #exponents then error "size of indices and exponets does not match"; 
    if o.Strategy == "determinant" then
    ans = determinant generalizedVandermondeMatrix(indices,exponents,R)// vandermondeDeterminant(indices,R)
    else if o.Strategy == "semistandard_tableaux" then (
        sortedList := sort exponents;
	sortedList =  sortedList - toList (0..(#sortedList-1));
        --print sortedList;
	--print increasing sortedList;
	if not increasing sortedList then ans = 0_R else (
	 l:= 0;
	 (l,sgn)= sortList exponents;
	 sortedList = reverse sortedList; 
	 notZero := position(sortedList,i->i==0);
	 if(notZero === null) then notZero = #sortedList-1 else notZero = notZero -1;
	 if(notZero >= 0 ) then 
	(
	    partition:= new Partition from sortedList_{0..notZero};
	    --print partition;
	    semistandard := semistandardTableaux(partition, #indices );
	    ans = sum(semistandard#length, i-> product(getRow(semistandard,i),j->R_(indices#j)));
	    );
	);
    );
    sgn*ans
    )

increasing = method()
increasing List := lista -> (
    all(#lista-1, i-> lista#i <= lista#(i+1))
)

decreasing = method()
decreasing List := lista -> (
    all(#lista-1, i-> lista#i >= lista#(i+1))
)


generatePermutationGroup = method()
generatePermutationGroup List := gens -> (
    	group:= hashTable apply (gens , g -> g=> 0 );
	products:= group;
	for g in keys group do products = merge (products, applyKeys (group, h-> g_h), (i,j)-> i+j);
	while #group < #products do(
	  group = products;
	  products = group;
	  for g in keys group do products = merge (products, applyKeys (group, h-> g_h), (i,j)-> i+j);
	    );
    	keys group
    )

representationMultiplicity = method()

representationMultiplicity(Tally,Partition,CharacterTable):= (tal,partition,charTable)-> (
       partis:= partitions sum toList partition;
       sum(keys tal, p ->(charTable_(partition,p)*tal#p))// sum values tal
    )

representationMultiplicity(Tally,Partition):= (tal,partition)-> (
    charTable := characterTable sum toList partition;    
    representationMultiplicity(tal,partition,charTable)
    )


vectorToPolynomial = method()
vectorToPolynomial(List,HashTable,TableauList):= (vector, basis,standard)->(
   	sum ( #vector, i-> if(vector#i == 0) then 0 else vector#i*basis#( getRow(standard,i))  )	
    )

secondaryInvariants = method(Options => {GenerateGroup => true, AsExpression => false })
secondaryInvariants(List,PolynomialRing):= o->(gens,R)-> (
    	if #gens#0 != numgens R then error "the size of the elements does not match the number of generators of R";
	H := generatePermutationGroup gens;
	tal := tally apply (H,h->conjugacyClass h);
       	partis := partitions numgens R;
	charTable := characterTable numgens R;
	hashTable apply (partis, p-> (
		if representationMultiplicity(tal,p,charTable)== 0 then p=> {}
		else (
		    standard := standardTableaux p;
		    isotypicalComponentBasis := higherSpechtPolynomials(p,R,AsExpression => o.AsExpression);
		    if representationMultiplicity(tal,p,charTable)==standard#length then (
		    	
			index:= hashTable apply (standard#length, i-> getRow(standard,i)=> i);
			p => hashTable apply(keys isotypicalComponentBasis, S->( S=> 
				applyKeys(isotypicalComponentBasis#S, T-> index#T) ) )			 
		    ) else
		    (
		    	V:=(coefficientRing R)^(standard#length);
			for h in gens do (
			    M:= matrixRepresentation(h,standard);
			    V = intersect(V,ker ( M - id_(source M ) ) );
			    );
			vectors:= generators V;
			p => hashTable apply (keys isotypicalComponentBasis,S-> ( S => 
			       hashTable apply (numColumns vectors, i-> i=> 
				   (vectorToPolynomial(flatten entries vectors_{i},isotypicalComponentBasis#S,standard ))) ))
				
		    )
		)
	    )
	)
    )
 
   
beginDocumentation()

multidoc ///
    Node
    	Key
	    SpechtModule
	Headline
    	    a package for constructing Specht Modules
	Description
	    Text
	    	{\em SpechtModule} calculates many objects related to the irreducible representations of the symmetric functions.
    		This construction is used to implement an algorithm in invariant theory which calculates efficiently the secondary
    		invariants of any permutation group.
		
		The main features of the package include a method for calculating the character table of $S_n$, algorithms for
    		calculating list of tableaux given a partition (tabloids, standard tableaux and semistandard tableaux among others)
    		an implementation of the straightening algorithm which includes an implementation of the garnir element given a tableau
    		an a row descent. Methods for calculating Higher Specht Polynomials which give a basis of
    		the Specht Modules that arrise in the coinvariant ring of $S_n$ which is the quotient $k[x_1,..,x_n]/({\rm Sym}(n)^+)$. 
    		And finally methods for calculating the secondary invariants described above.	    
	Caveat	  
	    An improvement can be made by finding an efficient way to calculate or represent Schur Polynomials
 
    Node
    	Key
	    CharacterTable
	    (symbol _,CharacterTable, Sequence)
    	    (net, CharacterTable)
	Headline
    	    the class of character tables
	Description
	    Text
	    	This type represents the character table of a symmetric group. It is implemented as a
    		hash table that stores the list of partitions, the size of the table and a
    		matrix which stores the values of the table.	    
	    
	    Example	
		charTable = characterTable 5
   		a = new Partition from {3,1,1}; b = new Partition from {1,1,1,1,1}
		peek charTable
		charTable_(a,b)
 	SeeAlso
 	    characterTable

    Node
    	Key
	    characterTable
    	    (characterTable,ZZ)
	Headline
    	    returns the character table of the symmetric group
	Usage
	    characterTable n
	Inputs
	    n:ZZ
	    	the degree of the symmmetric group
	Outputs
	    :CharacterTable
	    	the character table with the irreducible characters of $S_n$ indexed by partitions
	Description
	    Text
	    	This method construct the irreducible characters of $S_n$. The method works by recursively calculating the
		character tables for the permutation modules of $S_n$. Then applying Gram-Schimdt algorithm to this
		characters using the inner product of characters we obtain the irreducible characters of $S_n$	    
 	SeeAlso
 	    CharacterTable
    Node
    	Key
	    YoungTableau
    	Headline
    	    the class of Young Tableaux
    	Description
             Text
    	    	This type represents a Young Tableau. It is implemented as a MutableHashTable. This hash table stores
    		a partition that represents a shape of the tableau. The filling of the tableau is stored as a
    		mutable list.
    	    Example
    	    	p = new Partition from {3,2}
    		y = youngTableau(p,{1,0,2,3,4})
    		peek y
    Node
    	Key
    	    (youngTableau,Partition,List)
    	    (youngTableau,Partition,MutableList)
    	    youngTableau
    	Headline
    	    the constructor method for the class YoungTableau
    	Usage
    	    youngTableau(p,l)
    	Inputs
    	    p:Partition
    	    	the shape of the tableau
    	    l:List
    	    	the filling of the tableau
    	Outputs
    	    :YoungTableau
    	    	a young tableau with the given shape and filling
    	SeeAlso
	    YoungTableau
    Node
    	Key
    	    (youngTableau,YoungTableau)
    	Headline
    	    creates a copy of a YoungTableau object
    	Usage
    	    youngTableau(y)
    	Inputs
    	    y:YoungTableau
    	    	a Young tableau
    	Outputs
    	    :YoungTableau
    	    	a copy of y
    	Description
	    Example
	    	p = new Partition from {3,2}
		l = {2,1,0,3,4}
		y = youngTableau(p,l)
		y1 = youngTableau y
		y == y1  
    		y === y1    	
	
    Node
    	Key
    	    (tableauToList,YoungTableau)
    	    tableauToList
    	Headline
    	    converts a YoungTableau to list form
    	Usage
    	    tableauToList(y)
    	Inputs
    	    y:YoungTableau
    	    	a Young tableau
    	Outputs
    	    :List
    	    	a doubly nested list, the list of rows of the tableau
    	Description
	    Example
	    	p = new Partition from {2,2,1}
		l = {2,1,0,3,4}
		y = youngTableau(p,l)
		tableauToList y

    Node
    	Key
    	    (listToTableau,List)
    	    listToTableau
    	Headline
    	    constructs a Young Tableau from a doubly nested list of numbers
    	Usage
    	    listToTableau(l)
    	Inputs
    	    l:List
    	    	a doubly nested list of numbers
    	Outputs
    	    :YoungTableau
    	    	a Young Tableau, such that the rows corresponds to the elements of l
    	Description
	    Example
	        l = {{0,1,2},{3,4},{5}}
        	listToTableau l

    Node
    	Key
    	    (symbol _,YoungTableau,Sequence)
    	Headline
    	    retrieves the entry in cell (a,b) from a Young Tableau
    	Usage
    	    y_(a,b)
    	Inputs
    	    y:YoungTableau

    	    pos:Sequence
    	    	the position (a,b) of the cell where a is the row and b the column	    
    	Outputs
    	    :ZZ
    	    	the number in the cell at the position (a,b) of the tableau y
    	Description
	    Example
	        y = youngTableau(new Partition from {2,2},{0,2,1,3})
		y_(0,0)
		y_(1,1)

    Node
    	Key
    	    (symbol ^,YoungTableau,ZZ)
    	Headline
    	    retrieves a row from a Young Tableau
    	Usage
    	    y^n
    	Inputs
    	    y:YoungTableau

    	    n:ZZ
    	    	the number of the row
    	Outputs
    	    :List
    	    	a list of the numbers that appear in row n of y
    	Description
	    Example
	        y = youngTableau(new Partition from {3,2},{0,2,1,3,4})
		y^0
		y^1

    Node
    	Key
    	    (symbol _,YoungTableau,ZZ)
    	Headline
    	    retrieves a column from a Young Tableau
    	Usage
    	    y_n
    	Inputs
    	    y:YoungTableau
	    
    	    n:ZZ
    	    	the number of the row
    	Outputs
    	    :ZZ
    	    	a list of the numbers that appear in row n of y
  
    	Description
    	    Example
    	    	y = youngTableau(new Partition from {3,2},{0,2,1,3,4})
		y_0
		y_1

    Node
    	Key
	    (symbol ==,YoungTableau,YoungTableau)
    	Headline
    	    checks wheter two tableaux are equivalent	 
        Usage
    	    y1 == y2	
        Inputs
      	    y1:YoungTableau
      	    
	    y2:YoungTableau
  	Outputs
      	    :ZZ
            	true if the shape and filling of tableaux y1 and y2 are the same
  	Description
   	    Example
	    	y = youngTableau(new Partition from {3,2},{0,2,1,3,4})
		y1 = youngTableau(new Partition from {3,2},{0,2,1,3,4})
		y == y1
		y2 =  youngTableau(new Partition from {2,2,1},{0,2,1,3,4})
		y == y2

    Node
    	Key
    	    (entries,YoungTableau)
  	Headline
	    returns the filling of the tableau
  	Usage
    	    entries y
  	Inputs
      	    y:YoungTableau
  	Outputs
      	    :List
            	returns the filling of the tableau
  	Description
   	    Example
	    	y = youngTableau(new Partition from {3,1,1},{2,0,1,4,3})
		entries y

    Node
    	Key
    	    (numcols,YoungTableau)
  	Headline
    	    returns the number of columns of a tableau
  	Usage
    	    numcols y
  	Inputs
      	    y:YoungTableau
  	Outputs
      	    :ZZ
            	the number of columns of the tableau
       	Description
    	    Example
	    	y = youngTableau(new Partition from {2,1,1,1},{2,0,1,4,3})
		numcols y

    Node
    	Key
    	    (numrows,YoungTableau)
       	Headline
    	    returns the number of rows of a tableau
	Usage
	    numrows y
  	Inputs
    	    y:YoungTableau
	Outputs
      	    :ZZ
            	the number of rows of the tableau
  	Description
   	    Example
	    	y = youngTableau(new Partition from {2,1,1,1},{2,0,1,4,3})
		numrows y

    Node
    	Key
    	    (size,YoungTableau)
  	Headline
    	    returns the number of cells of a tableau
  	Usage
    	    size y
  	Inputs
      	    y:YoungTableau
  	Outputs
      	    :ZZ
            	the number of cells rows of the tableau
       	Description
   	    Text
       	    	The size is calculated as the sum of the numbers in the partition associated to the tableau
   	    Example
	    	y = youngTableau(new Partition from {2,1,1,1},{2,0,1,4,3})
		size y


    Node
    	Key
    	    TableauList
  	Headline
    	    the class of list of tableaux
  	Description
    
    	    Text
            	This type represents a list of tableaux of the same size. They are represented as a MutableHashTable.
		A matrix in this hash table stores the filling of every tableau in the list. This representation
		is particularly usefull when only the filling of the tableau is needed.
  	    Example
    	    	p = new Partition from {2,1}
    		y1 = youngTableau(p,{0,1,2})
		y2 = youngTableau(p,{0,2,1})
		y3 = youngTableau(p,{1,2,0})
    		t = tableauList p
		addTableau(t, y1)
		addTableau(t, y2)
		addTableau(t, y3)
		peek t
 

    Node
    	Key
    	    (tableauList,Partition,ZZ)
    	    (tableauList,Partition)
    	    tableauList
  	Headline
    	    the constructor for the type TableauList
  	Usage
    	    tableauList(p,n)
    	    tableauList(p)
  	Inputs
    	    p:Partition
    	    	the shape for the tableaux
    	    n:ZZ
    	    	the number of tableaux in the list, if is not provided then the default value
	    	multinomial p is used. See multinomial.
  	Outputs
      	    :TableauList
            	an empty TableauList with space for n tableaux
  	Description
        
    	    Example
    	    	p = new Partition from {2,1}
    		y = youngTableau(p,{0,1,2})
		t = tableauList p
		addTableau(t,y)
		peek t 
		t1 = tableauList (p,5)
		addTableau(t1,y)
		peek t1

    Node
    	Key
	    (toListOfTableaux,TableauList)
	    toListOfTableaux
	Headline
	    converts an object of type TableauList into a list of YoungTableau objects
	Usage
    	    toListOfTableaux(tableaux)
  	Inputs
    	    tableaux:TableauList
  	Outputs
    	    :List
    		a list of the tableaux stored in the TableauList  
   	Description
    	    Example
        	p = new Partition from {2,1}
    		y1 = youngTableau(p,{0,1,2})
		y2 = youngTableau(p,{0,2,1})
		y3 = youngTableau(p,{1,2,0})
    		t = tableauList p
		addTableau(t, y1)
		addTableau(t, y2)
		addTableau(t, y3)
		toListOfTableaux t

    Node 
    	Key
    	    (tabloids, Partition)
	    tabloids
    	Headline
    	    the list of tabloids for a given partition
    	Usage
    	    tabloids(p)
    	Inputs
    	    p:Partition
    	Outputs
    	    :TableauList
	    	the list of tabloids
    	Description
    	
	    Text
	    	Tabloids are the equivalence class of tableaux under the row permutation equivalence relation.
	   	Two tabloids are row permutation equivalent if one can be obtained from the other by permuting elements in its rows.
	   	For every tabloid there is a unique representative such that its rows
	   	are increasing. This representatives are the ones calculated by the method
	   	tabloids().
		
		Tabloids are the basis of the permutation modules from which the Specht Modules are constructed.	
	    Example	    
	    	p = new Partition from {3,2}
	    	tabloids p

    Node 
        Key
    	    (standardTableaux, Partition)
	    standardTableaux
    	Headline	
    	    the list of standard tableaux of shape p
    	Usage
    	    standardTableaux(p)
    	Inputs
    	    p:Partition
    	Outputs
    	    :TableauList
	    	the list of standard tableaux
    	Description    	
	    Text
    	    	The standard tableaux of a given partition $\lambda$ are tableaux of shape p.
	    	Such that they are both row and column increasing. This set of tableaux are
 	    	very important because they are in bijection with the basis of the Specht module
	    	$S^\lambda$.	    
	    	
		The method calculates this tableaux recursively filling the cells of the Ferrer diagram
	    	and checking if the rows and columns are still increasing.	
	    Example	    
	    	p = new Partition from {3,2}
	    	standardTableaux p


    Node
    	Key
    	    (semistandardTableaux, Partition, ZZ)
	    semistandardTableaux
    	Headline
    	    the list of semistandard tableaux of shape p and filling with the numbers from 0 to n-1.
    	Usage
    	    standardTableaux(p,n)
    	Inputs
    	    p:Partition
    	    	the shape of the tableaux
	    n:ZZ
	    	a limit of the range of numbers that appear in the tableaux
    	Outputs
    	    :TableauList
		the list of semistandard tableaux
    	Description
	    Text
    	    	The semistandard tableaux are tableaux that are strictly decreasign in rows and
		weakly deacreasing in rows. 	
	    Example
    		p = new Partition from {3,2}
	    	semistandardTableaux (p,4)

    Node
    	Key
	    (readingWord,YoungTableau)
	    readingWord
	Headline
	    gives the reading word of a given tableau
	Usage
	    readingWord(y)
	Inputs
	    y:YoungTableau
	    	a young tableau
	Outputs
	    :List
	    	the reading word of the Young tableau
	Description
	    Text
	    	The reading word of a tableau is word obtain by reading each column from the bottom up and reading 
		the columns from left to right. The reading word is used to calculate the cocharge statistic of the given tableau.
		
	    Example
	    	p = new Partition from {3,2}
	    	y = youngTableau(p,{0,2,3,1,4})
	    	readingWord(y)


    Node
    	Key
	    (indexTableau,YoungTableau)
	    indexTableau
	Headline
	    the index tableau for a given tableau
	Usage
	    indexTableau(y)
	Inputs
	    y:YoungTableau
	Outputs
	    :YoungTableau
	    	the index tableau
    	Description
	    Text
	    	The index tableau is a filling obtained by the original tableau using the reading word.
		To every element in the reading word a number is given recursively in the following way.
		f(0) = 0 and f(k+1) = f(k) if k+1 appear to the right of k. Otherwise f(k+1)= f(k)+1.
		
		Finally the entries in the original tableau are replaced by the values of the function f.
	    
	    Example
	    	p = new Partition from {3,2}
	    	y = youngTableau(p,{0,2,3,1,4})
	    	readingWord(y)
		indexTableau(y)

    Node
    	Key
    	    (rowPermutationTableaux, YoungTableau)
	    rowPermutationTableaux
    	Headline
    	    the list of row permutations without repetitions in columns
    	Usage
    	    rowPermutationTableaux(y)
    	Inputs
    	    y:YoungTableau
    	    	a tableau, generally the index tableau of a standard tableau	

    	Outputs
    	    :List
		the list of all row permutations of the tableau
    	Description
	    Text
    	    	This list of tableaux is used to calculate more efficiently higher Specht polynomials.
		If any of the columns has a repetition then the associated term in the higher Specht polynomial
		for this row permutation is zero. This is why such permutations are ommited. 	

	    Example
		p = new Partition from {3,2}
	    	y = youngTableau(p, {0,2,1,3,4})
		ind = indexTableau y
		rowPermutationTableaux ind

    Node
    	Key
    	    (hookLengthFormula, Partition)
	    hookLengthFormula
    	Headline
    	    a formula for the number of standard tableaux
    	Usage
    	    hookLengthFormula(p)
    	Inputs
    	    p:Partition
    	    	a partition that indexes a Specht Module	

    	Outputs
    	    :ZZ
		the dimension of the Specht module S_\lambda
    	Description
	    Text
    	    	The hook length formula is a method that counts the number of
		standard tableaux of a given shape p. Therefore it counts the
		dimension of the associated Specht module.
		
	        For each Ferrer diagram and each cell (a,b) the hook at (a,b) is
		the set of cells that comprise (a,b) the cells that are below (a,b),
		and the cells that are to right of (a,b). The hook length of a hook h(a,b) is
		defined of the number of cells in the hook.
		
		If p is a partition of n then the hook length formula for p is
		$ n!/\prod_{(a,b)} h(a,b) $ 	

	    Example
		p = new Partition from {3,2}
	    	standardTableaux p
		hookLengthFormula p

    Node
    	Key
    	    (cycleDecomposition, List)
	    cycleDecomposition
    	Headline
    	    the cycle decomposition of a permutation
    	Usage
    	    cycleDecomposition perm
    	Inputs
    	    perm:List
    	    	a permutation of the list of numbers from 0 to n-1	

    	Outputs
    	    :List
		a doubly nested list with cycles of the permutation
    	Description
	    Text
    	    	Every permutation has a decomposition as the concatenation of disjoint cycles.
		This decomposition is used to calculate the conjugacy class of the permutation.
		
	    Example
		cycleDecomposition {0,1,2,3,4}		
		cycleDecomposition {1,3,2,0,4} 
		
    Node
    	Key
    	    (conjugacyClass, List)
	    conjugacyClass
    	Headline
    	    the conjugacy class of a permutation
    	Usage
    	    conjugacyClass perm
    	Inputs
    	    perm:List
    	    	a permutation of the list of numbers from 0 to n-1	

    	Outputs
    	    :Partition
		a partition that represents the conjugacy class of the permutation
    	Description
	    Text
    	    	The method first calculates the cycle decomposition of the permutation
		Then the conjugacy class is the partition given by the lengths of the
		cycles in the decomposition
		
	    Example
		cycleDecomposition {0,1,2,3,4}
		conjugacyClass 	{0,1,2,3,4}	
		cycleDecomposition {1,3,2,0,4} 
    	    	conjugacyClass 	{0,1,2,3,4}

    Node
    	Key
    	    multinomial
	    (multinomial, Tally)
	    (multinomial, List)
	    (multinomial, Partition)
    	Headline
    	    a formula for the multinomial coefficient
    	Usage
    	    multinomial(tal)
	    multinomial(l)
	    multinomial(p)
    	Inputs
    	    p:Partition
    	    	a partition	
    	    l:List
	    	a list of non negative numbers
	    tal:Tally
    	    	a tally from a list
		
    	Outputs
    	    :ZZ
		the multinomial coefficient of the given list
    	Description
	    Text
    	    	The multinomial coefficient is a generalization of the binomial coefficient.
		Given a list of number $k_1,\ldots,k_l$, the multinomial coefficient is
		$n!/(k_1!\ldots,k_l!)$ where $n = \sum k_i$. The multinomial coefficient is calculated
		because it gives the numbers of tabloids for a given partition.
		
		The list of numbers used to calculate the multinomial can be given
		as a list, a partition or a tally. This last option was added to optimize
		this calculation.

	    Example
		p = new Partition from {2,2}
	    	tabloids p
		multinomial {2,2}
		multinomial tally {2,2}


    Node
    	Key
    	    (rowStabilizer,YoungTableau )
	    rowStabilizer
    	Headline
    	    the row stabilizer of the tableau
    	Usage
    	    rowStabilizer(y)
    	Inputs
    	    y:YoungTableau
    	Outputs
    	    :List
		a dubly nested list with the permutations in the row stabilizer
    	Description
	    Text
    	    	The row stabilizer of a tableau is the group of the permutations that fixes the rows of
		the tableau. In terms of tabloids it is the stabilizer of a tabloid under the action of the
		group of permutations S_n. This group is used in the calculation of polytabloids and Specht polynomials.
		

	    Example
		p = new Partition from {2,2,1}
	    	y = youngTableau(p,{0,3,1,4,2})
		rowStabilizer y

    Node
    	Key
    	    (columnStabilizer,YoungTableau )
	    columnStabilizer
    	Headline
    	    the column stabilizer of the tableau
    	Usage
    	    columnStabilizer(y)
    	Inputs
    	    y:YoungTableau
    	Outputs
    	    :List
		a doubly nested list with the permutations in the column stabilizer
    	Description
	    
	    Example
		p = new Partition from {2,2,1}
	    	y = youngTableau(p,{0,3,1,4,2})
		columnStabilizer y
    	SeeAlso
	    rowStabilizer

    Node
    	Key
    	    permutationSign
	    (permutationSign,List )
	    (permutationSign,Partition)
    	Headline
    	    the sign of a permutation
    	Usage
    	    permutationSign(perm)
    	Inputs
    	    perm:List
	    	a permutation of the numbers from 0 to n-1
	    p:Partition
	    	a partition that represents the conjugacy class of the permutation 
    	Outputs
    	    :ZZ
		1 or -1, the sign of the permutation
    	Description
	    Text
	    	Every permutation can be decompose as a product of transpositions.
		This decomposition is not unique, however the parity of the number
		of transpositions that appears in the decomposition is always the same.
		Thus the sign is defined as $(-1)^l$ where $l$ is the number of transposition.
	    	
		The sign can be calculated if the cycle decomposition if known because
		the sign is multiplicative and the sign of a $k$-cycle is $(-1)^(k+1)$.
		This is the way the method permutationSign calculates the sign.
		
		The sign permutation is used to calculate polytabloids and higher Specht polynomials.
		
	    Example
		perm = {2,1,4,3,0}
		c = cycleDecomposition perm
		permutationSign perm
		perm2 = {4,2,1,0,3}
    	    	c2 = cycleDecomposition perm2
		permutationSign perm2
    	    	
    Node
    	Key
	    SpechtModuleElement
	    (symbol *,QQ, SpechtModuleElement)
	    (symbol *,ZZ, SpechtModuleElement)
	    (trim,SpechtModuleElement)
	    (symbol +,SpechtModuleElement, SpechtModuleElement)
	    (symbol -,SpechtModuleElement, SpechtModuleElement)
	    (terms,SpechtModuleElement)
	    (symbol SPACE,List, SpechtModuleElement)
    	    (net, SpechtModuleElement)
	Headline
    	    the class of Specht Module elements
	Description
	    Text    	
		Polytabloids of shape $p$ are elements of the module of tabloids of the form 
		$\sum_{\tau \in C(T)}\sum_{\sigma \in R(T)}sgn(\tau) \tau\sigma(T)$
		where T is a tabloid of shape $p$.
		
		The set of polytabloids generates the Specht Module of shape $p$.
		
		In other words the element in a SpechtModule are linear combinations of
		polytabloids. This is the way such elements are implemented in this package.
	    
	    	The constructor takes just one polytabloid and a coefficient
	    Example
	    	p = new Partition from {3,2,1}
		y = youngTableau(p,{2,0,3,4,5,1})
		e = spechtModuleElement(y,-2)
	    Text
	    	More complex elements can be made by adding or substracting previously build elements
		and multiplying by any element of the base field (which is assumed to be \mathbb{Q}).
	    Example
	    	y2 = youngTableau(p,{5,0,2,4,1,3})
		e2 = spechtModuleElement(y2)
		e+e2
		e-e2
		3*oo
	    Text
	    	The element SpechtModuleElement is implemented as a MutableHashTable.
		The keys are the filling of the tableaux that label the polytabloids and they
		point to their respective coefficients
	    Example
	    	peek oo
	        peek ooo#values 
	    Text
	    	The method terms is used to retrieve the polytabloid with their respective coefficient.
		This is given as a list of pairs of tableaux and coefficients.
	    Example
	    	terms (3*(e-e2))
	    Text
	    	A method was implemented to apply a permutation to a SpechtModuleElement.
		The action is defined by permuting the entries of the tableaux that label the 
		polytabloids.
	    Example
	    	{0,1,2,3,4,5} (3*(e-e2))
		{1,0,2,3,4,5} (3*(e-e2))
 	SeeAlso
 	    spechtModuleElement

	        
    Node
    	Key
    	    spechtModuleElement
	    (spechtModuleElement,YoungTableau,QQ )
	    (spechtModuleElement,YoungTableau,ZZ )
	    (spechtModuleElement,YoungTableau)
	    
    	Headline
    	    the constructor for the class SpechtModuleElement
    	Usage
    	    spechtModuleElement(y,n)
	    spechtModueElement(y)
    	Inputs
    	    y:YoungTableau
	    	the label of the polytabloid
	    n:ZZ
	    	a number. If not specified then it is assumed to be a 1.
	    m:QQ
	    	a number. If not specified then it is assumed to be a 1.
    	Outputs
    	    :SpechtModuleElement
		an element of the form n*poly_y, where poly_y is the polytabloid labeled by the tableau y.
    	Description
	    Text	
		The basic constructor builds a SpechtModuleElement from just one polytabloid and
		its respective coefficient.
	    Example
		p = new Partition from {3,2,1}
		y = youngTableau(p,{2,0,3,4,5,1})
		spechtModuleElement(y,-2)
		spechtModuleElement(y)

    Node
    	Key
    	    garnirElement
	    (garnirElement,YoungTableau, ZZ,ZZ,ZZ )
	    (garnirElement,YoungTableau,ZZ )
	    (garnirElement,YoungTableau)
	    
    	Headline
    	    a SpechtModuleElement that is equal to zero
    	Usage
    	    garnirElement(y,coef,a,b)
	    garnirElement(y,coef)
	    garnirElement(y)
    	Inputs
    	    y:YoungTableau
	    	a tableau that labels a polytabloid
	    a:ZZ
	    	the row of the descent
	    b:QQ
	    	the column of the descent
	    coef:ZZ
	    	the coefficient of the polytabloid
    	Outputs
    	    :SpechtModuleElement
		an element which is equal to zero.
    	Description
	    Text	
		A Garnir element is an element which is constructed to remove row descents from a tableau.
		Given a tableau $T$, the Garnir element is defined for a subset $A$ of the $i$th column and a subset $B$ of the $i+1$ column.
		It is defined as $ \sum_{\pi} sgn(\pi)\pi(T)$. The  $\pi$ are called transversals. They are a set of permutations such that
		$S_{A \cup B}$  is the disjoint union of  $\pi(S_A \times S_B)$. 
		  
		The identity can always be chosen as a transversal for any pair of sets. Therefore the original tableau $T$ appears along side other tableaux which are
		closer to being standard. Another property is that this element is equal to zero. Therefore the original polytabloid $e_T$ can be written as
		$ e_T = -\sum_{\pi \neq id} sgn(\pi)\pi(e_T)  $ 
	    
	    	In this implementation the $i$th column is taken to be the parameter b. The set $A$ is all the cells in the $i$th column from the a-th row to the bottom.
		The set $B$ is all the cells in the $i+1$ column from the a-th row to the top.
		
		If the number (a,b) are not specified then they are taken as the coordinates of the first row descent of $T$
	    Example
		p = new Partition from {3,2,1}
		y = youngTableau(p,{1,2,3,5,4,6})
		garnirElement y
    	SeeAlso
    	    firstRowDescent

    Node
    	Key
    	    straighteningAlgorithm
	    (straighteningAlgorithm, SpechtModuleElement )
	    (straighteningAlgorithm,YoungTableau,ZZ )
	    (straighteningAlgorithm,YoungTableau)
	    
    	Headline
    	    an algorithm for expressing any polytabloid as linear combinations of standard polytabloids
    	Usage
    	    straighteningAlgorithm(ele)
	    straighteningAlgorithm(y,coef)
	    straighteningAlgorithm(y)
    	Inputs
	    ele:SpechtModuleElement
	    	a SpecthModuleElement
    	    y:YoungTableau
	    	a tableau that labels a polytabloid
	    coef:ZZ
	    	the coefficient of the polytabloid
    	Outputs
    	    :SpechtModuleElement
		the same SpechtModuleElement written as a linear combination of standard polytabloids 
    	Description
	    Text	
		The straigtening algorithm works by finding the first term that is not standard. Then, taking as coordinates
		the first row descent, it calculates the Garnir element of this tableaux. It then rewrites
		the SpechtModuleElement substituting the term by the linear combination given by the garnir element.
	    Example
		p = new Partition from {3,2,1}
		y = youngTableau(p,{1,2,3,5,4,6})
		garnirElement y
    	SeeAlso
	    garnirElement


    Node
    	Key
	    (sortColumnsTableau, YoungTableau)
	    
    	Headline
    	    a method for 
    	Usage
    	    sortColumnsTableau(y)
    	Inputs
    	    y:YoungTableau
    	Outputs
    	    :ZZ
		the sign of the permutation that sorts the columns of the tableau
    	Description
	    Text	
    	    	This method sorts the columns of the tableau and retrieves the sign of the associated permutation
	    Example
		p = new Partition from {2,2,1}
		y = youngTableau(p,{0,1,4,3,2})
		sortColumnsTableau y
		y

    Node
    	Key
	    (sortColumnsTableau, SpechtModuleElement)
    	    sortColumnsTableau
	    
    	Headline
    	    a method for sorting the columns of the tableaux in a SpechtModuleElement 
    	Usage
    	    sortColumnsTableau(ele)
    	Inputs
    	    ele:SpechtModuleElement
    	Outputs
    	    :null
    	Description
	    Text	
    	    	This method sorts the columns of every tableaux that appears as a term of the SpechtModuleElement.
		The corresponding sign of the sort is multiplied to the coefficient of the respective term.
		The method returns null but changes the SpechtModuleElement that was input as a parameter.
	    Example
		p = new Partition from {2,2,1}
		y1 = youngTableau(p,{0,1,4,3,2})
		y2 = youngTableau(p,{0,3,4,1,2})
		ele = spechtModuleElement(y1)-spechtModuleElement(y2)
		sortColumnsTableau ele
		ele
		
		
		
    Node
    	Key
	    (firstRowDescent, YoungTableau)
    	    firstRowDescent
	    
    	Headline
    	    retrieves the first row descent of a young tableau
    	Usage
    	    firstRowDescent y
    	Inputs
    	    y:YoungTableau
    	Outputs
    	    a:ZZ
	    	the row of the row descent or -1 if there is no row descent
	    b:ZZ
	    	the column of the row descent or -1 if there is no row descent
	    
    	Description
	    Text	
    	    	A row descent is defined to be a cell (a,b) in a tableau $T$ such that T_(a,b)>T_(a,b+1).
		This method reads by columns from left to rigth and each column is read from the top down until the first row descent is found.
		If no row descent is found the pair (a,b)= (-1,-1) is returned.
	    Example
		p = new Partition from {3,2,1}
		y = youngTableau(p,{1,2,3,5,4,6})
		firstRowDescent y
		y2 = youngTableau(p,{1,2,4,3,5,6})
		firstRowDescent y2

    Node
    	Key
	    (cardinalityOfConjugacyClass, Partition)
    	    cardinalityOfConjugacyClass
	    
    	Headline
    	    the size of the conjugacy classes of S_n
    	Usage
    	    cardinalityOfConjugacyClass p
    	Inputs
    	    p:Partition
	    	a partition that indexes a conjugacy class of S_n
    	Outputs
    	   :ZZ
	       the size of the conjugacy class  
    	Description
	    Text	
    	    	The formula for this classes is obtained by the Orbit-Stabilizer lemma applied for S_n
		with the action of conjugation.
		
		For a partition $p$ this formula is $n!/(\prod_i (\lambda_i )!i^\lambda_i$, where $\lambda_i$ denotes the number
		    of parts in $p$ that are equal to $i$.  
	    Example
		p1 = new Partition from {3,2,1}
		cardinalityOfConjugacyClass p1
		p2 = new Partition from {1,1,1,1,1}
		cardinalityOfConjugacyClass p2
		
		
    Node
    	Key
	    matrixRepresentation
	    (matrixRepresentation, List, TableauList)
    	    (matrixRepresentation, List, Partition)
	    (matrixRepresentation,TableauList)
	    (matrixRepresentation,Partition)
	    
    	Headline
    	    the matrix representation of a permutation in the Specht Module
    	Usage
    	    matrixRepresentation(perm,standard)
	    matrixRepresentation(perm,parti)
	    matrixRepresentation(standard)
	    matrixRepresentation(parti)
	    
    	Inputs
    	    perm:List
	    	a permutation
	    standard:TableauList
	    	a list of standard tableaux of a given partition
	    parti:Partition
	    	a partition
	    
    	Outputs
    	   :Matrix
	       the matrix representation of the given permutation in the Specht module index by the given partition
	   :HashTable
	       if no permutation is given then it calculates the representation for all the permutations in S_n
    	Description
	    Text	
    	    	The matrix representation for a permutation is calculated by studying the action of the permutation
		on the basis of standard polytabloids.
		
		The permuted polytabloids are then written as a linear combination of standard polytabloids using the
		straightening algorithm.
	    Example
		p = new Partition from {2,1}
		l = {0,2,1}
		matrixRepresentation (l,p)
		stan = standardTableaux p
		matrixRepresentation (l,stan)
    	    	matrixRepresentation stan
		
		
    Node
    	Key
	    permutePolynomial
	    (permutePolynomial, List, RingElement)
    	    (permutePolynomial, List, Product)
	    (permutePolynomial, List, Sum)
	    (permutePolynomial, List, Power)
    	Headline
    	    permutes a RingElement or a PolynomialExpression of RingElements
    	Usage
    	    permutePolynomial(perm,f)
	    permutePolynomial(perm,prod)
	    permutePolynomial(perm,s)
	    permutePolynomial(perm,pow)
	    
    	Inputs
	    
    	    f:RingElement
	    	a ring element
	    prod:Product
	    	a Product expression
	    s:Sum
	    	a sum expression
	    pow:Power
	    	a power expression
	    perm:
	    	a permutation
    	Outputs
    	   :RingElement
	       the result of applying perm to f  
	   :Expression
	       the result of applying f to the given expression
    	Description
	    Text
	    	This method applies permutations to polynomial ring elements by permuting the variables.  
	    	Therefore the size of the permutation must be equal to the number of generators of the ring of the elements.
	    Example
		R = QQ[x_0..x_4]
		l = {1,0,2,3,4}
		f = x_1*x_2*x_3
		permutePolynomial(l,f)
	    Text
	    	This method can also permute polynomial expressions that are constructed from ring elements
		either by sums, products or powers.
	    Example
	    	ex = factor(x_1*x_2*x_3)+factor(x_1*x_3*x_4)
    	    	permutePolynomial(l,ex)		

    				
    Node
    	Key
	    vandermondeDeterminant
	    (vandermondeDeterminant, List,PolynomialRing)
    	    
    	Headline
    	   the vandermonde determinant for a set of generators of a ring
    	Usage
    	    vandermondeDeterminant(l,R)
    	
	Inputs
	    R:PolynomialRing
	    
    	    l:List
	    	a subset of the indices of the generators of R
    	    AsExpression=>Boolean
	    	a Boolean value, default value is false. If true it returns the determinant as a product expression
		This is a particularly useful way to reduce the size of the object since a Vandermonde determinant
		has n! terms but only n*(n-1)/2 factors.
	Outputs
    	   :RingElement
	       the determinant of the Vandermonde matrix formed by the generators indexed by l. 
    	Description
	    Text	
    	    	A Vandermonde matrix is a matrix of $n$ elements is constructed by putting in each column
		all the powers from 0 to $n-1$ of each of the elements.
		
		If $x_i$ are the elements used to construct the matrix then it can be proven that the determinant
		has the following form.
		
		$\prod_{0 \leq i < j < n} (x_j-x_i) $
		  
	    Example
		R = QQ[x_0..x_3]
		vandermondeDeterminant({0,2,3},R)
    	    	factor oo
		
	        
    Node
    	Key
	    (spechtPolynomial,YoungTableau, PolynomialRing)
    	    spechtPolynomial
    	Headline
    	   the Specht polynomial indexed by a standard tableau 
    	Usage
    	    spechtPolynomial(y,R)
    	
	Inputs
	    y:YoungTableau
	    	
	    R:PolynomialRing
	    	
	Outputs
    	   :RingElement
	     the Specht polynomial  
    	Description
	    Text	
    	    	Specht polynomials were the original objects that gave rise to the Specht modules.
		The Specht polynomial of a tableau $T$ is product of the Vandermonde determinant of the variables
		index by the columns of the tableau.
		  
	    Example
		R = QQ[x_0..x_4]
		p = new Partition from {2,2,1}
		y = youngTableau(p,{0,3,1,4,2})
		spechtPolynomial(y,R)
    	    	factor oo
	     		

    Node
    	Key
	    (spechtPolynomials,Partition, PolynomialRing)
    	    spechtPolynomials
	    
    	Headline
    	   the set of all Specht polynomial indexed by standard tableaux of shape p 
    	Usage
    	    spechtPolynomials(p,R)
    	
	Inputs 
    	    p:Partition
	  
	    R:PolynomialRing
	   
	Outputs
    	   :HashTable
	     a hash table with the polynomials index by the filling of their respective tableaux 
    	Description
	    Text
	    	The set of all the Specht polynomials for standard tableaux of a given shape p forms a basis for a module which is isomorphich to 
		the Specht module indexed by p.
	   
	   Example
		R = QQ[x_0..x_4]
		p = new Partition from {2,2,1}
		specht = spechtPolynomials(p,R)
		specht = applyKeys(specht, y-> youngTableau(p,y));
		applyValues(specht, f-> factor f)
    	    	

    Node
    	Key
	    (indexMonomial,YoungTableau, YoungTableau,PolynomialRing)
    	    indexMonomial
	    
    	Headline
    	   a monomial that represents an index tableau 
    	Usage
    	    indexMonomial(S,T,R)
    	
	Inputs
	    S:YoungTableau
	    
    	    T:YoungTableau
	    
	    R:PolynomialRing
	    
	Outputs
    	   :RingElement 
    	Description
	    Text
	    	The index monomial is used in the construction of higher Specht polynomials.
	        To calculate the index monomial first the index tableau of $S$, $i(S)$ is calculated.
		Then the monomial is calculated as $x_T^{i(S)}$. This is a monomial with the variables as they appear in T
		with the exponents that appear in $i(S)$.
	   
	   Example
		R = QQ[x_0..x_4]
		p = new Partition from {2,2,1}
		S  = youngTableau(p,{0,2,1,3,4})
		T  = youngTableau(p,{0,1,2,3,4})
		ind = indexTableau(S)
		indexMonomial(S,T,R)
    	SeeAlso
	    indexTableau
	    
    Node
    	Key
	    (higherSpechtPolynomial,YoungTableau, YoungTableau,PolynomialRing)
    	    higherSpechtPolynomial
	    
    	Headline
    	   the higher Specht polynomial index by the pair of standard tableaux (S,T) 
    	Usage
    	    higherSpechtPolynomial(S,T,R)
	Inputs
	    S:YoungTableau
	    
    	    T:YoungTableau
	    
	    R:PolynomialRing
	    
	    AsExpression => Boolean
	    	An optional argument that allows to write the polynomial as an expression
	    Robust => Boolean
	    	An optional argument to decide the strategy for calculating the polynomial.
	Outputs
    	   :RingElement
	       if AsExpression == false
	   :Expression 
	       if AsExpression == true
    	Description
	    Text
	    	Higher Specht polynomials are a family of polynomials that form a basis of the coinvariant algebra for the symmetric group.
		The coinvariant algebra is isomorpich as a $S_n$ module to the regular representation of $S_n$. Therefore
		every Specht modules appears as an irreducible module in this algebra with multiplicity $f^\lambda= {\rm dim} \, S^\lambda $. 
		Higher Specht polynomials decompose this algebra into its irreducible submodules. 
		
		Higher Specht polynomials are indexed by pairs of standard tableaux of the same size.
		The usual construction of these polynomials is as follows.
		
		1. Given two tableaux (S,T) of shape $\lambda$ the index tableau i(S) is calculated and the index monomial $x_T^{i(S)}$ is calculated.
		2. The Young symmetrizer $\sum_{\tau \in C(T)} \sum_{R(T)} sgn(\tau)\sigma$ is applied to the index monomial.  
		
		The algorithm based on this construction can be used in this method with the optional input
		Robust => true
		
		A second algorithm  for this polynomials is based on a study on the structure of this polynomials.
		
		The outline of this construction is as follow.
		
	        1. Calculate the index tableau $i(S)$.
    		2. Calculate all row permutations of $i(S)$ such that no entries in the same column are equal.
    		3. For each different tableau $\sigma(i(S))$ in the previous step order the columns in descending order making sure to calculate the sign of the permutation used. 
    		4. For each column in $\sigma(i(S))$ determine the Schur polynomial with partition $\lambda = (a_p-p, \ldots,a_i-i ,\ldots ,a_0) $.
    		5. For all columns multiply the polynomials obtained in Step 4. Multiply this by the sign obtained in Step 3.
    		6. For all tableaux $\sigma(i(S))$, add all polynomials obtained in Step 5.
    		7. Multiply the polynomial in Step 6 by the Specht polynomial of T.  
	   
	   Example
		R = QQ[x_0..x_4]
		p = new Partition from {2,2,1}
		S  = youngTableau(p,{0,2,1,3,4})
		T  = youngTableau(p,{0,1,2,3,4})
		time higherSpechtPolynomial(S,T,R)
		time higherSpechtPolynomial(S,T,R, Robust => false)
		time higherSpechtPolynomial(S,T,R, Robust => false, AsExpression => true)

    	SeeAlso
	    spechtPolynomial
	    indexMonomial
	    columnStabilizer
	    rowStabilizer
	    rowPermutationTableaux
	    
    Node
    	Key
	    higherSpechtPolynomials
	    (higherSpechtPolynomials,YoungTableau,PolynomialRing)
	    (higherSpechtPolynomials,YoungTableau,TableauList,PolynomialRing)
	    (higherSpechtPolynomials,Partition,PolynomialRing)
	    (higherSpechtPolynomials,PolynomialRing)
    	    
    	Headline
    	   a method that gives sets of higher Specht polynomials 
    	Usage
    	    higherSpechtPolynomial(S,R)
	    higherSpechtPolynomial(S,standard,R)
	    higherSpechtPolynomial(p,R)
	    higherSpechtPolynomial(R)
	Inputs
	    S:YoungTableau
	    	    
	    R:PolynomialRing
	    
	    standard:TableauList
	    	The list of standard tableaux of the same shape as S
	    p:Partition
	    	
	    AsExpression => Boolean
	    	An optional argument that allows to write the polynomial as an expression
	    Robust => Boolean
	    	An optional argument to decide the strategy for calculating the polynomial.
	Outputs
    	   :HashTable
	       a hash table with multiple levels depending on the input
    	Description
	   Text
	    	 This methods returns higher Specht polynomials sorted in hash tables depending on the input received.
		 
		 If the input is just a YoungTableau $S$ of shape $\lambda$ and a PolynomialRing then it calculates the 
		 standard tableaux $ST(\lambda)$ and then stores all polynomials $F_T^S$ such that $T \in ST(\lambda)$.
		 The polynomials are stored in a hash table with the filling of $T$ as the key.
		 
		 The list $ST(\lambda)$ can be provided as an input. This is used to avoid repeating this calculation
		 when this method is called multiple times with the same shape $\lambda$.
		 
		 This set forms a basis for one of the copies of the Specht module $S^\lambda$.
	   
	   Example
		R = QQ[x_0..x_3]
	        p = new Partition from {2,2}
		S  = youngTableau(p,{0,2,1,3})
		higherSpechtPolynomials(S,R)
		stan = standardTableaux p
		higherSpechtPolynomials(S, stan,R)
	   Text	
	    	If only a partition $\lambda$ and a polynomial ring is given then the method calculates $ST(\lambda)$.
		Then it calculates all polynomials $F_T^S$ such that $S,T \in ST(\lambda)$.
		
		This is a basis for the isotypical component $\chi_\lambda$ in the coinvariant algebra of the symmetric group.

    	    	The polynomials are stored by calling for each $S \in \ST(\lambda) $ the previous method. The output is stored
		in another hash table with the key being the filling of the tableau $S$.
		  
	   Example
	       higherSpechtPolynomials(p,R)
	   Text
	       Finally if just a polynomial ring $R$ with $n$ elements is provided then the method calculates all higher Specht polynomials 
	       for all partitions $\lambda$ of $n$.
	       
	       The polynomials are calculated by calling the previous method for every partition of $n$ and storing the values in
	       a new hash table with the key being the partition.
	   Example
	       higherSpechtPolynomials(R)
	       
	       
    Node
    	Key
	    (generalizedVandermondeMatrix,List,List,PolynomialRing)
	    generalizedVandermondeMatrix
	Headline
	    the method for calculating generalized Vandermonde matrices
	Usage
	    generalizedVandermondeMatrix(indices,exponents,R)
	Inputs
	    indices:List
	    	a lits of the variables that appear in each column of the matrix
	    exponents:List
	    	a list of the powers that appear in each row of the matrix
	    R:PolynomialRing
	    
	Outputs
	    :Matrix
	Description
	    Text
    	    	Generalized vandermonde matrices allow the power in the rows to be different from the numbers
		from 0 to n-1.
	    Example
	    	R = QQ[x_0..x_4]
	    	M = generalizedVandermondeMatrix({0,2,3},{1,3,5},R)
		
	   Text
	       The determinant of these matrices divided by the Vandermonde determinant of the same rank is equal
		to a schur polynomial .
	   Example
		(determinant M)//vandermondeDeterminant({0,2,3},R) 
		
    Node
    	Key
	    (schurPolynomial,List,List,PolynomialRing)
	    schurPolynomial
	Headline
	    a method for constructing Schur polynomials
	Usage
	    generalizedVandermondeMatrix(indices,exponents,R)
	Inputs
	    indices:List
	    	a lits of the variables that appear in each column of the matrix
	    exponents:List
	    	a list of the powers that appear in each row of the matrix
	    R:PolynomialRing
	    
	Outputs
	    :Matrix
	Description
	    Text
    	    	Generalized vandermonde matrices allow the power in the rows to be different from the numbers
		from 0 to n-1.
	    Example
	    	R = QQ[x_0..x_4]
	    	M = generalizedVandermondeMatrix({0,2,3},{1,3,5},R)
		
	   Text
	       The determinant of these matrices divided by the Vandermonde determinant of the same rank is equal
		to a schur polynomial .
	   Example
		(determinant M)//vandermondeDeterminant({0,2,3},R)
		
		
    Node
    	Key
	    (generatePermutationGroup,List)
	    generatePermutationGroup
	Headline
	    a method for generating a permutation group given a set of generators
	Usage
	    generatePermutationGroup(gens)
	Inputs
	    gens:List
	    	a list of permutations
	    
	Outputs
	    :List
	    	the group generated by the given set of generators
	Description
	    Text
    	    	The method works by taking all multiplications of the elements in the set of generators. New elements
		that are found are added and the process is repeated until no new elements are found.
	    Example
	    	generatePermutationGroup {{1,0,2,3},{1,2,3,0}}
				
	    Text
	    	This method is used to calculate the size of each conjugacy classes for the groups.	
    Node
    	Key
	    representationMultiplicity
	    (representationMultiplicity,Tally,Partition,CharacterTable)
	    (representationMultiplicity,Tally,Partition)    
	Headline
	    the number of secondary invariants in a given irreducible representation			
	Usage
	    representationMultiplicity(tal,p,charTable)
	    representationMultiplicity(tal,p)
	Inputs
	    tal:Tally
	    	a tally with the number of elements in each conjugacy class of the group
	    p:Partition
	    	a partition that indexes an irreducible representation
	    charTable:CharacterTable
	    	optionally the character table of S_n. If it is not provided then it is calculated by the method
	Outputs
	    :ZZ
	    	the multiplicity of the trivial representation of the group described by tal in the irreducible representation of S_n indexed by p

	Description
	    Text
    	    	Since the given group $H$ is a subgroup of $S_n$, the restrictions of the Specht modules to $H$
		are also $H$-modules. The number of copies of the trivial representation of $H$ in each of this modules
		can be found by the formula for the inner product for characters applied to the characters of the previous modules.
		
		$\frac{1}{|H|}\sum_{C \in Cl(H)} |C|\chi(\sigma_c)$ 
		
		$Cl(H)$ is the set of conjugacy classes of $H$, $|C|$ is the size of the conjugacy class and $\sigma_c$ is a representative
		of the conjugacy class $C$.
			
	   Example
	    	generatePermutationGroup {{1,0,2,3},{1,2,3,0}}
   
///
end

    	
 
