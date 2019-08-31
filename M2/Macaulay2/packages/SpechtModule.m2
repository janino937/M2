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

export {"vandermondeDiscriminant"}
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

export {"Robust","AsExpression"}
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
    p:=partitions(n,n);
    for i to numColumns(C)-1 do(
        prod=prod+(C_(0,i))*(X_(0,i))*(cardinalityOfConjugacyClass(p#(i)));
    ); 
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
  s:=sum(size tableau)-(tableau#partition)#(ind#row);
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


SpechtModuleElement = new Type of HashTable 

spechtModuleElement = method()
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

straighteningAlgorithm = method(TypicalValue=> List)
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

garnirElement( YoungTableau) := tableau -> garnirElement(tableau,1)

sortColumnsTableau = method()
sortColumnsTableau YoungTableau := tableau -> (
    product(tableau#partition#0,i->sortColumn(tableau,i))
    )

sortColumnsTableau SpechtModuleElement := element ->
(
    scan (keys element#values, t -> (
	    y := youngTableau(element#partition,t);
	    --print net y;
	    sign:= sortColumnsTableau(y);
	    if(t != toList y#values) then (
		coef := sign*element#values#t;
		remove(element#values,t);
		element#values#(entries y) = coef;
		);
	    )
	)
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

vandermondeDiscriminant = method()
vandermondeDiscriminant(List,PolynomialRing):= (lista,R)->(
    variables := apply(lista,i-> R_i);
    product flatten apply (#lista, i->toList apply( (i+1)..(#lista-1),j-> (variables#j-variables#i) ) ) 
    )

spechtPolynomial = method()
spechtPolynomial ( YoungTableau, PolynomialRing ) := (tableau, R)-> (
    product (numcols tableau, i->vandermondeDiscriminant(tableau_i,R))
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
    ans:= R_0;
    if(o.Robust) then (
	monomial := indexMonomial(S,T,R);
    	sym:= sum (rowStabilizer T, sigma-> permutePolynomial(sigma,monomial));
    	polynomial:= sum (columnStabilizer T, tau -> permutationSign(tau)*permutePolynomial(tau,sym))*hookLengthFormula(S#partition)//(numgens R)!;
	if o.AsExpression then ans = factor polynomial else ans = polynomial 
    	)
    else (
	ans = R_1;
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


end


