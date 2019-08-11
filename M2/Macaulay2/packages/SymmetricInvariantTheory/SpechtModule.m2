load-- -*- coding: utf-8 -*-
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
export {"isLastIndex"}
export {"nextIndex"}

export {"hookLengthFormula"}

export {"changeElement"}
export {"addElement"}
export {"previousElementInRow"}
export {"previousElementInColumn"}
export {"getRow"}
export {"getColumn"}
export {"getElement"}
export {"next"}
export {"printTableau"}
export {"printTableaux"}
export {"changeLabels"}


export {"TableauList"}
export {"addTableau"}
export {"getTableau"}
export {"tabloids"}
export {"standardTableaux"}
export {"semistandardTableaux"}
export {"matrixRepresentation"}
export {"generalizedTableaux"}

export {"indexTableau"}
export {"signPermutation"}
export {"permutationsFixColumn"}
export {"permutationsFixRow"}
export {"columnStabilizer"}
export {"rowStabilizer"}
export {"cycleStructure"}
export {"combinations"}
export {"garnirElement"}
export {"orderColumnsTableau"}
export {"cardinalityOfConjugacyClass"}
export {"differentElementsInPartition"}

export{"multinomial"}
export {"straighteningAlgorithm"}

export {"firstRowDescent"}
export {"columnDominance"}
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
    tableau#index = {0,0,0};
    scan(0..sum(toList p)-1, i-> tableau#i = 0);
    tableau
)

youngTableau(Partition,List):= (p,L)->(
    if(sum toList p != #L) then error " Partition size does not match with the length of the list L";
    tableau:= new YoungTableau;
    tableau#partition =p;
    tableau#index = {0,0,0};
    if #L != 0 then (
    tableau#index = {#p-1,(last p)-1,sum(toList p)};
    scan(0..sum(toList p)-1, i-> tableau#i = L#i);
    );
    tableau
)

youngTableau(YoungTableau):= (tableau)->(
    t:= new YoungTableau; 
    for i to #keys(tableau)-1 do t#((keys(tableau))#i) = tableau#((keys(tableau))#i);
    t      
)

youngTableau(Partition,MutableList):= (p,L)->(
     if(sum toList p != #L) then error " Partition and List size do not match";
    tableau:= new YoungTableau;
    tableau#partition =p;
    tableau#index = {0,0,0};
    if #L!= 0 then (
    tableau#index = {#p-1,(last p)-1,sum(toList p)};
    scan(0..sum(toList p)-1, i-> tableau#i = L#i);
    );
    tableau
)

youngTableau(Partition,MutableMatrix):= (p,L)->(
    if(sum toList p != # (flatten entries L )) then error " Partition and List size do not match";
    tableau:= new YoungTableau;
    tableau#partition =p;
    tableau#index = {0,0,0};
    
    if (#L != 0) then (
    tableau#index = {#p-1,(last p)-1,sum(toList p)};
    
    scan(0..sum(toList p)-1, i-> tableau#i = L_(0,i));
    );
    tableau
)

youngTableau(Partition,Sequence):=(p,L)->(
    if(sum toList p != #L) then error " Partition and List size do not match ";
    tableau:= new YoungTableau;
    tableau#partition =p;
    tableau#index = {0,0,0};
    
    if (#L != 0) then (
    tableau#index = {#p-1,(last p)-1,sum(toList p)};
    
    scan(0..sum(toList p)-1, i-> tableau#i = L#i);
    );
    tableau
)

------
-- Methods for object tableau
------

changeLabels = method()

-- Assume that the initial values were then numbers from 0 to n-1
-- The labels are given in increasing order

changeLabels(YoungTableau,List):= (tableau, labels)-> (
    tab := youngTableau(tableau);
    for i to sum toList  tableau#partition-1 do (
	tab#i = labels#(tableau#i);
	);
    tab
    )

changeLabels(List,List) := (tableau, labels) ->(
    tab:= new MutableList;
    for i to #tableau-1 do (
	tab#i = labels#(tableau#i);
	);
    toList tab
    )


------
-- Gives a representation of the Young Tableau as a list of the rows in the
-- diagram.
------
tableauToList = method(TypicalValue => MutableList)
tableauToList(YoungTableau):= (tableau)->(
    L:= new MutableList;
    d:= 0;
    n:= #(tableau#partition);
    L#(n-1)=0; 
    for i to #(tableau#partition)-1 do (
        l:= new MutableList;
	l#((tableau#partition#i)-1)=0;
        for j to (tableau#partition#i)-1 do (
            l#j = tableau#d;
            d = d+1;
        );
        L#i = toList l;
    );
    toList L
)


------
-- Given a YoungTableau, it iterates its index so that it seats at the next position in the
--tableau. This assumes that the tableau if been read by rows.
------
nextIndex=method(TypicalValue=>YoungTableau)
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
addElement(YoungTableau, ZZ) := (tableau, n) -> (
    i := tableau#index#2;
    tableau#i = n;
    tableau = nextIndex(tableau);
    tableau
)


------
-- Changes the index to the given index.
------
setIndex = method(TypicalValue =>YoungTableau)
setIndex(List, YoungTableau) := (L,tableau)->(
    tableau#index = L;
    tableau
)

------
-- Given a tableau with an index, it gets the element thats to the right of the element
-- that the index is pointing to. In case there is no such element (for example when the
-- index points to first element in a row, it return 0)
------
previousElementInRow = method(TypicalValue => ZZ)
previousElementInRow(YoungTableau):= (tableau)->(
    
    e := -1;
    ind := tableau#index;
    if ind#1!=0 then e = tableau#(ind#2-1);
    e
)

------
-- Given a tableau with an index, it gets the element thats to above of the element
-- that the index is pointing to. In case there is no such element (for example when the
-- index points to an element in the first row, it return 0).
------
previousElementInColumn = method(TypicalValue => ZZ)
previousElementInColumn(YoungTableau):= (tableau)->(
    e:=-1;
    ind := tableau#index;
    p:= tableau#partition;
    if ind#0!=0 then e = tableau#(ind#2-p#(ind#0-1));
    e
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
maxPossibleNumber(YoungTableau):= (tableau) ->(
  ind:=tableau#index;
  s:=sum(toList tableau#partition)-(tableau#partition)#(ind#0);
  s= s+ind#1;
  s
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
maxPossibleNumberStandard(YoungTableau):= (tableau) ->(
  ind:=tableau#index;
  s:=sum(toList tableau#partition);
  for i from ind#0 to #(tableau#partition)-1 when ((tableau#partition)#(i) > ind#1 ) do (    
     s = s - (tableau#partition)#(i)+ind#1;
  );
  --s = s+1;
  s
)


maxPossibleNumbersSemistandard = method(TypicalValue => ZZ)
maxPossibleNumbersSemistandard(YoungTableau,ZZ):= (tableau,n)-> (
    
  ind:=tableau#index;
  s:=n;
  s = s - #(getColumn(tableau,ind#1))+ind#0;
  --s = s+1;
  s
    )

------
-- Gets the element in the position (i,j) of the young diagram.
-- i: row
-- j: column 
------

getElement = method()
getElement(YoungTableau, ZZ, ZZ):= (tableau,i,j) -> (
    ans:= 0;
    if(i < #(tableau#partition)) then (
        
        ind:= 0;
        if(j < tableau#partition#i) then ( 
            for  k to i-1 do (
                ind= ind + tableau#partition#k;
            );
            ans = tableau#(ind+j);
        )
        else (error "Index out of bounds ");
    
    )
    else( error "Index out of bounds" );
    ans   
)

next = method()
next YoungTableau:= tableau -> (
    
    ind:= tableau#index;
    ans:= tableau#(ind#2);
    nextIndex(tableau);
    )
------
-- Sets the element in the position (i,j) of the young diagram.
-- i: row
-- j: column 
------
setElement = method()
setElement(YoungTableau,ZZ,ZZ,ZZ):= (tableau,i,j,element) -> (
    ans:= 0;
    if(i < #(tableau#partition)) then (
        ind:= 0;
        if(j < tableau#partition#i) then ( 
            for  k to i-1 do (
                ind = ind + tableau#partition#k;
            );
            tableau#(ind+j)= element;
        )
        else (error "Index out of bounds ");
    
    )
    else( error "Index out of bounds" );
    true
    
)

------
-- Gives a list of all the elements in the row i 
------
getRow = method(TypicalValue => ZZ)
getRow(YoungTableau, ZZ):= (tableau, i) -> (
    ans:= 0;
    if i < #(tableau#partition) then (
        ind:= 0;
        for j to i-1 do(
            ind = ind+tableau#partition#j;
        );
        ans = new MutableList;
        for j from ind to (ind + (tableau#partition#i)-1) do(
            ans#(j-ind) = tableau#j,
        );
        ans = toList ans;
    )
    else error "Index out of bounds";
    ans
)

------
-- Gives a list of all the elements in the column i 
------
getColumn = method(TypicalValue => ZZ)
getColumn(YoungTableau, ZZ):= (tableau, i) -> (
    ans:= 0;
    if i < tableau#partition#0 then (
        ind:= 0;
        ans = new MutableList;
        for j to #(tableau#partition)-1 when (tableau#partition#j > i) do(
            ans#j = tableau#(ind+i);
            ind = ind+(tableau#partition#j);
        );
        ans = toList ans;
    )
    else error "Index out of bounds";
    ans
)


------
-- A method to give a graphical representation of a Young diagram. This method saves the
-- diagram in a mutable matrix and then prints the matrix. 
------
printTableau = method()
printTableau YoungTableau := tableau ->(
    matrix:= mutableMatrix(QQ,#(tableau#partition),tableau#partition#0);
    for i to numRows (matrix) -1 do(
    	row:= getRow(tableau,i);
	for j to #row-1 do(
	    matrix_(i,j)= row#j;    
	);	
    );
    print("");
    print(matrix);
)

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

printTableaux = method()
printTableaux(TableauList):= lista -> (
    
    l:= new MutableList;
    for k to lista#length-1 do(
	tableau1:= getTableau(lista,k);
	
	matrix1:= mutableMatrix(QQ,#(tableau1#partition),tableau1#partition#0);
    	for i to numRows (matrix1)-1 do(
    	    row:= getRow(tableau1,i);
	    for j to #row-1 do(
	    	matrix1_(i,j)= row#j;    
		);	
    	    );
	l#k = matrix1;
	);
    print("");
    print(toList l);
)

------
-- Adds a tableau to the list    .
------
addTableau = method(TypicalValue => ZZ)
addTableau(TableauList, YoungTableau):= (tableaux, tableau) ->(
   scan(0..sum(toList tableau#partition)-1, i-> (tableaux#matrix)_(tableaux#length,i) = tableau#i);
   tableaux#length = tableaux#length+1;
   tableaux
)

------
-- Retrieves a tableau from the list
------
getTableau = method(TypicalValue => ZZ)
getTableau(TableauList,ZZ) := (tableaux, n) -> (
    
    youngTableau(tableaux#partition,flatten entries tableaux#matrix^{n})
    ) 
------
-- MultiSet 
------

-- A strucuture that represents a list of elements with possible repetitions as pairs of the
-- the for (a,n) where a is an element and n is the number of times that it appears in the
-- list.
MultiSet = new Type of MutableHashTable;

-- Constructor 

multiSet = method()
multiSet(List) := (numbers) -> (
    num:= new MultiSet;
    for i to #numbers-1 do (
    	if not member(numbers#i,keys(num)) then
	    num#(numbers#i) = 0;
	num#(numbers#i)=num#(numbers#i)+1;    
    );
    num#basis = keys(num);
    num#index = 0;
    num
)

setIndex(MultiSet,ZZ):= (numbers, ind) -> (
      n := -1;
      if(ind>=0) then(
      	  for i from ind to #(numbers#basis)-1 when(n<0) do(
	     j := (numbers#basis)#i;
	     if(numbers#j!=0) then (n = i); 
	  );
      );
      numbers#index = n;
)

-- Methods

-----
-- This method codes 
-----
hookLengthFormula = method(TypicalValue =>ZZ)
hookLengthFormula Partition := parti -> (
    
    prod := (sum toList parti)!;
    m := #parti;
    if m!= 0 then (
    for i to parti#0-1 do(
        mn :=m;
        for j to m-1 do (
            r:= parti#(m-j-1)-i;
            --print (m,i,j,r,prod);
            prod = prod//(r+j);
            if(r==1) then mn = m-j-1;
        );
        m=mn;
    
    );
);
    prod
)

-----
-- This method codes 
-----
cycleStructure = method(TypicalValue => Partition)
cycleStructure List := perm ->(
    ans:= new MutableList;
    rec:= new MutableList;
    for i to #perm-1 do (rec#i = 0);
    
    m := 0;
    ind:= 0;
    rec#(m) = 1;
    while m<#perm do (
        n:= perm#(m);
        length:= 1;
        while n != m do(
            rec#(n) = 1;
            length = length+1;
            n = perm#(n);
        );
        ans#ind = length;
        ind = ind+1;
        
        for i from m to #perm-1 when rec#i==1 do 
        (
            m = i;
        );
        m = m+1;
        rec#(m) = 1;
    );
    new Partition from (reverse sort toList ans)
)

copyOfMultiSet = method()
copyOfMultiSet(MultiSet):=(numbers)->(
    
    newList:= new MultiSet;
    newList#basis = numbers#basis;
    newList#index = 0;
    for i to #(numbers#basis)-1 do(
    	j := (numbers#basis)#i;
	newList#j = numbers#j;	
    );
    newList
)  

nextIndex(MultiSet):=(numbers)->(
      n := -2;
      if(numbers#index>=0) then(
      	  for i from numbers#index to #(numbers#basis)-1 when(n<0) do(
	     j:= (numbers#basis)#i;
	     if numbers#j!=0 then n = i; 
	  );
      );
      numbers#index = n+1;
      n+1
)

getElement(MultiSet):= (numbers)-> (
    
    ind := numbers#index-1;
    base:= numbers#basis;
    base#ind
)


-----
-- Method that generates the list of all tabloids of a given partition.
-- A filling of young diagram is a tableau if it is increasing in rows.
-- The number of tableaux is given by the multinomial coefficient associated to the partition
-- nC(p_1,p_2,..,p_k).
-----
tabloids = method(TypicalValue => TableauList)
tabloids(Partition) := p->(
    size:=sum toList p;
    tableaux :=tableauList(p,size);
    if(size!= 0) then(
    nums := toList(0..size-1);
    tableau:= youngTableau(p);
    tableaux = recursiveTabloids(nums,tableau,tableaux);
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
recursiveTabloids = method(TypicalValue => TableauList)
recursiveTabloids(List,YoungTableau , TableauList):= (numbers, tableau, tableaux) -> (
    if(isLastIndex(tableau)) then 
    (
       print(numbers);
       if previousElementInRow(tableau)< numbers#0 then
       ( 
           tableau = addElement(tableau,numbers#0);
           tableaux = addTableau(tableaux,tableau);
	   printTableau(tableau)
       )
    ) else
    (
	maximum:= maxPossibleNumber(tableau);
      for i from 0 to #numbers-1 when (numbers#i < maximum+1)  do (
        
            if(numbers#i>previousElementInRow(tableau)) then
            (
                tableauNuevo := youngTableau(tableau);
		addElement(tableauNuevo,numbers#i);
		numbers2 := delete(numbers#i,numbers);
		printTableau(tableauNuevo);
                tableaux = recursiveTabloids(numbers2,tableauNuevo,tableaux);
            );
        );  
    );
    tableaux
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
    tableaux = recursiveStandardTableaux(nums,tableau,tableaux);
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
recursiveStandardTableaux(List,YoungTableau,TableauList):= (numbers, tableau, tableaux) -> (
    if(isLastIndex(tableau)) then 
    (
       if (previousElementInRow(tableau) < numbers#0) and (previousElementInColumn(tableau) < numbers#0) then
       ( 
           tableau = addElement(tableau,numbers#0);
           tableaux = addTableau(tableaux,tableau);
       )
    ) else
    (
	maximum:= maxPossibleNumberStandard(tableau);
        for i from 0 to #numbers-1 when (numbers#i < maximum+1)  do (
        
            if(numbers#i>previousElementInRow(tableau) and numbers#i>previousElementInColumn(tableau) ) then
            (
                tableauNuevo := youngTableau(tableau);
		addElement(tableauNuevo,numbers#i);
		numbers2 := delete(numbers#i,numbers);
                tableaux = recursiveStandardTableaux(numbers2,tableauNuevo,tableaux);
            );
        );  
    );
    tableaux
)


semistandardTableaux = method(TypicalValue => TableauList)
semistandardTableaux(Partition,ZZ) := (p,n)->(
    size:=sum(toList p);
    tableaux :=tableauList(p,n^size);
    if size!=0 then (
    nums := toList(0..size-1);
    tableau:= youngTableau(p);
    tableaux = recursiveSemistandardTableaux(n,tableau,tableaux);
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
recursiveSemistandardTableaux(ZZ,YoungTableau,TableauList):= (maxNumber, tableau, tableaux) -> (
    if(isLastIndex(tableau)) then 
    (
	maximum:=maxPossibleNumbersSemistandard(tableau,maxNumber);
	for i from max(max(previousElementInRow(tableau),0),previousElementInColumn(tableau)+1) to maximum do(
          tableauNuevo:= youngTableau(tableau);
	  --printTableau(tableauNuevo);
	  addElement(tableauNuevo,i);
	  --print(tableauNuevo#index);
           tableaux = addTableau(tableaux,tableauNuevo);
	   );
       
    ) else
    (
	maximum= maxPossibleNumbersSemistandard(tableau,maxNumber);
        for i from max(max(previousElementInRow(tableau),0),previousElementInColumn(tableau)+1) to maximum do(
        
             tableauNuevo := youngTableau(tableau);
	     addElement(tableauNuevo,i);
	    -- print(tableauNuevo#index);
	     tableaux = recursiveSemistandardTableaux(maxNumber,tableauNuevo,tableaux);
        );  
    );
    tableaux
)

-----
-- This method codes 
-----
indexTableau = method()
indexTableau(YoungTableau):= tableau -> (
    rec := new MutableList;
    rec#(sum(toList tableau#partition)-1)=0;
    ind:=0;
    for i to (tableau#partition#0)-1 do (
        col := getColumn(tableau,i);
        for j from 0 to #col-1 do (
            rec#ind = col#(-j-1);
            ind= ind+1;
        );
    );
    ind = 0;
    m:= 0;
    index := new MutableList;
    while m < sum(toList tableau#partition) do(
        for i to #rec -1 do(
            if(rec#i == m) then (
                m = m+1;
                index#i = ind;
                )
        );
            ind = ind +1;
        );
    ans:= youngTableau(tableau#partition);
    ind = 0;
    for i to (tableau#partition#0)-1 do (
	col := getColumn(tableau,i);
        for j from 0 to #col-1 do (
            setElement(ans, #col-j-1,i,index#ind);
            ind = ind+1
        );
    );
    ans   
)

------
-- Checks whether the element is already stored in the column of a tableau. This method
-- used for the recursive calculation of index tableaus.
------
notInColumn = method()
notInColumn(YoungTableau,ZZ):= (tableau,element ) -> (
    ans:= true;
    col:= (tableau#index)#1;
    column := getColumn(tableau,col);
    for i to #column-1 when  ans and (column#i!=(-1)) do(
    	if( column#i == element  ) then ans= false;	    
    );
    ans
)


-----
-- Method that generates the list of all index tableaux of a given Index Tableau.
-- An index tableau can have repetitions of the numbers in its slots.
-- The method calculates all the different tableaus that can be obtained by permuting the
-- elements in the rows, in such a way that all elements in the columns are different.
-----
generalizedTableaux = method()
generalizedTableaux(YoungTableau) := (tableau)->(
    --Assuming all tableaus have size greater or equal to one.
    size:=sum(toList tableau#partition);	
    maxNumberOfTableaus:=1;
    for i to #(tableau#partition)-1 do (
	numRow:= getRow(tableau,i);
	composition:= multiSet(numRow);
    	maxNumberOfTableaus=maxNumberOfTableaus*factorial(tableau#partition#i);
	    
	for j to #(composition#basis)-1 do(
	    k:= (composition#basis)#j;
	    maxNumberOfTableaus = maxNumberOfTableaus//factorial(composition#k);
	       
	);	
    );
    tableaux :=tableauList(tableau#partition,maxNumberOfTableaus);
    newTableau:= youngTableau(tableau#partition,size:(-1));
    setIndex({0,0,0},newTableau);
    nums:= multiSet(getRow(tableau,0));
    tableaux = recursiveGeneralizedTableaux(tableau,nums,newTableau,tableaux);
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
recursiveGeneralizedTableaux = method(TypicalValue => TableauList)
recursiveGeneralizedTableaux(YoungTableau, MultiSet ,YoungTableau,TableauList):= (original,rowNumbers, tableau, tableaux) -> (
    row:= 0;
    col:=0;
    element:=0;
    if(isLastIndex(tableau)) then 
    (
	--Case that the we need to find the only possible number 
        row = (tableau#index)#0;
	col = (tableau#index)#1;
	if(col==0) then (rowNumbers = multiSet(getRow(original,row)));
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
	if(col==0) then (rowNumbers = multiSet(getRow(original,row)));
	--change name of row basis
	
	while nextIndex(rowNumbers) != (-1) do (
	    element= getElement(rowNumbers);
            if(notInColumn(tableau,element)) then
            (
		
                tableauNuevo := youngTableau(tableau);
		addElement(tableauNuevo,element);
		rowNumbers2 := copyOfMultiSet(rowNumbers);
		setIndex(rowNumbers2,0);
		rowNumbers2#element = rowNumbers2#element-1;
                tableaux =   recursiveGeneralizedTableaux(original,rowNumbers2,tableauNuevo,tableaux);
            );
        );  
    );
    tableaux
)

-----
-- This method codes 
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
-- This method codes 
-----
multinomial = method(TypicalValue => ZZ)
multinomial(ZZ, Partition) := (n,p)->(
    r:= n!;
    l:= differentElementsInPartition(p);
    for i to #keys(l)-1 do r = r//(((keys(l))#i)!^(l#((keys(l))#i)));  
    r
  )

multinomial( List) := (c)->(
    r:= (sum c)!;
    for i to #c-1 do r = r/((c#i)!);  
    r
  )

    
-----
-- This method codes 
-----
factorial = method(TypicalValue => ZZ)
factorial(ZZ) := n->(if n ==0 then 1 else n*factorial(n-1)) 


-----
-- This method extends the permutations from a subset of (1,...n) to all the permutations of
-- (1,...n) by fixing all letters that are not in the subset 
-----
canonicalPermutation = method(TypicalValue => List)
canonicalPermutation(ZZ, List) := (n,per) -> (
    per2 := sort(per);
    j := 0;
    result := new MutableList;
    result#(n-1) = 0;
    for i from 0 to n-1 do (
        if(j < #per and i == per2#j) then 
        (
	    result#(i) = per#j;
            j = j+1;
        )
        else result#(i) = i;
    );
    result = toList result;
    result
)


-----
-- This method codes 
-----
permutationsFixColumn = method(TypicalValue =>List)
permutationsFixColumn(YoungTableau,ZZ):= (tableau,col) -> (
    column:= getColumn(tableau,col);
    perms:= permutations(column);
    n := sum(toList tableau#partition);
    permsFinal := new MutableList;
    
    for i to #perms-1 do(
        permsFinal#i = canonicalPermutation(n,perms#i);
    );
    permsFinal = toList permsFinal;
    permsFinal

)

permutationsFixColumn(YoungTableau,ZZ,ZZ):= (tableau,n,col) -> (
    column:= getColumn(tableau,col);
    perms:= permutations(column);
    permsFinal := new MutableList;
    
    for i to #perms-1 do(
        permsFinal#i = canonicalPermutation(n,perms#i);
    );
    permsFinal = toList permsFinal;
    permsFinal

)


-----
-- This method codes 
-----
permutationsFixRow = method(TypicalValue =>List)
permutationsFixRow(YoungTableau,ZZ):= (tableau, num) -> (
    row:= getRow(tableau,num);
    perms:= permutations(row);
    n := sum(toList tableau#partition);
    permsFinal := new MutableList;
    
    for i to #perms-1 do(
        
        permsFinal#i = canonicalPermutation(n,perms#i);
    );
    permsFinal = toList permsFinal;
    permsFinal

)


permutationsFixRow(YoungTableau,ZZ,ZZ):= (tableau,n, num) -> (
    row:= getRow(tableau,num);
    perms:= permutations(row);
    permsFinal := new MutableList;
    
    for i to #perms-1 do(
        
        permsFinal#i = canonicalPermutation(n,perms#i);
    );
    permsFinal = toList permsFinal;
    permsFinal

)

-----
-- Direct product 
-----
productPermutationsList = method(TypicalValue =>List)
productPermutationsList(List,List):= (L,M) ->(
   P:= new MutableList;
   ind:= 0;
   for i from 0 to #L-1 do(
      for j from 0 to #M-1 do(
         P#ind=(L#i)_(M#j);
         ind= ind+1;
      );
   );
    toList P
)

-----
-- This method codes 
-----
columnStabilizer=method(TypicalValue => List)
columnStabilizer(List):= (T) ->(
    col:=#T#0;
    P:=permutationsFixColumn(T,1);
    for i from 2 to col do(
	P=productPermutationsList(P,permutationsFixColumn(T,i));
	);
    P
)

columnStabilizer(YoungTableau):= (tableau) ->(
    col:=(tableau#partition)#0;
    P:=permutationsFixColumn(tableau,0);
    for i from 1 to col-1 do (
    	P=productPermutationsList(P,permutationsFixColumn(tableau,i));
    	);
    toList P
)


columnStabilizer(YoungTableau,ZZ):= (tableau,n) ->(
    col:=(tableau#partition)#0;
    P:=permutationsFixColumn(tableau,n,0);
    for i from 1 to col-1 do (
    	P=productPermutationsList(P,permutationsFixColumn(tableau,n,i));
    	);
    toList P
)

-----
-- This method codes 
-----
rowStabilizer=method(TypicalValue => List)
rowStabilizer(List):= (T) ->(
    rowss:=#T;
    P:=permutationsFixRow(T.1);
    for i from 2 to rowss do(
	P=productPermutationsList(P,permutationsFixRow(T,i))
	);
    P
)

rowStabilizer(YoungTableau):= (tableau) ->(
    rowss:=#(tableau#partition);
    P:=permutationsFixRow(tableau,0);
    for i from 1 to rowss-1 do(
        P=productPermutationsList(P,permutationsFixRow(tableau,i));
    );
toList P
)

rowStabilizer(YoungTableau,ZZ):= (tableau,n) ->(
    rowss:=#(tableau#partition);
    P:=permutationsFixRow(tableau,n,0);
    for i from 1 to rowss-1 do(
        P=productPermutationsList(P,permutationsFixRow(tableau,n,i));
    );
toList P
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


signPermutation =method(TypicalValue=>ZZ)
signPermutation Partition := partis -> (
    sign:=1;
    for i to #partis-1 when partis#i >1 do(
        sign = sign*(-1)^(partis#i-1);
    );
    sign
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
    saved:= new MutableHashTable;
    saved#matrix = mutableMatrix(ZZ,n!//(m!*(n-m)!),n);
    saved#size = 0;
    intermediateCombination := new MutableList from 0..n-1;
    combinationsRecursive(saved,intermediateCombination,0,m);
    return matrix(saved#matrix);	
)    



----
-- The methos is recursive
----

---
--Apperantly there is no need for a list of numbers
---

combinationsRecursive = method()
combinationsRecursive(MutableHashTable, MutableList,ZZ,ZZ) := (saved,intermediate, i,m)->(
    
    if(i>=m) then(
	
	row:=saved#size;
	k := 0;
	l := m;
	for j from 0 to #intermediate-1 do(
	    if(k>=m or intermediate#k>j) then (
	    	saved#matrix_(row,l)= j;
	    	l= l+1;
	    	)
	    else (
		saved#matrix_(row,k)=intermediate#k;
		k=k+1;
		);
	    );
    	saved#size = row+1;
	)
    else(
	--when #intermediate+k-m
	ini:= 0;
	if(i == 0) then ini=0 else ini=intermediate#(i-1)+1; 
      	for k from ini to #intermediate+i-m  do(
	    intermediate#(i) = k;	
	    combinationsRecursive(saved,intermediate,i+1,m);
	    );
	);
    )

----
--Change the algorithms that make the list of tableaux according to this findings.
----

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
garnirElement(YoungTableau,ZZ):= (tableau,coef) -> (
    (a,b):= firstRowDescent(tableau);
    ans:={(tableau,coef)};
    if ((a,b) < (tableau#partition#0,0)) then ( 
    	conju:= conjugate(tableau#partition);
    	combs:= combinations(conju#a+1,b+1);
    	--print(a,b);
	A:= getColumn(tableau,a+1);
    	B:= getColumn(tableau,a);
	AB:= new MutableList from (#B+1):0;
     	newTableaux:= new MutableList from (numRows(combs)-1):0;
	--print (newTableaux, combs);
    	for i to b do (
	    AB#(i)=A#i;
	    );
	
	for i from b+1 to #B do (
	    AB#(i)= B#(i-1);
	    );
       	--print(AB);
	for i from 1 to numRows combs -1 do(
	    newTableau:= youngTableau(tableau#partition,flatten tableauToList tableau);
	   -- print("OK");
	    combination:= flatten entries combs^{i};
	   -- print(combination);
	    for j to b do(
		setElement(newTableau,j,a+1,AB#(combination#j));
	    	);
	    for j from b+1 to conju#a do (  
	    	setElement(newTableau,j-1,a,AB#(combination#j));
		);
	    sign:=orderColumnsTableau(newTableau);
	    newTableaux#(i-1) = (newTableau,-coef*sign*signPermutation(cycleStructure(combination)));
      	    );
	
	ans = toList newTableaux;
    	);
    
    -- TODO Find out how to use sort from Macaulay2
    --print(ans);
    (ans,coef)= bubbleSort(ans,columnDominance);
    ans
    )


columnDominance = method()
columnDominance(YoungTableau,YoungTableau):= (tableau1,tableau2)-> (
    
    ans:= 0;
    if(firstRowDescent tableau1 < firstRowDescent tableau2) then (
	
	ans=-1;
	)
    else if ( firstRowDescent tableau1 > firstRowDescent tableau2) then (
	
	ans = 1;
	
	)
    else (
	
	ans = lexicographicalOrder(tableau1,tableau2)
	
	);
    
    ans
    
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

firstRowDescent= method()
firstRowDescent YoungTableau := tableau -> (
    
    parti := conjugate(tableau#partition);
    fin:= false;
    (a,b):= (#parti,0);
    for i from 1 to #parti-1 when not fin do(
	for j to parti#i -1 when not fin do(
	    if (getElement(tableau,j,i-1) > getElement(tableau,j,i)) then (
		    fin = true;
		    (a,b)=(i-1,j);
		);
	    );
	);
    (a,b)
    )

lexicographicalOrder = method()
lexicographicalOrder(YoungTableau, YoungTableau):=(tableau1,tableau2) ->(
    
    ans:= 0;
    if(toList tableau1#partition != toList tableau2#partition) then
    	error "The tableaus don't have the same partition";
    for i to #(tableau1#partition)-1 when ( ans == 0) do (
    
    	for j to tableau1#partition#i-1 when (ans == 0) do (
	    
	    if( getElement(tableau1,i,j) < getElement(tableau2,i,j)) then
	    	(ans=-1)
	    else if (getElement(tableau1,i,j) > getElement(tableau2,i,j)) then
	    	(ans = 1); 
		
	    );
	    	
    	);
	
    ans
    
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
    

orderColumnsTableau = method()
orderColumnsTableau(YoungTableau):= tableau -> (
    
    sign:= 1;
    for i to tableau#partition#0-1 do(
	column:=getColumn(tableau,i);
	(lista,signColumn):=bubbleSort(column); 
	
	for j to #column-1 do(
	    
	    setElement(tableau,j,i,lista#j);
	    );
	
	sign = sign*signColumn;
	);
    sign
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
