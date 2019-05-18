load-- -*- coding: utf-8 -*-
newPackage(
        "SymmetricCharacterTable",
        Version => "1.5", 
        Date => "May 17, 2017",
        Authors => {{Name => "Jonathan Niño", 
                  Email => "ja.nino937@uniandes.edu.co", 
                  HomePage => "http://www.uniandes.edu.co"}
                  },
        Headline => "Calculating the character table for S_n.",
	PackageExports => {"SpechtModule"},
        DebuggingMode => true
        )
		
export {"CharacterTable"}
export {"characterTable"}
export {"getEntry"}
export {"binarySearch"}


--***************************
-- CharacterTable
--***************************

CharacterTable = new Type of MutableHashTable

--------------------
-- Constructors
--------------------
characterTable = method(TypicalValue => CharacterTable)
characterTable ZZ := n -> (
    
    charTables := new MutableHashTable;
    
    
    
    
    for i from 1 to n do (
	
	 
	charTable := new CharacterTable;
    	charTable#index = partitions i;
    	charTable#length = #(charTable#index);
    	charTable#degree = i;
    	charTable#values = mutableMatrix(ZZ,charTable#length,charTable#length);
    	charTables#i = charTable;
	--print("ok");
	y:= partitions(i);
	for j  to #y-1 do (
	    
	    for k from j to #y-1 do (
		val:= calculateNumberOfEquals(y#(j),y#(k),charTables);
		--print("ok");
		changeEntry(j,k,val,charTables#i);
	    );
	);
        --print("Table",i);
    	--print((charTables#i)#values);	
    ); 
    reduceCharacterTable(charTables#n)
)

--------------------
-- Methods
--------------------


-- Calculates the index of partition p in the list partitions.
-- It uses the binary search methods.
-- The list of partitions must be indexed in lexicographical order
binarySearch = method()
binarySearch(Partition,List) := (p,partitions)->(
    
    a := 0;
    b := #partitions;  
    c := (b+a)//2;
    while not toList partitions#c == toList p do (
	if(toList partitions#c> toList p) then(
	    a = c;	
	    )
	else(
	    b = c;	
	    );
    	c = (b+a)//2;
	);
    	c
    )
    

getEntry = method (TypicalValue => ZZ)
getEntry(ZZ,ZZ,CharacterTable):=(a,b,charTable)-> (
    charTable#values_(a,b)
    )

getEntry(Partition,Partition,CharacterTable):= (a,b,charTable)->(
    
    if(sum(toList a) != charTable#degree or sum(toList b)!= charTable#degree) then error ("Partition dimensions do not match ",a," ",b," ",charTable#number);
    a=binarySearch(a,charTable#index);
    b=binarySearch(b,charTable#index);
    (charTable#values)_(a,b)
    )
getEntry(ZZ,Partition,CharacterTable):= (a,b,charTable)->(
    if(sum(toList b)!= charTable#degree) then error ("Partition dimensions do not match ",b, " " ,charTable#number);
    b=binarySearch(b,charTable#index);
    (charTable#values)_(a,b)
    )
getEntry(Partition,ZZ,CharacterTable):= (a,b,charTable)->(
    if(sum(toList a) != charTable#degree) then error ("Partition dimensions do not match ",a, " ", charTable#number);
    a=binarySearch(a,charTable#index);
    (charTable#values)_(a,b)
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
       
changeEntry = method()
changeEntry(ZZ,ZZ,ZZ,CharacterTable):= ( a,b,val,charTable)->(
    (charTable#values)_(a,b)=val;
    )
changeEntry(Partition,Partition,ZZ,CharacterTable):= (a,b,val,charTable)->(
    if(sum(toList a) != charTable#degree or sum(toList b)!= charTable#degree) then error ("Partition dimensions do not match",a," ",b," ",charTable#number);
    a=binarySearch(a,charTable#index);
    b=binarySearch(b,charTable#index);
    (charTable#values)_(a,b)=val;
    )
changeEntry(ZZ,Partition,ZZ,CharacterTable):= ( a,b,val,charTable)->(
    if( sum(toList b)!= charTable#degree) then error ("Partition dimensions do not match",b," ",charTable#number);
    b=binarySearch(b,charTable#index);
    (charTable#values)_(a,b) = val;
    )
changeEntry(Partition,ZZ,ZZ,CharacterTable):= ( a,b,val,charTable)->(
    if(sum(toList a) != charTable#degree) then error ("Partition dimensions do not match",a," ", charTable#number);
    a=binarySearch(a,charTable#index);
    (charTable#values)_(a,b)=val;
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



- This method applies Gram-Schmidt to the table of permutation characters.
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
		val:= getEntry(i,k,charTable)-c*getEntry(j,k,charTable);
                changeEntry(i,k,val,charTable);
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
		    z = z+getEntry(newPartition,partition2,charTables#(sum(toList newPartition)));
		    --print("ok");
		    --print(z);
		);
		
	    );
	    
	);    
    ) else error "Partition dimensions do not match";
    z
)

--******************************************--
-- DOCUMENTATION     	       	    	    -- 
--******************************************--

beginDocumentation()

doc ///
  Key
    SymmetricCharacterTable
  Headline
    a package that calculates the character table of the symmetric group.
  Description
    
    Text
    	{\bf SymmetricCharacterTable} is a package that is used to calculate the character tables of the symmetric group. 
	The algorithm we proposed is alternative to the now standard {\em Murnaghan-Nakayama rule}. This is one of the packages used by
	SymmetricInvariantTheory.m2.
	
	
	This implementation is based in the construction of Specht Module as explained in [Sagan]. Let $\lambda$ be a partition of n. In this work it is shown that 
	the permutation modules $M^\lambda$ have a single copy of the Specht module $S^\lambda$. Let $\phi^\lambda$ denote the character of $M^\lambda$. This means that
	the irreducible characters can be obtained from $\phi^\lambda$ using the inner product for characters. The values of the $\phi^\lambda$ can be
	calculated using a recursive formula.
	 
	Since the entries in the character table of $S_n$ are indexed by partitions of the integer $n$, the package has an object CharacterTable where the
	entries are indexed by partitions.
	
	As an example we show the character table for $S_5$.
    
    Example
    	peek characterTable 5	
   ///;
   
--###################################
-- Types
--###################################

doc ///
  
  Key
    CharacterTable
  Headline
    the class of character tables
  Description
    
    Text
        This type represents the character table of a symmetric group. Its implemented as a
    	hash table which stores the list of partitions, the size of the table and a
    	matrix which stores the values of the table.
  
  SeeAlso
    	characterTable
 ///
 
 
 doc ///
  Key
    characterTable
    (characterTable,ZZ)
  Headline
   returns the character table of $S_n$
  Usage
      characterTable n
  Inputs
      n:ZZ
         the degree of the symmmetric group
  Outputs
      :CharacterTable
         the character table with the irreducible characters of S_n indexed by partitions
  Description
    Text
	This method construct the irreducible characters of $S_n$. The method works by recursively calculating the
	character tables for the permutation modules of $S_n$. Then applying Gram-Schimdt algorithm to this
	characters using the inner product of characters we obtain the irreducible characters of $S_n$ 
  
  SeeAlso
    	CharacterTable
 ///
       
   doc ///
  Key
    binarySearch
    (binarySearch,Partition,List)
  Headline
   method used to find the appropriate index of an entry in the character table 
  Usage
      binarySearch(p,partitions) 
  Inputs
      partitions:List
      	the list of partitions of n
      p:Partition
      	 the partition which index is being search.
  Outputs
      :ZZ
      	 the index of p in the list of partitions.
  Description
    
    Text
        This method is used to efficiently navigate the character table of $S_n$. Since the entries in this table are indexed by partitions, the method takes a partition an performs binary
	search on the list of partitions to return the appropriate position of this partition in the list. This method can be used since partitions are ordered in lexicographical order. 
    Example
    	partitions 5
    	binarySearch (new Partition from {3,2} , partitions 5)
  SeeAlso
      getEntry

 ///
    
 
   doc ///
  Key
    getEntry
    (getEntry,Partition,Partition,CharacterTable)
    (getEntry,Partition,ZZ,CharacterTable)
    (getEntry,ZZ,Partition,CharacterTable)
    (getEntry,ZZ,ZZ,CharacterTable)
  Headline
   method that returns an entry of the character table
  Usage
      getEntry(a,b,CharacterTable) 
  Inputs
      partitions:List
      	the list of partitions of n
       a:ZZ or Partition
      	 the row index which can be either a number or a partition
       b:ZZ or Partition
      	 the column index which can be either a number or a partition
       charTable:CharacterTable
      	 the character table in which the search is being conducted
       
  Outputs
      :ZZ
      	 the value in the cell (a,b) of charTable.
  Description
    
    Text
        This method gives the entry of a cell which is index either by a number or a partition
    Example
    	charTable = irreducibleCharacters 5
	a = new Partition from {3,1,1};b = new Partition from {1,1,1,1,1}
	peek charTable
	getEntry(a,b,charTable)
  SeeAlso
      getEntry

 ///
    
    
 end
 
 
    