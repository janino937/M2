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
export {"irreducibleCharacters"}
export {"getIndexPartition"}
export {"getEntry"}
export {"binarySearch"}



------
-- CharacterTable
------

-- An object used to represent a character table 
-- The object comes equip with an index tree. This index gives an structure to the
-- partitions. This allows for an efficient way to access the entries of the character table
-- given partitions as indexes. This in turn is used in the algorithm that calculates the
-- character tables recursively. 

-- Index: The tree with has the indexes of the partitions.
-- Lenght: The number of rows (or columns) in the table
-- Number: The order of the symmetric group whos character table is being calculated.
-- Table: The matrix where the values of the character table are store.  

CharacterTable = new Type of MutableHashTable

-- Constructors

characterTable = method(TypicalValue => CharacterTable)
characterTable ZZ := n -> (
    
    charTable:= new CharacterTable;
    charTable#index = partitions n;
    charTable#length = #(charTable#index);
    charTable#number = n;
    charTable#table = mutableMatrix(ZZ,charTable#length,charTable#length);
    charTable
)

-- Returns the index of the partition in the list of all partitions

getIndexPartition = method()
getIndexPartition(CharacterTable, Partition):= (table,parti)-> (
    	binarySearch(table#index, parti)
    )


-- Returns the index of the partition in the list of all partitions

binarySearch = method()
binarySearch(List, Partition) := (partis,parti)->(
    
    a := 0;
    b := #partis;  
    c := (b+a)//2;
    while not toList partis#c == toList parti do (
	if(toList partis#c> toList parti) then(
	    a = c;	
	    )
	else(
	    b = c;	
	    );
    	c = (b+a)//2;
	);
    	c
    )
    

-- Methods

------
-- Method for obtaining an entry of a character table given the index of the row and column
-- or the partitions associated to each row or partition.
------
getEntry = method (TypicalValue => ZZ)
getEntry(CharacterTable,ZZ,ZZ):= (charTable, a,b)-> (
    charTable#table_(a,b)
    )

getEntry(CharacterTable,Partition,Partition):= (charTable, a,b)->(
    
    if(sum(toList a) != charTable#number or sum(toList b)!= charTable#number) then error ("Partition dimensions do not match ",a," ",b," ",charTable#number);
    a=binarySearch(charTable#index,a);
    b=binarySearch(charTable#index,b);
    (charTable#table)_(a,b)
    )
getEntry(CharacterTable,ZZ,Partition):= (charTable, a,b)->(
    if(sum(toList b)!= charTable#number) then error ("Partition dimensions do not match ",b, " " ,charTable#number);
    b=binarySearch(charTable#index,b);
    (charTable#table)_(a,b)
    )
getEntry(CharacterTable,Partition,ZZ):= (charTable, a,b)->(
    if(sum(toList a) != charTable#number) then error ("Partition dimensions do not match ",a, " ", charTable#number);
    a=binarySearch(charTable#index,a);
    (charTable#table)_(a,b)
    )

------
-- Changes an entry of the table given the index of the row and column
-- or the partitions associated to each row or partition.
------

changeEntry = method()
changeEntry(CharacterTable,ZZ,ZZ,ZZ):= (charTable, a,b,val)->(
    (charTable#table)_(a,b)=val;
    )
changeEntry(CharacterTable,Partition,Partition,ZZ):= (charTable, a,b,val)->(
    if(sum(toList a) != charTable#number or sum(toList b)!= charTable#number) then error ("Partition dimensions do not match",a," ",b," ",charTable#number);
    a=binarySearch(charTable#index,a);
    b=binarySearch(charTable#index,b);
    (charTable#table)_(a,b)=val;
    )
changeEntry(CharacterTable,ZZ,Partition,ZZ):= (charTable, a,b,val)->(
    if( sum(toList b)!= charTable#number) then error ("Partition dimensions do not match",b," ",charTable#number);
    b=binarySearch(charTable#index,b);
    (charTable#table)_(a,b) = val;
    )
changeEntry(CharacterTable,Partition,ZZ,ZZ):= (charTable, a,b,val)->(
    if(sum(toList a) != charTable#number) then error ("Partition dimensions do not match",a," ", charTable#number);
    a=binarySearch(charTable#index,a);
    (charTable#table)_(a,b)=val;
    )
	


	

-----
-- This method codes 
-----
innerProduct = method(TypicalValue => ZZ)
innerProduct(ZZ,MutableMatrix,MutableMatrix) := (n,C,X) -> (
    prod:=0;
    p:=partitions(n,n);
    for i to numColumns(C)-1 do(
        prod=prod+(C_(0,i))*(X_(0,i))*(cardinalityOfConjugacyClass(p#(i)));
    ); 
    prod//(n)!
)


-----
-- How does the index work
-----
irreducibleCharacters = method(TypicalValue => CharacterTable)
irreducibleCharacters(ZZ) := (n) -> (
    
    charTables := new MutableHashTable;
    
    for i from 1 to n do (
	
	charTables#i = characterTable(i);
        --print("ok");
	y:= partitions(i);
	for j  to #y-1 do (
	    
	    for k from j to #y-1 do (
		val:= calculateNumberOfEquals(charTables,y#(j),y#(k));
		--print("ok");
		changeEntry(charTables#i,j,k,val);
	    );
	);
        --print("Table",i);
    	--print((charTables#i)#table);	
    ); 
    reduceCharacterTable(charTables#n,n)
    --charTables#n
)

-----
-- This method codes 
-----
reduceCharacterTable = method(TypicalValue => CharacterTable)
reduceCharacterTable (CharacterTable,ZZ)  := (charTable,n) -> (
    for i to charTable#length-1 do(
    
        for j to  i-1 do(
            
            c := innerProduct(n,(charTable#table)^{i},(charTable#table)^{j});
            for k to charTable#length-1 do(
		val:= getEntry(charTable,i,k)-c*getEntry(charTable,j,k);
                changeEntry(charTable,i,k,val);
            );
     );
    	
    );
   
    charTable
    
)

-----
-- This method codes 
-----
calculateNumberOfEquals = method(TypicalValue => ZZ )
calculateNumberOfEquals(MutableHashTable,Partition, Partition):= (charTables,part1, part2)->(
    
    z:=0;
    if(sum(toList part1) == sum(toList part2)) then (
    	if #part1 == 1 then (z = 1;)
	else ( 
    	    border:= part2#0;
	    part2 = drop(part2,1);
	    for i to #part1-1 when part1#i>=border do(
	    	c:= new MutableList from part1;
		c#i = c#i-border;
		parti := new Partition from reverse sort toList c;
		if(parti#(-1) == 0)
		    then (parti = drop(parti,-1););
		if(#parti == 0)
		    then (z= z+ 1;)
		else(
		    
		    --print(parti);
		    --print(part2);
		    z = z+getEntry(charTables#(sum(toList parti)),parti,part2);
		    --print("ok");
		    --print(z);
		);
		
	    );
	    
	);    
    ) else error "Partition dimensions do not match";
    z
)