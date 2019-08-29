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
		


--***************************
-- CharacterTable
--***************************


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
    (symbol _,CharacterTable, Sequence)
    (net,CharacterTable)
  Headline
    the class of character tables
  Description
    
    Text
        This type represents the character table of a symmetric group. Its implemented as a
    	hash table which stores the list of partitions, the size of the table and a
    	matrix which stores the values of the table.
  
     Example
    	charTable = characterTable 5
	a = new Partition from {3,1,1};b = new Partition from {1,1,1,1,1}
	peek charTable
	charTable_(a,b)
 
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
 
    
 
    
    
 end
 
 
   --------------------
-- Methods
--------------------

-- Deprecated
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
