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
  
  
 ///
 
 
 doc ///
  
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
