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
