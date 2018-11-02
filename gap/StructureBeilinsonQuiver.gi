
InstallMethod( StructureBeilinsonQuiverAlgebraOp,
		"for gap or homalg field and an integer n",
		[ IsField, IsInt ],
	function( field, n )
	local i,j,u,v,arrows,kQ,AQ,Q,s;

	s := "";
	for i in [ 1 .. n + 1 ] do
		if i <> n+1 then
			if i = 1 then 
		    	Print( s, "O(", "i", ") <--", String( n + 1 ), "-- " );
			else
		    	Print( s, "O(", "i-", String( i-1 ), ") <--", String( n + 1 ), "-- " );
			fi;
		else
		    Print( s, "O(", "i-", String( i-1 ), ")\n" );
		fi;
	od;

	u := "";
	
	# Defining the string that contains the arrows of the quiver 
	for i in [ 1 .. n ] do
		for j in [ 0 .. n ] do
			u := Concatenation( u,"x",String(i),String(j),":",String(i),"->",String(i+1),"," );
		od;
	od;

	Remove( u, Length( u ) );
	u := Concatenation( "Q(", String(n+1),")[",u,"]" );
	Q := RightQuiver( u );
	
	arrows := Arrows( Q );
	kQ := PathAlgebra( field, Q );
	
	v := [ ];
	for i in [ 1 .. n-1 ] do
		for j in Combinations( [ 0 .. n ], 2 ) do
			Add( v, kQ.(Concatenation( "x", String(i),String(j[1])) )* kQ.(Concatenation( "x", String(i+1),String(j[2]) ) )-
		        kQ.(Concatenation( "x",String(i),String(j[2]) ) )* kQ.(Concatenation( "x", String(i+1),String(j[1]) ) ) );
		od;
	od;

	return QuotientOfPathAlgebra( kQ, v );
end );

InstallMethod( UnderlyingHomalgGradedPolynomialRing, 
	[ IsQuiverAlgebra ], 
	function( A )
	local n, indterminates, S;

	n := NumberOfVertices( QuiverOfAlgebra( A ) );
	indterminates := Concatenation( List( [ 0 .. n-1 ], i -> Concatenation( ",x", String( i ) ) ) );
	Remove( indterminates, 1 );

	S :=  GradedRing( HomalgFieldOfRationalsInSingular( )*indterminates );
	SetWeightsOfIndeterminates( S, List( [ 1 .. n ], i -> 1 ) );
	
	return S;
end );