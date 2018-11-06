
InstallMethod( StructureBeilinsonQuiverAlgebraOp,
		"for gap or homalg field and an integer n",
		[ IsField, IsInt ],
	function( field, n )
	local i,j,u,v,arrows,kQ,A,Q,s, chains_vector_bundles_quiver_reps, vector_bundles_quiver_reps, 
	homotopy_chains_vector_bundles_quiver_reps, S, graded_lp_cat_sym, chains_graded_lp_cat_sym, 
	homotopy_chains_graded_lp_cat_sym;

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

	A := QuotientOfPathAlgebra( kQ, v );


	vector_bundles_quiver_reps := CategoryOfQuiverRepresentations( A: FinalizeCategory := false );

	SetIsAbelianCategoryWithEnoughProjectives( vector_bundles_quiver_reps, true );

	AddEpimorphismFromSomeProjectiveObject( vector_bundles_quiver_reps, ProjectiveCover );

	AddIsProjective( vector_bundles_quiver_reps, function( R )
                        return IsIsomorphism( ProjectiveCover( R ) ) ;
                      end );

	AddLift( vector_bundles_quiver_reps, COMPUTE_LIFT_IN_QUIVER_REPS );

	AddColift( vector_bundles_quiver_reps, COMPUTE_COLIFT_IN_QUIVER_REPS );

	AddGeneratorsOfExternalHom( vector_bundles_quiver_reps, GENERATORS_OF_EXTERNAL_HOM_IN_QUIVER_REPS );

	Finalize( vector_bundles_quiver_reps );
	
	# ReadPackage( "ModelCategories", "examples/tools/Triangulated_Structure.g" );
	
	# Contructing the chains category and adding some basic opertions and the model structure to it.
	chains_vector_bundles_quiver_reps := ChainComplexCategory( vector_bundles_quiver_reps: FinalizeCategory := false );
	AddLift( chains_vector_bundles_quiver_reps, COMPUTE_LIFTS_IN_COMPLEXES_OF_QUIVER_REPS );
	AddColift( chains_vector_bundles_quiver_reps, COMPUTE_COLIFTS_IN_COMPLEXES_OF_QUIVER_REPS );
	AddGeneratorsOfExternalHom( chains_vector_bundles_quiver_reps, GENERATORS_OF_EXTERNAL_HOM_IN_CHAINS_OF_QUIVER_REPS );
	ModelStructureOnChainComplexes( chains_vector_bundles_quiver_reps );
	AddAreLeftHomotopic( chains_vector_bundles_quiver_reps,
	    function( phi, psi )
	        return IsNullHomotopic( phi - psi );
	    end );
	Finalize( chains_vector_bundles_quiver_reps ); 

	homotopy_chains_vector_bundles_quiver_reps := HomotopyCategory( chains_vector_bundles_quiver_reps );
	AddTriangulatedStructure( homotopy_chains_vector_bundles_quiver_reps );
	Finalize( homotopy_chains_vector_bundles_quiver_reps );

	# BindGlobal( "dimension_of_projective_space", n );
	# ReadPackage( "BBGG", "examples/glp_over_g_exterior_algebra/stable_cat_of_glp_over_exterior_algebra.g" );
	# SetUnderlyingHomalgGradedPolynomialRing( A, ValueGlobal("S") );
	
	S := UnderlyingHomalgGradedPolynomialRing( A );

	graded_lp_cat_sym := GradedLeftPresentations( S : FinalizeCategory := false );

	if not HasIsFinalized( graded_lp_cat_sym ) then 
	
	AddEvaluationMorphismWithGivenSource( graded_lp_cat_sym,
	    function( a, b, s )
	    local mor;
	    mor := EvaluationMorphismWithGivenSource( UnderlyingPresentationObject( a ), UnderlyingPresentationObject( b ), UnderlyingPresentationObject( s ) );
	    return GradedPresentationMorphism( s, UnderlyingMatrix( mor )*S, b );
	end );

	AddCoevaluationMorphismWithGivenRange( graded_lp_cat_sym,
	    function( a, b, r )
	    local mor;
	    mor := CoevaluationMorphismWithGivenRange( UnderlyingPresentationObject( a ), UnderlyingPresentationObject( b ), UnderlyingPresentationObject( r ) );
	    return GradedPresentationMorphism( a, UnderlyingMatrix( mor )*S, r );
	end );

	AddEpimorphismFromSomeProjectiveObject( graded_lp_cat_sym,
	    function( M )
	    local hM, U, current_degrees;
	    hM := AsPresentationInHomalg( M );
	    ByASmallerPresentation( hM );
	    U := UnderlyingModule( hM );
	    current_degrees := DegreesOfGenerators( hM );
	    return GradedPresentationMorphism(
	                GradedFreeLeftPresentation( Length( current_degrees), S, current_degrees ),
	                TransitionMatrix( U, PositionOfTheDefaultPresentation(U), 1 )*S,
	                M );
	end, -1 );

##
	AddIsProjective( graded_lp_cat_sym,
	    function( M )
	    local l;
	    l := Lift( IdentityMorphism( M ), EpimorphismFromSomeProjectiveObject( M ) );
	    if l = fail then
		return false;
	    else
		return true;
	    fi;
	end );

	AddGeneratorsOfExternalHom( graded_lp_cat_sym,
	   function( M, N )
	    local hM, hN, G;
	    hM := AsPresentationInHomalg( M );
	    hN := AsPresentationInHomalg( N );
	    G := GetGenerators( Hom( hM, hN ) );
	    return List( G, AsPresentationMorphismInCAP );
	end );
	Finalize( graded_lp_cat_sym );

	# constructing the chain complex category of graded left presentations over S
	chains_graded_lp_cat_sym := ChainComplexCategory( graded_lp_cat_sym : FinalizeCategory := false );
	ModelStructureOnChainComplexes( chains_graded_lp_cat_sym );
	AddAreLeftHomotopic( chains_graded_lp_cat_sym, 
    	function( phi, psi )
    	    return IsNullHomotopic( phi - psi );
        end );

	AddGeneratorsOfExternalHom( chains_graded_lp_cat_sym,
	GENERATORS_OF_EXTERNAL_HOM_IN_CHAINS_OF_GRADED_LEFT_PRESENTATIONS );
	Finalize( chains_graded_lp_cat_sym );

	homotopy_chains_graded_lp_cat_sym := HomotopyCategory( chains_graded_lp_cat_sym );
	AddTriangulatedStructure( homotopy_chains_graded_lp_cat_sym );
	Finalize( homotopy_chains_graded_lp_cat_sym );

	fi;
return A;
end );

InstallMethodWithCrispCache( HOMALG_GRADED_POLYNOMIAL_RING, 
	[ IsInt ], 
	function( n )
	local indterminates, S;
	indterminates := Concatenation( List( [ 0 .. n-1 ], i -> Concatenation( ",x", String( i ) ) ) );
	Remove( indterminates, 1 );
	S :=  GradedRing( HomalgFieldOfRationalsInSingular( )*indterminates );
	SetWeightsOfIndeterminates( S, List( [ 1 .. n ], i -> 1 ) );
	return S;
end );
	
InstallMethod( UnderlyingHomalgGradedPolynomialRing,
	[ IsQuiverAlgebra ],
	function( A )
	local n;
	n := NumberOfVertices( QuiverOfAlgebra( A ) );
	return HOMALG_GRADED_POLYNOMIAL_RING( n );
end );