
InstallMethod( CotangentBeilinsonQuiverAlgebraOp,
		"for gap or homalg field and an integer n",
		[ IsField, IsInt ],
	function( field, n )
    local s, u, variable_string, Q, arrows, kQ, v, A, vector_bundles_quiver_reps, chains_vector_bundles_quiver_reps, FinalizeCategory, homotopy_chains_vector_bundles_quiver_reps, S, i, j;
    
    s := "";
    for i in [ 0 .. n ] do
      
      if i <> n then
        
        s := Concatenation(s, "Ω^", String(i), "(", String(i), ") <--",String( n + 1 ),"-- " );
        
      else
        
        s := Concatenation( s, "Ω^", String(i), "(", String(i), ")" );
        
      fi;
    
    od;
    
    Print( s, "\n" );
    
    u := "";
    
    variable_string := ValueOption( "VariableString" );
    
    if variable_string = fail then
    
      variable_string := "y";
    
    fi;
    
    for i in [ 1 .. n ] do
      
      for j in [ 0 .. n ] do
        
        u := Concatenation( u,variable_string,String(i),String(j),":",String(i),"->",String(i+1),"," );
        
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
      
        Add( v, kQ.(Concatenation( variable_string, String(i),String(j[1])) )* kQ.(Concatenation( variable_string, String(i+1),String(j[2]) ) )+
        
          kQ.(Concatenation( variable_string,String(i),String(j[2]) ) )* kQ.(Concatenation( variable_string, String(i+1),String(j[1]) ) ) );
        
      od;
    od;
    
    for i in [ 1 .. n-1 ] do
      
      for j in [ 0 .. n ] do
        
        Add( v, kQ.(Concatenation( variable_string, String(i),String(j)) )* kQ.(Concatenation( variable_string, String(i+1),String(j) ) ) );
        
      od;
      
    od;
    
    A := QuotientOfPathAlgebra( kQ, v );
    
    #vector_bundles_quiver_reps := CategoryOfQuiverRepresentations( A );
    
    # ReadPackage( "ModelCategories", "examples/tools/Triangulated_Structure.g" );
    
    # Contructing the chains category and adding some basic opertions and the model structure to it.
   # chains_vector_bundles_quiver_reps := ChainComplexCategory( vector_bundles_quiver_reps: FinalizeCategory := false );
   # 
   # AddLift( chains_vector_bundles_quiver_reps, COMPUTE_LIFTS_IN_COMPLEXES_OF_QUIVER_REPS );
   # 
   # AddColift( chains_vector_bundles_quiver_reps, COMPUTE_COLIFTS_IN_COMPLEXES_OF_QUIVER_REPS );
   # 
   # AddGeneratorsOfExternalHom( chains_vector_bundles_quiver_reps, BASIS_OF_EXTERNAL_HOM_IN_CHAINS_OF_QUIVER_REPS );
   # 
   # ModelStructureOnChainComplexes( chains_vector_bundles_quiver_reps );
   # 
   # AddAreLeftHomotopic( chains_vector_bundles_quiver_reps,
   #     function( phi, psi )
   #         return IsNullHomotopic( phi - psi );
   #     end );
   # 
   # Finalize( chains_vector_bundles_quiver_reps ); 
   # 
   # homotopy_chains_vector_bundles_quiver_reps := HomotopyCategory( chains_vector_bundles_quiver_reps );
   # 
   # AddTriangulatedStructure( homotopy_chains_vector_bundles_quiver_reps );
   # 
   # Finalize( homotopy_chains_vector_bundles_quiver_reps );
   # 
   S := UnderlyingHomalgGradedPolynomialRing( A );
   # 
   PREPARE_CATEGORIES_OF_HOMALG_GRADED_POLYNOMIAL_RING( S );
   # #LIST_OF_MORPHISMS_BETWEEN_TWISTED_COTANGENT_BUNDLES( S );
    
    return A;
    
end );


InstallMethod( LIST_OF_MORPHISMS_BETWEEN_TWISTED_COTANGENT_BUNDLES_AS_QUIVER_REPS, [ IsQuiverAlgebra ],
function( A )
local indec_projectives, n, morphisms, j, k, l, current;
indec_projectives := ShallowCopy( IndecProjRepresentations( A ) );
Sort( indec_projectives, function(u,v) return DimensionVector(u)<DimensionVector(v); end );

n := Length( indec_projectives );
morphisms := List( [ 1 .. n-1 ], i -> BasisOfExternalHom( indec_projectives[i], indec_projectives[i+1] ) );

for j in [ 2 .. n-1] do
    current := [ ];
    for k in [ 1 .. n ] do
    for l in [ 1 .. n ] do
        if IsZeroForMorphisms( PreCompose( morphisms[j-1][k], morphisms[j][l] ) ) then
            current[k] := morphisms[j][l];
        fi;
    od;
    od;
    morphisms[ j ] := current;
od;

for j in [ 2 .. n-1] do
    for k in [ 1 .. n ] do
    for l in [ 1 .. n ] do
        if k <> l and IsEqualForMorphisms( PreCompose( morphisms[j-1][k], morphisms[j][l] ),
             PreCompose( morphisms[j-1][l], morphisms[j][k] ) ) then
            morphisms[ j ][ l ] := -morphisms[ j ][ l ];
        elif k <> l and not IsEqualForMorphisms( PreCompose( morphisms[j-1][k], morphisms[j][l] ),
             -PreCompose( morphisms[j-1][l], morphisms[j][k] ) ) then
            Print( "unexpected!");
        fi;
    od;
    od;
od;

return morphisms;
end );

