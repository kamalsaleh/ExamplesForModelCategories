

DeclareAttribute( "EquivalenceFromCategoryOfQuiverRepresentationsToCategoryOfFunctors", IsQuiverAlgebra );

DeclareAttribute( "EquivalenceFromCategoryOfFunctorsToCategoryOfQuiverRepresentations", IsQuiverAlgebra );


##
BindGlobal( "SET_EQUIVALENCE_FUNCTORS_BETWEEN_QUIVER_REPS_AND_FUNCTORS",

  function( A )
    local quiver, homalg_field, P, rel, B, quivers_cat, matrix_cat, functors_cat, F, G; 
    
    quiver := QuiverOfAlgebra( A );
    
    homalg_field := EXAMPLES_FOR_MODEL_CATEGORIES!.QQ;
    
    P := PathAlgebra( homalg_field, quiver );
    
    rel := RelationsOfAlgebra( A );
    
    rel := List( rel, r -> Coefficients(r)*List( Paths(r), p -> Product( List( ArrowList(p), arrow -> P.(String( arrow ) ) ) ) ) );
    
    B := Algebroid( P, rel );
    
    quivers_cat := CategoryOfQuiverRepresentations( A );
    
    matrix_cat := MatrixCategory( homalg_field );
    
    functors_cat := Hom( B, matrix_cat );
    
    F := CapFunctor( "Equivalence functor: representations cat -> functors cat", quivers_cat, functors_cat );
    
    AddObjectFunction( F,
      function( rep )
        local obj,  dimension_vec, mor, matrices, i;
        
        obj := rec( );
        
        dimension_vec := DimensionVector( rep );

        for i in [ 1 .. Length( dimension_vec ) ] do
          
          obj!.( String( Vertex( quiver, i ) ) ) := VectorSpaceObject( dimension_vec[ i ], homalg_field );
        
        od;

        mor := rec( );
        
        matrices := MatricesOfRepresentation( rep );
        
        matrices := List( matrices, mat ->
        
        HomalgMatrix( RowsOfMatrix( mat ), DimensionsMat( mat )[1], DimensionsMat( mat )[2], homalg_field ) );

        for i in [ 1 .. Length( matrices ) ] do;
        
          mor!.( String( Arrow( quiver, i ) ) ) :=
          
            VectorSpaceMorphism(
            
                obj!.( String( Source( Arrow( quiver, i ) ) )  ),
                
                matrices[i],
                
                obj!.( String( Target( Arrow( quiver, i ) ) )  ) );
        
        od;

        return AsObjectInHomCategory( B, obj, mor );
    
    end );

    AddMorphismFunction( F,
      function( source, rep_mor, range )
        local matrices, mor, i;
        
        matrices := MatricesOfRepresentationHomomorphism( rep_mor );
        
        matrices := List( matrices, mat ->
        
          HomalgMatrix( RowsOfMatrix( mat ), DimensionsMat( mat )[1], DimensionsMat( mat )[2], homalg_field ) );

        mor := rec( );
        
        for i in [ 1 .. Length( matrices ) ] do
          
          mor!.( String( Vertex( quiver, i ) ) ) :=
          
            VectorSpaceMorphism(
            
              VectorSpaceObject( NrRows( matrices[ i ] ), homalg_field ),
              
              matrices[ i ],
              
              VectorSpaceObject( NrColumns( matrices[ i ] ), homalg_field )
            
            );
        
        od;
        
        return AsMorphismInHomCategory( source, mor, range );
        
    end );

    G := CapFunctor( "Equivalence functor: functors cat --> representations cat", functors_cat, quivers_cat );
    
    AddObjectFunction( G,
      function( func )
        local U, V, L;
        
        U := UnderlyingCapTwoCategoryCell( func );
        
        V := List( Vertices( quiver ),
          v -> Dimension( ApplyFunctor( U, B.( String( v ) ) ) ) );
        
        L := List( Arrows( quiver ), l -> UnderlyingMatrix(
                    ApplyFunctor( U, B.( String( l ) ) ) ) );

        L := List( L, l -> MatrixByRows( Rationals, [ NrRows( l ), NrColumns( l ) ],
              EntriesOfHomalgMatrixAsListList( l ) ) );
        
        return QuiverRepresentation( A, V, L );
        
      end );
    
    AddMorphismFunction( G,
      function( source, mor, range )
        local U, V;
        
        U := UnderlyingCapTwoCategoryCell( mor );

        V := List( Vertices( quiver ), v -> UnderlyingMatrix(
                ApplyNaturalTransformation( U, B.( String( v ) ) ) ) );

        V := List( V, v -> MatrixByRows( Rationals, [ NrRows( v ), NrColumns( v ) ],
          EntriesOfHomalgMatrixAsListList( v ) ) );
        
        return QuiverRepresentationHomomorphism( source, range, V );
      
      end );
     
     SetEquivalenceFromCategoryOfQuiverRepresentationsToCategoryOfFunctors( A, F );
     SetEquivalenceFromCategoryOfFunctorsToCategoryOfQuiverRepresentations( A, G );
    
end );

##
InstallMethod( EquivalenceFromCategoryOfQuiverRepresentationsToCategoryOfFunctors,
  [ IsQuiverAlgebra ],
  function( A )
    
    SET_EQUIVALENCE_FUNCTORS_BETWEEN_QUIVER_REPS_AND_FUNCTORS( A );
    
    return EquivalenceFromCategoryOfQuiverRepresentationsToCategoryOfFunctors( A );
    
end );

##
InstallMethod( EquivalenceFromCategoryOfFunctorsToCategoryOfQuiverRepresentations,
  [ IsQuiverAlgebra ],
  function( A )
    
    SET_EQUIVALENCE_FUNCTORS_BETWEEN_QUIVER_REPS_AND_FUNCTORS( A );
    
    return EquivalenceFromCategoryOfFunctorsToCategoryOfQuiverRepresentations( A );
    
end );

