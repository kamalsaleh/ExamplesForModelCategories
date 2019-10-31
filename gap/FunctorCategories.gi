

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


##
InstallMethod( BasisOfExternalHom,
    [ IsCapCategoryObjectInHomCategory, IsCapCategoryObjectInHomCategory ],
  function( S, R )
    local cat, matrix_cat, field, S_as_functor, R_as_functor, algebroid, algebra, quiver, S_dimensions, R_dimensions, nr_of_vertices, mat, nr_of_arrows, source_of_arrow, range_of_arrow, S_i, R_i, id_1, id_2, nr_rows_of_block, u, v, nr_cols_in_block1, block_1, block_2, nr_cols_in_block3, block_3, block_4, nr_cols_in_block5, block_5, block, cols_of_mat, hom, morphism, L, i;
  
    cat := CapCategory( S );
    
    matrix_cat := Range( cat );
    
    if not HasCommutativeRingOfLinearCategory( matrix_cat ) then
      
      Error( "The category must be linear\n" );
      
    fi;
    
    field := CommutativeRingOfLinearCategory( matrix_cat );
    
    if not IsFieldForHomalg( field ) then
      
      Error( "The commutative ring of the linear category must be a homalg field\n" );
      
    fi;
    
    #Vec := function( matrix )
    #        return HomalgMatrix(
    #          EntriesOfHomalgMatrix(
    #            TransposedMatrix( matrix ) ), NrRows( matrix )* NrCols( matrix ), 1, field );
    #end;
    
    S_as_functor := UnderlyingCapTwoCategoryCell( S );
    
    R_as_functor := UnderlyingCapTwoCategoryCell( R );
    
    algebroid := AsCapCategory( Source( S_as_functor ) );
    
    algebra := UnderlyingQuiverAlgebra( algebroid );
    
    quiver := UnderlyingQuiver( algebroid );
    
    
    S_dimensions := List( Vertices( quiver ),
                      v -> Dimension(
                        ApplyFunctor( S_as_functor, algebroid.( String( v ) ) )
                                    )
                        );
    
    R_dimensions := List( Vertices( quiver ),
                      v -> Dimension(
                        ApplyFunctor( R_as_functor, algebroid.( String( v ) ) )
                                    )
                        );
    
    nr_of_vertices := NumberOfVertices( quiver );
    
    mat := HomalgZeroMatrix( 0, S_dimensions * R_dimensions, field );
    
    nr_of_arrows := NumberOfArrows( quiver );
    
    for i in [ 1 .. nr_of_arrows ] do
      source_of_arrow := VertexIndex( Source( Arrow( quiver, i ) ) );
      range_of_arrow := VertexIndex( Target( Arrow( quiver, i ) ) );
      
      S_i := ApplyFunctor( S_as_functor, algebroid.( String( Arrow( quiver, i ) ) ) );
      S_i := UnderlyingMatrix( S_i );
      
      R_i := ApplyFunctor( R_as_functor, algebroid.( String( Arrow( quiver, i ) ) ) );
      R_i := UnderlyingMatrix( R_i );
      
      
      id_1 := HomalgIdentityMatrix( NrRows( S_i ), field );
      id_2 := HomalgIdentityMatrix( NrCols( R_i ), field );
      
      nr_rows_of_block := NrRows( S_i ) * NrCols( R_i );
      
      u := Minimum( source_of_arrow, range_of_arrow );
      
      v := Maximum( source_of_arrow, range_of_arrow );
      
      if u = 1 then
        
        nr_cols_in_block1 := 0;
        
      else
        
        nr_cols_in_block1 := S_dimensions{ [ 1 .. u - 1 ] } * R_dimensions{ [ 1 .. u - 1 ] };
        
      fi;
      
      block_1 := HomalgZeroMatrix( nr_rows_of_block,  nr_cols_in_block1, field );
      
      if u = source_of_arrow then
        
        block_2 := - KroneckerMat( TransposedMatrix( R_i ), id_1 );
        
      elif u = range_of_arrow then
      
        block_2 := KroneckerMat( id_2, S_i );
        
      fi;

      if v - u in [ 0, 1 ] then
        
        nr_cols_in_block3 := 0;
        
      else
        
        nr_cols_in_block3 := S_dimensions{ [ u + 1 .. v - 1 ] } * R_dimensions{ [ u + 1 .. v - 1 ] };
        
      fi;

      block_3 := HomalgZeroMatrix( nr_rows_of_block,  nr_cols_in_block3, field );

      if v = source_of_arrow then
        
        block_4 := - KroneckerMat( TransposedMatrix( R_i ), id_1 );
        
      elif v = range_of_arrow then
      
        block_4 := KroneckerMat( id_2, S_i );
        
      fi;

      if v = nr_of_vertices then
        
        nr_cols_in_block5 := 0;
        
      else
        
        nr_cols_in_block5 := S_dimensions{ [ v + 1 .. nr_of_vertices ] }
                              * R_dimensions{ [ v + 1 .. nr_of_vertices ] };
        
      fi;
      
      block_5 := HomalgZeroMatrix( nr_rows_of_block,  nr_cols_in_block5, field );
      
      block := UnionOfColumns( [ block_1, block_2, block_3, block_4, block_5 ] );
      
      mat := UnionOfRows( mat, block );
      
    od;
    
    Print( "I am going to compute columns syzygies of a ", NrRows( mat ), " X ", NrCols( mat ), " homalg matrix ...\n"  );
    mat := SyzygiesOfColumns( mat );
    Print( "Syzygies has been computed!\n" );
    
    if mat = fail then
      
      return [ ];
      
    fi;
    
    cols_of_mat := TransposedMat( EntriesOfHomalgMatrixAsListList( mat ) );
    
    hom := [ ];
    
    for L in cols_of_mat do
    
    morphism:= rec( );
      
      for i in [ 1 .. nr_of_vertices ] do
        
        if S_dimensions[ i ] * R_dimensions[ i ] = 0 then
          
          morphism!.( String( Vertex( quiver, i ) ) ) :=
            ZeroMorphism(
                          VectorSpaceObject( S_dimensions[ i ], field ),
                          VectorSpaceObject( R_dimensions[ i ], field )
                        );
        
        else
          
          mat := L{ [ 1 .. S_dimensions[ i ] * R_dimensions[ i ] ] };
       
          mat := TransposedMat( List( [ 1 .. R_dimensions[ i ] ],
              u -> mat{ [ ( u - 1 ) * S_dimensions[ i ] + 1 .. u * S_dimensions[ i ] ] } ) );
        
          mat := HomalgMatrix( mat, S_dimensions[ i ], R_dimensions[ i ], field );
        
          morphism!.( String( Vertex( quiver, i ) ) ) :=
            VectorSpaceMorphism(
                              VectorSpaceObject( S_dimensions[ i ], field ),
                              mat,
                              VectorSpaceObject( R_dimensions[ i ], field )
                             );
        
        fi;
        
        L := L{ [ S_dimensions[ i ] * R_dimensions[ i ] + 1 .. Length( L ) ] };
      
      od;
      
      Add( hom, AsMorphismInHomCategory( S, morphism, R ) );
    
    od;
    
    return hom;
    
end );

