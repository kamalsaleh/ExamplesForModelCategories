
##
BindGlobal( "ADD_HOMOMORPHISM_STRUCTURE_TO_CATEGORY_OF_QUIVER_REPRESENTATIONS",
  function( cat )
    local field;
    
    field := FieldForHomomorphismStructure( cat );

    SetRangeCategoryOfHomomorphismStructure( cat, MatrixCategory( field ) );

    AddDistinguishedObjectOfHomomorphismStructure( cat,
       function( )
         
         return VectorSpaceObject( 1, field );
    
    end );
    
    ##
    AddHomomorphismStructureOnObjects( cat,
      function( a, b )
        local dimension;
        
        dimension := Length( BasisOfExternalHom( a, b ) );
        
        return VectorSpaceObject( dimension, field );
    
    end );
    
    #          alpha
    #      a --------> a'     s = H(a',b) ---??--> r = H(a,b')
    #      |           |
    # alpha.h.beta     h
    #      |           |
    #      v           v
    #      b' <------- b
    #          beta
    
    ##
    AddHomomorphismStructureOnMorphismsWithGivenObjects( cat,
      function( s, alpha, beta, r )
        local B, mat;
        
        B := BasisOfExternalHom( Range( alpha ), Source( beta ) );
        
        B := List( B, b -> PreCompose( [ alpha, b, beta ] ) );
        
        B := List( B, CoefficientsOfLinearMorphism );
        
        # Improve this
        if Dimension( s ) * Dimension( r ) = 0 then
          
          mat := HomalgZeroMatrix( Dimension( s ), Dimension( r ), field );
        
        else
          
          mat := HomalgMatrix( B, Dimension( s ), Dimension( r ), field );
        
        fi;
        
        return VectorSpaceMorphism( s, mat, r );
    
    end );
    
    ##
    AddDistinguishedObjectOfHomomorphismStructure( cat,
      function( )
        
        return VectorSpaceObject( 1, field );
    
    end );
    
    ##
    AddInterpretMorphismAsMorphismFromDinstinguishedObjectToHomomorphismStructure( cat,
      function( alpha )
        local coeff, D;
        
        coeff := CoefficientsOfLinearMorphism( alpha );
        
        coeff := HomalgMatrix( coeff, 1, Length( coeff ), field );
        
        D := VectorSpaceObject( 1, field );
        
        return VectorSpaceMorphism( D, coeff, VectorSpaceObject( NrCols( coeff ), field ) );
    
    end );
    
    AddInterpretMorphismFromDinstinguishedObjectToHomomorphismStructureAsMorphism( cat,
      function( a, b, iota )
        local mat, coeff, B, L;
        
        mat := UnderlyingMatrix( iota );
        
        coeff := EntriesOfHomalgMatrix( mat );
        
        B := BasisOfExternalHom( a, b );
        
        L := List( [ 1 .. Length( coeff ) ], i -> MultiplyWithElementInFieldForHomomorphismStructure( coeff[ i ], B[ i ] ) );
        
        if L = [  ] then
          
          return ZeroMorphism( a, b );
        
        else
          
          return Sum( L );
        
        fi;
    
    end );

end );

##
BindGlobal( "ADD_HOMOMORPHISM_STRUCTURE_TO_COMPLEX_CATEGORY_OF_QUIVER_REPRESENTATIONS",
  ADD_HOMOMORPHISM_STRUCTURE_TO_CATEGORY_OF_QUIVER_REPRESENTATIONS );

##
InstallMethod( CategoryOfQuiverRepresentations,
              [ IsQuiverAlgebra and IsRightQuiverAlgebra ],
              1000,
  function( A )
    local add_extra_methods, cat, FinalizeCategory, AddExtraMethods, to_be_finalized, domain;
    
    add_extra_methods := ValueOption( "AddExtraMethods" );
    
    if add_extra_methods = false then
      
      TryNextMethod( );
      
    fi;
    
    cat := CategoryOfQuiverRepresentations( A : FinalizeCategory := false, AddExtraMethods := false );
    
    domain := LeftActingDomain( A );
    
    if domain = Rationals then
      
      SetFieldForHomomorphismStructure( cat, HomalgFieldOfRationals( ) );
      
    elif IsFieldForHomalg( domain ) then
    
      SetFieldForHomomorphismStructure( cat, domain );
      
    else
      
      TryNextMethod( );
      
    fi;
    
    ADD_HOMOMORPHISM_STRUCTURE_TO_CATEGORY_OF_QUIVER_REPRESENTATIONS( cat );
    
    # Lift and Colift can be derived from the homomorphism structure, but the following is quicker
	  AddLift( cat, COMPUTE_LIFT_IN_QUIVER_REPS );

	  AddColift( cat, COMPUTE_COLIFT_IN_QUIVER_REPS );

    AddRandomObjectByList( cat,
    
      function( C, l )
        local indec_proj, s, r, source, range, L;
        
        indec_proj := IndecProjRepresentations( A );
        
        s := l[ 1 ];
        
        r := l[ 2 ];
        
        source := List( [ 1 .. s ], i -> Random( indec_proj ) );
        
        range := List( [ 1 .. r ], i -> Random( indec_proj ) );
        
        L := List( [ 1 .. s ],
          i -> List( [ 1 .. r ],
            j -> Random(
              Concatenation(
                BasisOfExternalHom( source[ i ], range[ j ] ),
                [ ZeroMorphism(source[ i ], range[ j ] ) ]
                           )
              ) ) );
        
        return CokernelObject( MorphismBetweenDirectSums( L ) );
        
    end );

    AddRandomObjectByInteger( cat,
    
      function( C, n )
        
        return RandomObjectByList( C, [ n, n ] );
        
    end );
   
    AddRandomMorphismWithFixedRangeByList( cat,
    
      function( M, L )
        local pi, K, H;
        
        if not ForAll( L, l -> l in domain ) then
          
          Error( "All entries should belong to the acting domain of the algebra" );
          
        fi;
        
        pi := ProjectiveCover( M );
        
        K := KernelObject( pi );
        
        if IsZero( K ) then
          
          K := Source( pi );
          
        fi;
        
        H := BasisOfExternalHom( K, M );
        
        H := Concatenation( H, [ ZeroMorphism( K, M ) ] );
        
        return Sum( List( L, l -> l * Random( H ) ) );
        
     end );
    
    AddRandomMorphismWithFixedRangeByInteger( cat,
     
      function( M, n )
        
        return RandomMorphismWithFixedRangeByList( M, [ 1 .. n ] * One( domain ) );
        
    end );
    
    AddRandomMorphismWithFixedSourceByList( cat,
    
      function( M, L )
        local iota, K, H;
        
        if not ForAll( L, l -> l in domain ) then
          
          Error( "All entries should belong to the acting domain of the algebra" );
          
        fi;
        
        iota := InjectiveEnvelope( M );
        
        K := CokernelObject( iota );
        
        if IsZero( K ) then
          
          K := Range( iota );
          
        fi;
        
        H := BasisOfExternalHom( M, K );
        
        H := Concatenation( H, [ ZeroMorphism( M, K ) ] );
        
        return Sum( List( L, l -> l * Random( H ) ) );
        
    end );
    
    AddRandomMorphismWithFixedSourceByInteger( cat,
     
      function( M, n )
        
        return RandomMorphismWithFixedSourceByList( M, [ 1 .. n ] * One( domain ) );
        
    end );
    
    AddRandomMorphismWithFixedSourceAndRangeByList( cat,
      
      function( M, N, L )
        local H;
        
        H := BasisOfExternalHom( M, N );
        
        if H = [ ] then
          
          return ZeroMorphism( M, N );
          
        fi;
        
        return Sum( List( H, h -> Random( L ) * h ) );
        
    end );
    
    AddRandomMorphismWithFixedSourceAndRangeByInteger( cat,
      
      function( M, N, n )
        
        return RandomMorphismWithFixedSourceAndRangeByList( M, N, [ 1 .. n ] * One( domain ) );
        
    end );
    
    AddIsProjective( cat,
      function( M )
        
        return IsMonomorphism( EpimorphismFromSomeProjectiveObject( M ) );
    
    end );
    
    to_be_finalized := ValueOption( "FinalizeCategory" );
    
    if to_be_finalized = false then
      
      return cat;
      
    fi;
    
	  Finalize( cat );
	
    return cat;
              
end );

##
InstallMethod( QuiverRepresentation,
               [ IsQuiverRepresentationCategory, IsDenseList, IsList ],
function( cat, objects, morphisms )
  local check;

  check := ValueOption( "CheckWellDefinedness" );
  
  if check = true then
    
    TryNextMethod( );
    
  else
    
    return QuiverRepresentationNC( cat, objects, morphisms );
    
  fi;
  
end );

InstallMethod( QuiverRepresentationHomomorphism,
               "for quiver representations and list",
               [ IsQuiverRepresentation, IsQuiverRepresentation,
                 IsList ],
function( R1, R2, maps )
  local check, cat, ucat, Q, morphisms, i, V1, V2, morphism, m, a, comp1,
        comp2;
  
  check := ValueOption( "CheckWellDefinedness" );
  
  if check = true then
    
    TryNextMethod( );
    
  fi;
 
  cat := CapCategory( R1 );
  if not IsIdenticalObj( cat, CapCategory( R2 ) ) then
    Error( "representations in different categories" );
  fi;
  ucat := VectorSpaceCategory( cat );

  Q := QuiverOfRepresentation( R1 );
  if Length( maps ) > NumberOfVertices( Q ) then
    Error( "too many maps for representation homomorphism: ", Length( maps ), " maps, ",
           "but only ", NumberOfVertices( Q ), " vertices in quiver" );
  fi;

  morphisms := [];
  for i in [ 1 .. NumberOfVertices( Q ) ] do
    V1 := VectorSpaceOfRepresentation( R1, i );
    V2 := VectorSpaceOfRepresentation( R2, i );
    if not IsBound( maps[ i ] ) then
      morphism := ZeroMorphism( V1, V2 );
    else
      m := maps[ i ];
      if IsCapCategoryMorphism( m ) then
        if not IsIdenticalObj( CapCategory( m ), ucat ) then
          Error( "morphism for vertex ", Vertex( Q, i ), " is from wrong category" );
        elif Source( m ) <> V1 then
          Error( "morphism for vertex ", Vertex( Q, i ), " has wrong source",
                 " (is ", Source( m ), ", should be ", V1, ")" );
        elif Range( m ) <> V2 then
          Error( "morphism for vertex ", Vertex( Q, i ), " has wrong range",
                 " (is ", Range( m ), ", should be ", V2, ")" );
        fi;
        morphism := m;
      else
        morphism := LinearTransformationConstructor( cat )( V1, V2, m );
      fi;
    fi;
    Add( morphisms, morphism );
  od;

  return QuiverRepresentationHomomorphismNC( R1, R2, morphisms );
end );

##
BindGlobal( "CHAIN_AND_COCHAIN_CATEGORIES_CONSTRUCTOR",

  function( ChainOrCochainComplexCategory )

    InstallMethod( ChainOrCochainComplexCategory,
            [ IsQuiverRepresentationCategory ],
            
      function( cat )
        local add_extra_methods, complexes, FinalizeCategory, AddExtraMethods, A, domain, to_be_finalized, objects_equality, morphisms_equality;

        objects_equality := ValueOption( "ObjectsEqualityForCache" );

        morphisms_equality := ValueOption( "MorphismsEqualityForCache" );
    
        add_extra_methods := ValueOption( "AddExtraMethods" );
    
        if add_extra_methods = false then
      
          TryNextMethod( );
      
        fi;
    
        complexes := ChainOrCochainComplexCategory( cat : FinalizeCategory := false, AddExtraMethods := false, 
                                                          ObjectsEqualityForCache := objects_equality,
                                                          MorphismsEqualityForCache := morphisms_equality ); 
    
        A := AlgebraOfCategory( cat );
    
        domain := LeftActingDomain( A );
    
        if domain = Rationals then
      
          SetFieldForHomomorphismStructure( complexes, HomalgFieldOfRationals( ) );
      
        elif IsFieldForHomalg( domain ) then
    
          SetFieldForHomomorphismStructure( cat, domain );
      
        fi;
        
        # Lift and Colift can be derived from the homomorphism structure, but the following is much quicker
        AddLift( complexes, COMPUTE_LIFT_IN_COMPLEXES_OF_QUIVER_REPS );
    
        AddColift( complexes, COMPUTE_COLIFT_IN_COMPLEXES_OF_QUIVER_REPS );
        
        # Adding the homomorphism structure this way is at least 50 times better than the standard derivation of homomorphism structure
        # in the package ComplexesForCAP
        ADD_HOMOMORPHISM_STRUCTURE_TO_COMPLEX_CATEGORY_OF_QUIVER_REPRESENTATIONS( complexes );
        
        AddMorphismIntoColiftingObject( complexes,
          function( a )
          
            return NaturalInjectionInMappingCone( IdentityMorphism( a ) );
            
        end );
        
        to_be_finalized := ValueOption( "FinalizeCategory" );
    
        if to_be_finalized = false then
      
          return complexes;
      
        fi;
    
    	  Finalize( complexes );
	
        return complexes;
    
    end );

end );

CHAIN_AND_COCHAIN_CATEGORIES_CONSTRUCTOR( ChainComplexCategory );

CHAIN_AND_COCHAIN_CATEGORIES_CONSTRUCTOR( CochainComplexCategory );

# The natural place for this is file matrix.gi in QPA.
InstallMethod( KroneckerProduct, "for two QPA matrices",
    [ IsQPAMatrix, IsQPAMatrix ],
  function( M1, M2 )
    local k, dim1, dim2, mat;
  
    k := BaseDomain( M1 );
  
    if not IsIdenticalObj( k, BaseDomain( M2 ) ) then
      Error( "Base domains of the given matrices are not identical" );
    fi;
  
    dim1 := DimensionsMat( M1 );
    dim2 := DimensionsMat( M2 );
  
    if dim1[1]*dim2[1] = 0 or dim1[2]*dim2[2] = 0 then
          return MatrixByRows( k, [ dim1[1]*dim2[1], dim1[2]*dim2[2] ], [] );
    fi;
  
    mat := KroneckerProduct( RowsOfMatrix( M1 ), RowsOfMatrix( M2 ) );
  
    return MatrixByRows( k, [ dim1[1]*dim2[1], dim1[2]*dim2[2] ], mat );
  
end );

##
InstallMethod( StackMatricesDiagonally, 
                [ IsQPAMatrix, IsQPAMatrix ],
  function( M1, M2 )
    local d1,d2,F, M1_, M2_; 

    d1 := DimensionsMat( M1 );
    
    d2 := DimensionsMat( M2 );
   
    if d1 = [ 0, 0 ] then
      
      return M2;
      
    fi;
    
    if d2 = [ 0, 0 ] then
      
      return M1;
      
    fi;
   
    F := BaseDomain( M1 );
    
    if F <> BaseDomain( M2 ) then
      
       Error( "matrices over different rings" );
       
    fi;
   
    M1_ := StackMatricesHorizontally( M1, MakeZeroMatrix( F, d1[1], d2[2] ) );
    
    M2_ := StackMatricesHorizontally( MakeZeroMatrix( F, d2[1], d1[2] ), M2 );
    
    return StackMatricesVertically( M1_, M2_ );
    
end );

##
InstallMethod( StackMatricesDiagonally, [ IsDenseList ],
  function( matrices )
  
    return Iterated( matrices, StackMatricesDiagonally );
    
end );

InstallGlobalFunction( STACK_LISTLIST_QPA_MATRICES,
  function( matrices )
    
    if matrices = [] or matrices[ 1 ] = [ ] then
      
      Error( "The input should not be or contain empty lists\n" );
    
    else
      
      return StackMatricesVertically( List( matrices, StackMatricesHorizontally ) );
      
    fi;
    
end );
##
InstallGlobalFunction( BASIS_OF_EXTERNAL_HOM_IN_QUIVER_REPS,
    function( S, R )
    local A, Q, field, S_dimensions, R_dimensions, nr_cols_in_block1, nr_cols_in_block3,
    nr_cols_in_block5, nr_of_vertices, nr_of_arrows, nr_rows_of_block, mat, L, vector,
    block_1, block_2, block_3, block_4, block_5, block, i, u, v, matrices, id_1, id_2,
    source_of_arrow, range_of_arrow, S_i, R_i, Vec, hom;
    A := AlgebraOfRepresentation( S );
    Q := QuiverOfAlgebra( A );
    field := LeftActingDomain( A );
    Vec := function( M )
        return MatrixByCols( field, [ Product( DimensionsMat( M ) ), 1 ], [ Concatenation( ColsOfMatrix( M ) ) ] );
    end;
    S_dimensions := DimensionVector( S );
    R_dimensions := DimensionVector( R );
    nr_of_vertices := Length( S_dimensions );
    mat := MakeZeroMatrix( field, 0, S_dimensions*R_dimensions );
    nr_of_arrows := NumberOfArrows( Q );
    for i in [ 1 .. nr_of_arrows ] do
        source_of_arrow := VertexIndex( Source( Arrow( Q, i ) ) );
        range_of_arrow := VertexIndex( Target( Arrow( Q, i ) ) );
        S_i := RightMatrixOfLinearTransformation( MapForArrow( S, i ) );
        R_i := RightMatrixOfLinearTransformation( MapForArrow( R, i ) );
        id_1 := IdentityMatrix( field, DimensionsMat( S_i )[ 1 ] );
        id_2 := IdentityMatrix( field, DimensionsMat( R_i )[ 2 ] );
        nr_rows_of_block := DimensionsMat( S_i )[ 1 ]*DimensionsMat( R_i )[ 2 ];
        u := Minimum( source_of_arrow, range_of_arrow );
        v := Maximum( source_of_arrow, range_of_arrow );
        if u = 1 then
            nr_cols_in_block1 := 0;
        else
            nr_cols_in_block1 := S_dimensions{[1..u-1]}*R_dimensions{[1..u-1]};
        fi;
        block_1 := MakeZeroMatrix( field, nr_rows_of_block,  nr_cols_in_block1 );
        if u = source_of_arrow then
            block_2 := -KroneckerProduct( TransposedMat( R_i ), id_1 );
        elif u = range_of_arrow then
            block_2 := KroneckerProduct( id_2, S_i );
        fi;

        if v-u in [ 0, 1 ] then
            nr_cols_in_block3 := 0;
        else
            nr_cols_in_block3 := S_dimensions{[u+1..v-1]}*R_dimensions{[u+1..v-1]};
        fi;

        block_3 := MakeZeroMatrix( field, nr_rows_of_block,  nr_cols_in_block3 );

        if v = source_of_arrow then
            block_4 := -KroneckerProduct( TransposedMat( R_i ), id_1 );
        elif v = range_of_arrow then
            block_4 := KroneckerProduct( id_2, S_i );
        fi;

        if v = nr_of_vertices then
            nr_cols_in_block5 := 0;
        else
            nr_cols_in_block5 := S_dimensions{[v+1..nr_of_vertices]}*R_dimensions{[v+1..nr_of_vertices]};
        fi;
        block_5 := MakeZeroMatrix( field, nr_rows_of_block,  nr_cols_in_block5 );
        block := StackMatricesHorizontally( [ block_1, block_2, block_3, block_4, block_5 ] );
        mat := StackMatricesVertically( mat, block );
    od;

    mat := NullspaceMat( TransposedMat( mat ) );
    if mat = fail then
        return [ ];
    fi;
    hom := [ ];
    for L in RowsOfMatrix( mat ) do
    matrices := [ ];
        for i in [ 1 .. nr_of_vertices ] do
            mat := L{[1..S_dimensions[i]*R_dimensions[i]]};
            Add( matrices, MatrixByCols( field, [ S_dimensions[i], R_dimensions[i] ], mat ) );
            L := L{[S_dimensions[i]*R_dimensions[i]+1 .. Length( L ) ]};
        od;
        Add( hom, QuiverRepresentationHomomorphism( S, R, matrices ) );
    od;

    return hom;
end );

## The methods needed to enhance the category with homomorphism structure
##
InstallMethodWithCrispCache( BasisOfExternalHom,
  [ IsQuiverRepresentation, IsQuiverRepresentation ],
  function( a, b )
    local B;
    
    #if HasIsProjective( a ) and IsProjective( a ) and HasIsProjective( b ) and IsProjective( b ) then
    #        
    #  # This method is not quicker than BasisOfHom but it make it possible to compute
    #  # Hom(a,b) for very big representations with out memory issues.
    #  B := BASIS_OF_EXTERNAL_HOM_BETWEEN_PROJECTIVE_QUIVER_REPRESENTATIONS( a, b );
    #  
    #  if B <> fail then
    #    
    #    return B;
    #    
    #  else
    #    
    #    return BasisOfHom( a, b );
    #  
    #  fi;
    #  
    #fi;
      
    return BasisOfHom( a, b );
    
end );

##
InstallMethod( CoefficientsOfLinearMorphism, # w.r.t BasisOfExternalHom
            [ IsQuiverRepresentationHomomorphism ],
  function( f )
    local hom_basis, Q, k, V, L, vector, mat, sol;

    hom_basis := BasisOfExternalHom( Source( f ), Range( f ) );
    
    return COEFFICIENTS_OF_LINEAR_MORPHISM( hom_basis, f );
  
end );

InstallMethod( MultiplyWithElementInFieldForHomomorphismStructure,
            [ IsMultiplicativeElement, IsQuiverRepresentationHomomorphism ],
  function( e, phi )
    local category;
    
    category := CapCategory( phi );
    
    if not HasFieldForHomomorphismStructure( category ) then
      
      Error( "The attribute FieldForHomomorphismStructure must be set for the category of the given morphism!\n" );
      
    fi;
    
    if not e in FieldForHomomorphismStructure( category ) then
      
      Error( "The given element must belong to the field of the homomorphism structure!\n" );
      
    fi;
    
    return e * phi;
    
end );

InstallMethodWithCrispCache( BasisOfExternalHom,
  [ IsBoundedChainOrCochainComplex, IsBoundedChainOrCochainComplex ], # of quiver representations
  function( C1, C2 )
    local category, cat, m, n, A, R1, R2, B;
    
    category := CapCategory( C1 );
    
    cat := UnderlyingCategory( category );
    
    if not IsQuiverRepresentationCategory( cat ) then
      
      TryNextMethod( );
      
    fi;
    
    m := Minimum( ActiveLowerBound( C1 ), ActiveLowerBound( C2 ) ) + 1;
    
    n := Maximum( ActiveUpperBound( C1 ), ActiveUpperBound( C2 ) ) - 1;
    
    if IsChainComplex( C1 ) then
      
        A := PRODUCT_OF_QUIVER_ALGEBRAS( AlgebraOfRepresentation( C1[m] ), n, m );
        
    else
      
        A := PRODUCT_OF_QUIVER_ALGEBRAS( AlgebraOfRepresentation( C1[m] ), m, n );
        
    fi;
    
    R1 := CONVERT_COMPLEX_OF_QUIVER_REPS_TO_QUIVER_REP( C1, A );
    
    R2 := CONVERT_COMPLEX_OF_QUIVER_REPS_TO_QUIVER_REP( C2, A );
    
    B := BasisOfExternalHom( R1, R2 );
    
    return List( B, mor -> CONVERT_QUIVER_REP_MORPHISM_TO_COMPLEX_MORPHISM_OF_QUIVER_REPS( C1, C2, mor, A ) );
    
end );

##
InstallMethod( CoefficientsOfLinearMorphism, # w.r.t BasisOfExternalHom
            [ IsBoundedChainOrCochainMorphism ],
  function( phi )
    local category, cat, m, n, A, f;
    
    category := CapCategory( phi );
    
    cat := UnderlyingCategory( category );
    
    if not IsQuiverRepresentationCategory( cat ) then
      
      TryNextMethod( );
      
    fi;
    
    m := ActiveLowerBound( Source( phi ) ) + 1;
    
    n := ActiveUpperBound( Source( phi ) ) - 1;

    if IsChainMorphism( phi ) then
      
        A := PRODUCT_OF_QUIVER_ALGEBRAS( AlgebraOfRepresentation( Source( phi[ m ] ) ), n, m );
        
    else
      
        A := PRODUCT_OF_QUIVER_ALGEBRAS( AlgebraOfRepresentation( Source( phi[ m ] ) ), m, n );
        
    fi;

    f := CONVERT_COMPLEX_MORPHISM_OF_QUIVER_REPS_TO_QUIVER_REP_MORPHISM( phi, A );

    return CoefficientsOfLinearMorphism( f );
    
end );

InstallMethod( MultiplyWithElementInFieldForHomomorphismStructure,
            [ IsMultiplicativeElement, IsBoundedChainOrCochainMorphism ],
  function( e, phi )
    local category, cat;
    
    category := CapCategory( phi );
    
    cat := UnderlyingCategory( category );
    
    if not IsQuiverRepresentationCategory( cat ) then
      
      TryNextMethod( );
      
    fi;
    
    if not HasFieldForHomomorphismStructure( category ) then
      
      Error( "The attribute FieldForHomomorphismStructure must be set for the category of the given morphism!\n" );
      
    fi;
    
    if not e in FieldForHomomorphismStructure( category ) then
      
      Error( "The given element must belong to the field of the homomorphism structure!\n" );
      
    fi;
    
    return e * phi;
    
end );


InstallGlobalFunction( COMPUTE_LIFT_IN_QUIVER_REPS,
  function( f, g )
    local hom_basis, Q, k, V, hom_basis_composed_with_g, L, vector, mat, sol, lift, h;
    
    if IsZeroForObjects( Range( f ) ) then
      
        return ZeroMorphism( Source( f ), Source( g ) );
        
    fi;

    hom_basis := BasisOfExternalHom( Source( f ), Source( g ) );
    
    # if hom_basis = [] then there is only the zero morphism between source(f) and source(g)
    # Thus f must be zero in order for lift to exist.
    
    if IsZeroForMorphisms( f ) then
        
      return ZeroMorphism( Source( f ), Source( g ) );
        
    fi;
 
    if hom_basis = [ ] then
             
      return fail;
      
    fi;
    
    Q := QuiverOfRepresentation( Source( f ) );
    
    k := LeftActingDomain( AlgebraOfRepresentation( Source( f ) ) );
    
    V := Vertices( Q );
    
    hom_basis_composed_with_g := List( hom_basis, m -> PreCompose( m, g ) );
    
    L := List( V, v -> Concatenation( 
          [ RightMatrixOfLinearTransformation( MapForVertex( f, v ) ) ],
            List( hom_basis_composed_with_g,
              h -> RightMatrixOfLinearTransformation( MapForVertex( h, v ) ) ) ) );
    
    L := Filtered( L, l -> ForAll( l, m -> not IsZero( DimensionsMat( m )[ 1 ]*DimensionsMat( m )[ 2 ] ) ) );
    
    L := List( L, l ->  List( l, m -> MatrixByCols( k, [ Concatenation( ColsOfMatrix( m ) ) ] ) ) );

    L := List( TransposedMat( L ), l -> StackMatricesVertically( l ) );
     
    vector := StandardVector( k, ColsOfMatrix( L[ 1 ] )[ 1 ] );
    
    mat := TransposedMat( StackMatricesHorizontally( List( [ 2 .. Length( L ) ], i -> L[ i ] ) ) );
    
    sol := SolutionMat( mat, vector );

    if sol = fail then
      
      return fail;
        
    else

      sol := ShallowCopy( AsList( sol ) );

      lift := ZeroMorphism( Source( f ), Source( g ) );
    
      for h in hom_basis do
      
        if not IsZero( sol[ 1 ] ) then
        
          lift := lift + sol[ 1 ]*h;
             
        fi;
         
        Remove( sol, 1 );
    
      od;
    
    fi;
    
    return lift;
    
end );

##
InstallGlobalFunction( COMPUTE_COLIFT_IN_QUIVER_REPS,
  function( f, g )
    local hom_basis, Q, k, V, hom_basis_composed_with_f, L, vector, mat, sol, colift, h;

    hom_basis := BasisOfExternalHom( Range( f ), Range( g ) );
    
    # if hom_basis = [] then there is only the zero morphism between range(f) and range(g)
    # Thus g must be zero in order for colift to exist.
    
    if IsZeroForMorphisms( g ) then
        
	    return ZeroMorphism( Range( f ), Range( g ) );
      
    fi;
 
    if hom_basis = [ ] then
             
	    return fail;
      
    fi;
    
    Q := QuiverOfRepresentation( Source( f ) );
    
    k := LeftActingDomain( AlgebraOfRepresentation( Source( f ) ) );
    
    V := Vertices( Q );
    
    hom_basis_composed_with_f := List( hom_basis, m -> PreCompose( f, m ) );
    
    L := List( V, v -> Concatenation( 
            [ RightMatrixOfLinearTransformation( MapForVertex( g, v ) ) ],
              List( hom_basis_composed_with_f, 
                h -> RightMatrixOfLinearTransformation( MapForVertex( h, v ) ) ) ) );
    
    # this line is added because I get errors when MatrixByCols recieve empty matrix
    # it is still true since i only delete zero matrices from the equation system.
    L := Filtered( L, l -> ForAll( l, m -> not IsZero( DimensionsMat( m )[ 1 ]*DimensionsMat( m )[ 2 ] ) ) );
    
    L := List( L, l ->  List( l, m -> MatrixByCols( k, [ Concatenation( ColsOfMatrix( m ) ) ] ) ) );

    L := List( TransposedMat( L ), l -> StackMatricesVertically( l ) );
    
    vector := StandardVector( k, ColsOfMatrix( L[ 1 ] )[ 1 ] );
    
    mat := TransposedMat( StackMatricesHorizontally( List( [ 2 .. Length( L ) ], i -> L[ i ] ) ) );
    
    sol := SolutionMat( mat, vector );

    if sol = fail then
      
     return fail;
     
    else
      
      sol := ShallowCopy( AsList( sol ) );
      
      colift := ZeroMorphism( Range( f ), Range( g ) );
      
      for h in hom_basis do
        
        if not IsZero( sol[ 1 ] ) then
          
          colift := colift + sol[ 1 ] * h;
            
        fi;
        
        Remove( sol, 1 );
        
      od;

    fi;
    
    return colift;
    
end );

InstallGlobalFunction( LINEAR_QUIVER,
	# IsDirection, IsObject, IsInt, IsInt
  function( d, k, m, n )
    local L, kL, c, l, constructor;
    if d = RIGHT then
      	constructor := "RightQuiver";
    else
        constructor := "LeftQuiver";
    fi;

    if m<=n then
    	L := ValueGlobal(constructor)(  Concatenation( "L(v", String(m), ")[d", String(m), "]" ), n - m + 1,
    		List( [ m .. n - 1 ], i-> [ Concatenation( "v", String(i) ), Concatenation( "v", String(i+1) ) ]  ) );
    	kL := PathAlgebra( k, L );
    	c := ArrowLabels( L );
    	l := List( [ 1 .. Length( c )-1 ], i -> [ c[i], c[i+1] ] );
	if d = RIGHT then
    	    l := List( l, label -> PrimitivePathByLabel( L, label[1] )*PrimitivePathByLabel( L, label[2] ) );
	else
	    l := List( l, label -> PrimitivePathByLabel( L, label[2] )*PrimitivePathByLabel( L, label[1] ) );
	fi;
    	l := List( l, r -> QuiverAlgebraElement( kL, [1], [r] ) );
    	return [ L, kL, l ];
    else
        L := ValueGlobal(constructor)(  Concatenation( "L(v", String(n), ")[d", String(n+1), "]" ), m - n + 1,
	        List( [ n .. m - 1 ], i-> [ Concatenation( "v", String(i+1) ), Concatenation( "v", String(i) ) ]  ) );
        kL := PathAlgebra( k, L );
	c := ArrowLabels( L );
	l := List( [ 1 .. Length( c )-1 ], i -> [ c[i+1], c[i] ] );
	if d = RIGHT then
	    l := List( l, label -> PrimitivePathByLabel( L, label[1] )*PrimitivePathByLabel( L, label[2] ) );
	else
	    l := List( l, label -> PrimitivePathByLabel( L, label[2] )*PrimitivePathByLabel( L, label[1] ) );
	fi;
	l := List( l, r -> QuiverAlgebraElement( kL, [1], [r] ) );
	L!.("m") := m;
	L!.("n") := n;
	return [ L, kL, l ];
    fi;
end );

InstallGlobalFunction( LINEAR_LEFT_QUIVER,
	#[ IsObject, IsInt, IsInt ],
  function( k, m, n )
    return LINEAR_QUIVER( LEFT, k, m, n );
end );

InstallGlobalFunction( LINEAR_RIGHT_QUIVER,
	#[ IsObject, IsInt, IsInt ],
  function( k, m, n )
    return LINEAR_QUIVER( RIGHT, k, m, n );
end );

# InstallMethod( ArrowsBetweenTwoVertices,
# 		[ IsVertex, IsVertex ],
#   function( v1, v2 )
#     return Intersection( OutgoingArrows( v1 ), IncomingArrows( v2 ) );
# end );

InstallGlobalFunction( PRODUCT_OF_QUIVER_ALGEBRAS,
  function( Aq, m, n )
    local k, Lmn, AL;
    k := LeftActingDomain( Aq );
    Lmn := LINEAR_RIGHT_QUIVER( k, m, n );
    if Lmn[3] = [ ] then
        AL := Lmn[2];
    else
        AL := QuotientOfPathAlgebra( Lmn[2], Lmn[3] );
    fi;
    return TensorProductOfAlgebras( AL, Aq );
end );

# #FIXME Apply caching
InstallGlobalFunction( PRODUCT_OF_QUIVER_REPRESENTATIONS,
  function( list_of_objs )
    local A, matrices, identity_matrices, kronecker_product, n, L, current, D, i;
    
    A := TensorProductOfAlgebras( List(  list_of_objs, AlgebraOfRepresentation) );
    
    matrices := List( list_of_objs, a -> MatricesOfRepresentation( a ) );;
    
    identity_matrices := List( list_of_objs, a -> List( DimensionVector( a ), d -> IdentityMatrix( Rationals, d ) ) );;
    
    kronecker_product := function( L ) return Iterated( L, KroneckerProduct ); end;;
    
    n := Length( list_of_objs );
    
    L := [ ];
    
    for i in Reversed( [ 1 .. n ] ) do
      
      current := ShallowCopy( identity_matrices );;
      
      current[ i ] := matrices[ i ];
      
      L := Concatenation( L, List( Cartesian( current ), kronecker_product ) );;
      
    od;
    
    D :=  List( Cartesian( List( list_of_objs, DimensionVector ) ), Product );;
    
    return QuiverRepresentation( A, D, L );;
  
end );

InstallGlobalFunction( PRODUCT_OF_QUIVER_REPRESENTATION_HOMOMORPHISMS,
  function( list_of_mors )
    local matrices, kronecker_product, a, b;
    
    matrices := List( list_of_mors, MatricesOfRepresentationHomomorphism );
    
    kronecker_product := function( L ) return Iterated( L, KroneckerProduct ); end;;
    
    matrices := List( Cartesian( matrices ), kronecker_product );
    
    a := PRODUCT_OF_QUIVER_REPRESENTATIONS( List( list_of_mors, Source ) );
    
    b := PRODUCT_OF_QUIVER_REPRESENTATIONS( List( list_of_mors, Range ) );
    
    return QuiverRepresentationHomomorphism( a, b, matrices );
    
end );


InstallMethod( TensorProductFunctor,
  [ IsQuiverAlgebra and HasTensorProductFactors ],
  function( A )
    local list_of_algebras, cat, cats, product_cat, n, name, F;
     
    list_of_algebras := TensorProductFactors( A );
    
    cat := CategoryOfQuiverRepresentations( A );
    
    cats := List( list_of_algebras, CategoryOfQuiverRepresentations );
    
    product_cat := CallFuncList( Product, cats );
    
    n := Length( cats );
    
    name := Concatenation( "Product of quiver representations functor from ", Name( product_cat ), " to ", Name( cat ) );
    
    F := CapFunctor( name, product_cat, cat );
    
    # M_1 x M_2 x ... x M_n -> M_1 ⊠ M_2 ⊠ ... ⊠ M_n
    AddObjectFunction( F,
      function( product_obj )
        local list_of_objs;
        
        list_of_objs := List( [ 1 .. n ], i -> product_obj[ i ] );
        
        return PRODUCT_OF_QUIVER_REPRESENTATIONS( list_of_objs );
        
    end );
    
    # f_1 x f_2 x ... x f_n -> f_1 ⊠ f_2 ⊠ ... ⊠ f_n
    AddMorphismFunction( F,
      function( source, product_mor, range )
        local list_of_mors;
        
        list_of_mors := List( [ 1 .. n ], i -> product_mor[ i ] );
      
        return PRODUCT_OF_QUIVER_REPRESENTATION_HOMOMORPHISMS( list_of_mors );
        
    end );

    return F;
    
end );


InstallGlobalFunction( CONVERT_COMPLEX_OF_QUIVER_REPS_TO_QUIVER_REP,
  function( C, A  )
    local L, m, n, Q, dimension_vector, matrices1, matrices2, matrices;

    L := QuiverOfAlgebra( TensorProductFactors( A )[1] );
    m := ShallowCopy( Label( Vertex( L, 1 ) ) );
    RemoveCharacters( m, "v" );
    m := Int(m);
    n := m + NumberOfVertices( L ) - 1;
    if IsChainComplex( C ) then
        Q := QuiverOfAlgebra( A );
        dimension_vector := Concatenation( List( [ m .. n ], i-> DimensionVector( C[ i ] ) ) );
        matrices1 := Concatenation( List( [ m .. n ], i -> MatricesOfRepresentation( C[ i ] ) ) );
        matrices2 := Concatenation( List( [ m + 1 .. n ], i-> MatricesOfRepresentationHomomorphism( C^i ) ) );
        matrices := Concatenation( matrices1, matrices2 );
        return QuiverRepresentation( A, dimension_vector, Arrows( Q ), matrices );
    else
        Q := QuiverOfAlgebra( A );
        dimension_vector := Concatenation( List( [ m .. n ], i-> DimensionVector( C[ i ] ) ) );
        matrices1 := Concatenation( List( [ m .. n ], i -> MatricesOfRepresentation( C[ i ] ) ) );
        matrices2 := Concatenation( List( [ m .. n - 1 ], i-> MatricesOfRepresentationHomomorphism( C^i ) ) );
        matrices := Concatenation( matrices1, matrices2 );
        return QuiverRepresentation( A, dimension_vector, Arrows( Q ), matrices );
    fi;

end );


InstallGlobalFunction( CONVERT_COMPLEX_MORPHISM_OF_QUIVER_REPS_TO_QUIVER_REP_MORPHISM,
  function( phi, A )
    local L,m,n, matrices, r1, r2;
    L := QuiverOfAlgebra( TensorProductFactors( A )[1] );
    m := ShallowCopy( Label( Vertex( L, 1 ) ) );
    RemoveCharacters( m, "v" );
    m := Int(m);
    n := m + NumberOfVertices( L ) - 1;
    matrices := Concatenation( List( [ m .. n ], i -> MatricesOfRepresentationHomomorphism( phi[ i ] ) ) );
    r1 := CONVERT_COMPLEX_OF_QUIVER_REPS_TO_QUIVER_REP( Source( phi ), A );
    r2 := CONVERT_COMPLEX_OF_QUIVER_REPS_TO_QUIVER_REP( Range( phi ), A );
    return QuiverRepresentationHomomorphism( r1, r2, matrices );
end );


InstallGlobalFunction( CONVERT_QUIVER_REP_MORPHISM_TO_COMPLEX_MORPHISM_OF_QUIVER_REPS,
  function( C1, C2, mor, A )
    local Q, L, q, m, n, mats;
    # Do the compatibility stuff
    Q := QuiverOfAlgebra( A );
    L := QuiverOfAlgebra( TensorProductFactors( A )[1] );
    q := QuiverOfAlgebra( TensorProductFactors( A )[2] );
    m := ShallowCopy( Label( Vertex( L, 1 ) ) );
    RemoveCharacters( m, "v" );
    m := Int(m);
    n := m + NumberOfVertices( L ) - 1;
#     maps := MatricesOfRepresentationHomomorphism( mor );
    mats := MatricesOfRepresentationHomomorphism( mor );
    mats := List( [ 1 .. NumberOfVertices( L ) ],
                i -> List( [ 1 .. NumberOfVertices( q ) ],
                        j-> mats[ (i-1)*NumberOfVertices( q ) + j ] ) );
    mats := List( [ m .. n ], k -> QuiverRepresentationHomomorphism( C1[k], C2[k], mats[k-m+1] ) );
    if IsChainComplex( C1 ) then
        return ChainMorphism( C1, C2, mats, m );
    else
        return CochainMorphism( C1, C2, mats, m );
    fi;
end );

InstallGlobalFunction( COMPUTE_LIFT_IN_COMPLEXES_OF_QUIVER_REPS,
  function( f, g )
    local m, n, A, f_, g_, lift;
    
    m := Minimum( ActiveLowerBound( Source(f) ), ActiveLowerBound( Source(g) ) ) + 1;
    
    n := Maximum( ActiveUpperBound( Source(f) ), ActiveUpperBound( Source(g) ) ) - 1;

    if IsChainMorphism( f ) then
      
      A := PRODUCT_OF_QUIVER_ALGEBRAS( AlgebraOfRepresentation( Source(f[ m ]) ), n, m );
    
    else
      
      A := PRODUCT_OF_QUIVER_ALGEBRAS( AlgebraOfRepresentation( Source(f[ m ]) ), m, n );
    
    fi;

    f_ := CONVERT_COMPLEX_MORPHISM_OF_QUIVER_REPS_TO_QUIVER_REP_MORPHISM( f, A );
    
    g_ := CONVERT_COMPLEX_MORPHISM_OF_QUIVER_REPS_TO_QUIVER_REP_MORPHISM( g, A );

    lift := COMPUTE_LIFT_IN_QUIVER_REPS( f_, g_ );

    if lift = fail then
      
        return fail;
        
    else
      
        return CONVERT_QUIVER_REP_MORPHISM_TO_COMPLEX_MORPHISM_OF_QUIVER_REPS( Source(f), Source( g ), lift, A );
        
    fi;
    
end );

InstallGlobalFunction( COMPUTE_COLIFT_IN_COMPLEXES_OF_QUIVER_REPS,
  function( f, g )
    local m, n, A, f_, g_, colift;
    
    m := Minimum( ActiveLowerBound( Range(f) ), ActiveLowerBound( Range(g) ) ) + 1;
    
    n := Maximum( ActiveUpperBound( Range(f) ), ActiveUpperBound( Range(g) ) ) - 1;

    if IsChainMorphism( f ) then
      
      A := PRODUCT_OF_QUIVER_ALGEBRAS( AlgebraOfRepresentation( Source(f[ m ]) ), n, m );
      
    else
      
      A := PRODUCT_OF_QUIVER_ALGEBRAS( AlgebraOfRepresentation( Source(f[ m ]) ), m, n );
      
    fi;

    f_ := CONVERT_COMPLEX_MORPHISM_OF_QUIVER_REPS_TO_QUIVER_REP_MORPHISM( f, A );
    
    g_ := CONVERT_COMPLEX_MORPHISM_OF_QUIVER_REPS_TO_QUIVER_REP_MORPHISM( g, A );

    colift := COMPUTE_COLIFT_IN_QUIVER_REPS( f_, g_ );

    if colift = fail then
      
        return fail;
        
    else
      
        return CONVERT_QUIVER_REP_MORPHISM_TO_COMPLEX_MORPHISM_OF_QUIVER_REPS( Range(f), Range( g ), colift, A );
        
    fi;
    
end );

InstallGlobalFunction( COMPUTE_HOMOTOPY_IN_COMPLEXES_OF_QUIVER_REPS,
  
  function( phi )
    local index, A, B, m, n, var_list, Hom_i, Q, k, V, mat, f_mat_v, d, current_mat, vector, sol, homotopy_morphisms, h, i, j, v, var;
    
    if IsChainMorphism( phi ) then
      
      index := 1;
      
    else
      
      index := -1;
      
    fi;
    
    A := Source( phi );
    B := Range( phi );

    ObjectsSupport( A );
    ObjectsSupport( B );

    m := Minimum( ActiveLowerBound( A ) + 1, ActiveLowerBound( B ) + 1 );
    
    n := Maximum( ActiveUpperBound( A ) - 1, ActiveUpperBound( B ) - 1 );

    var_list := [ ];
    
    for i in [ m .. n ] do
      
      Hom_i := BasisOfExternalHom( A[ i ], B[ i + index ] );
      
      for j in Hom_i do
        
        Add( var_list, [ i, j ] );
         
      od;
    
    od;

    Q := QuiverOfRepresentation( B[ m ] );
    
    k := LeftActingDomain( AlgebraOfRepresentation( A[ m ] ) );
    
    V := Vertices( Q );

    mat := [ ];
    
    for i in [ m .. n ] do
      
      for v in  V do
        
        f_mat_v := RightMatrixOfLinearTransformation( MapForVertex( phi[ i ], v ) );
        
        d := DimensionsMat( f_mat_v );
        
        current_mat := [ f_mat_v ];
        
        for var in var_list do
          
          if  var[ 1 ] = i then
            
            Add( current_mat, RightMatrixOfLinearTransformation( MapForVertex( var[ 2 ], v ) )*
                                RightMatrixOfLinearTransformation( MapForVertex( B^( i + index ), v ) ) );
          
          elif var[ 1 ] = i - index then
            
            Add( current_mat, RightMatrixOfLinearTransformation( MapForVertex( A^i, v ) )*
                                RightMatrixOfLinearTransformation( MapForVertex( var[ 2 ], v ) ) );
          
          else
            
            Add( current_mat, MakeZeroMatrix( k, d[ 1 ], d[ 2 ] ) );
            
          fi;
          
        od;
        
        if not ForAll( current_mat, IsZero ) then Add( mat, current_mat ); fi;
        
      od;
    
    od;
    
    mat := TransposedMat( mat );
    
    mat := List( mat, l -> StackMatricesDiagonally( l ) );
    
    mat := List( mat,
    
      function( m )
        local cols;
        
        cols := ColsOfMatrix( m );
        
        cols := Concatenation( cols );
        
        return MatrixByCols( k, [ cols ] );
        
      end );
    
    if mat = [ ] then
      
      sol := List( [ m .. n ], i -> ZeroMorphism( A[ i ], B[ i + index ] ) );
      
      return [ [ m, n ], sol ];
      
    fi;
    
    vector := StandardVector( k, ColsOfMatrix( mat[ 1 ] )[ 1 ] );

    mat := TransposedMat( StackMatricesHorizontally( List( [ 2 .. Length( mat ) ], i-> mat[ i ] ) ) );

    sol := SolutionMat( mat, vector );

    if sol = fail then
      
      return fail;
       
    else
      
      sol := ShallowCopy( AsList( sol ) );
      
      homotopy_morphisms := [ ];
      
      for i in [ m .. n ] do
        
        h := ZeroMorphism( A[ i ], B[ i + index ] );
           
        for var in var_list do
             
          if var[ 1 ] = i then
            
            h := h + sol[ 1 ] * var[ 2 ];
            
            Remove( sol, 1 );
          
          fi;
        
        od;
           
        Add( homotopy_morphisms, h );
          
        od;

    return [ [ m, n ], homotopy_morphisms ];
    
    fi;

end );

BindGlobal( "CERTAIN_ROWS",
  function( mat, L )
    local rows, l;
    
    rows := RowsOfMatrix( mat );
    
    l := Filtered( L, e -> e in [ 1 .. DimensionsMat( mat )[ 1 ] ] );
     
    if l = [ ] then
      
      return MakeZeroMatrix( BaseDomain( mat ), 0, DimensionsMat( mat )[ 2 ] );
      
    fi;
    
    if DimensionsMat( mat )[ 2 ] = 0 then
      
      return MakeZeroMatrix( BaseDomain( mat ), Length( L ), 0 );
      
    fi;
    
    rows := rows{l};
   
    return MatrixByRows( BaseDomain( mat ), rows );
  
end );
    
 BindGlobal( "CERTAIN_COLS",
  function( mat, L )
    local cols, l;
    
    cols := ColsOfMatrix( mat );
    
    l := Filtered( L, e -> e in [ 1 .. DimensionsMat( mat )[ 2 ] ] );
 
    if l = [ ] then
      
      return MakeZeroMatrix( BaseDomain( mat ), DimensionsMat( mat )[ 1 ], 0 );
      
    fi;
    
    if DimensionsMat( mat )[ 1 ] = 0 then
      
      return MakeZeroMatrix( BaseDomain( mat ), 0, Length( L ) );
      
    fi;
    
    cols := cols{l};
    
    return MatrixByCols( BaseDomain( mat ), cols );
  
end );

InstallMethodWithCrispCache( DECOMPOSITION_OF_PROJECTIVE_QUIVER_REPRESENTATION,
  [ IsQuiverRepresentation ],
  function( P )
    local A, quiver, ind_A, n, nr_arrows, matrices_of_indec_projs, dims, matrices_of_P, func, matrices, d;
    
    if IsZero( P ) then
      
      return [ P ];
      
    fi;
    
    if not IsProjective( P ) then
      
      Error( "The given object should be projective!" );
      
    fi;
    
    A := AlgebraOfRepresentation( P );
    
    quiver := QuiverOfAlgebra( A );
    
    ind_A := IndecProjRepresentations( A );
 
    n := Length( ind_A ) - 1;
    
    nr_arrows := NumberOfArrows( quiver );
       
    matrices_of_indec_projs := List( ind_A, p -> List( [ 1 .. nr_arrows ],
          i -> RightMatrixOfLinearTransformation( MapForArrow( p, i ) ) ) );
    
    dims := List( matrices_of_indec_projs, matrices -> List( matrices, DimensionsMat ) );
    
    matrices_of_P := List( [ 1 .. nr_arrows ],
      i -> RightMatrixOfLinearTransformation( MapForArrow( P, i ) ) );
    
    func := function( matrices )
      local dims_of_matrices, p;
      
      dims_of_matrices := List( matrices, DimensionsMat );
      
      p := Positions( dims, dims_of_matrices );
      
      if Length( p ) = 1 then
        
        return [ ind_A[ p[1] ] ];
        
      elif Length( p ) > 2 then
      
        Error( "This should not happen, please report this" );
      
      fi;
      
      p := PositionProperty( dims,
        dim -> 
          ListN( dim, matrices,
            function(l,m)
              return CERTAIN_COLS( CERTAIN_ROWS( m, [ 1 .. l[1] ] ), [ 1 .. l[2] ] );
            end ) 
            =
            matrices_of_indec_projs[ Position( dims, dim ) ]
      );
      
      if p = fail then
        
        return fail;
        
      fi;
      
      matrices := ListN( dims[ p ], matrices,
        function( l, m )
          return CERTAIN_COLS( CERTAIN_ROWS( m, [ l[1] + 1 .. DimensionsMat( m )[ 1 ] ] ), 
                      [ l[ 2 ] + 1 .. DimensionsMat( m )[ 2 ] ] );
      end );
      
      return Concatenation( [ ind_A[ p ] ], func( matrices ) );
    
    end;
    
    d := func( matrices_of_P );
    
    if fail in d then
      
      return fail;
      
    fi;
    
    return d;
    
end );

InstallGlobalFunction( BASIS_OF_EXTERNAL_HOM_BETWEEN_PROJECTIVE_QUIVER_REPRESENTATIONS,
  function( P1, P2 )
    local cat, D1, D2, m, n, morphisms, current_morphisms, hom, D_1_to_i_minus_1,
      D_2_to_j_minus_1, z1, D_i_plus_1_to_m, D_j_plus_1_to_n, z2, i, j, phi;
    
    cat := CapCategory( P1 );
    
    D1 := DECOMPOSITION_OF_PROJECTIVE_QUIVER_REPRESENTATION( P1 );
    
    D2 := DECOMPOSITION_OF_PROJECTIVE_QUIVER_REPRESENTATION( P2 );
    
    if D1 = fail or D2 = fail then
      
      Error( "?" );
      
    fi;
    
    m := Length( D1 );
    
    n := Length( D2 );
     
    morphisms := [ ];
    
    for i in [ 1 .. m ] do
      
      for j in [ 1 .. n ] do
        
        current_morphisms := [ ];
        
        hom := BasisOfHom( D1[ i ], D2[ j ] );
       
        if hom <> [ ] then
          
          D_1_to_i_minus_1 := Concatenation( [ ZeroObject( cat ) ], D1{ [1 .. i - 1 ] } );
          D_2_to_j_minus_1 := Concatenation( [ ZeroObject( cat ) ], D2{ [1 .. j - 1 ] } );
           
          D_i_plus_1_to_m := Concatenation( [ ZeroObject( cat ) ], D1{ [ i + 1 .. m ] } );
          D_j_plus_1_to_n := Concatenation( [ ZeroObject( cat ) ], D2{ [ j + 1 .. n ] } ); 
          
          z1 := ZeroMorphism( DirectSum( D_1_to_i_minus_1 ), DirectSum( D_2_to_j_minus_1 ) );
          z2 := ZeroMorphism( DirectSum( D_i_plus_1_to_m ), DirectSum( D_j_plus_1_to_n ) );
          
          for phi in hom do
           
            Add( current_morphisms,  
              DirectSumFunctorial( 
                [ z1, phi, z2 ] 
              ) 
            );
         
          od;
        
          morphisms := Concatenation( morphisms, current_morphisms );
          
        fi;
        
      od;
      
    od;
        
    return morphisms;
    
end );

BindGlobal( "BASIS_OF_EXTERNAL_HOM_BETWEEN_PROJECTIVE_QUIVER_REPRESENTATIONS2",
  function( P1, P2 )
    local cat, D1, D2, m, n, morphisms, temp, current_morphisms, current_temp, hom, i, j, phi;
    
    cat := CapCategory( P1 );
    
    D1 := DECOMPOSITION_OF_PROJECTIVE_QUIVER_REPRESENTATION( P1 );
    
    D2 := DECOMPOSITION_OF_PROJECTIVE_QUIVER_REPRESENTATION( P2 );
    
    if D1 = fail or D2 = fail then
      
      Error( "?" );
      
    fi;
    
    m := Length( D1 );
    
    n := Length( D2 );
     
    morphisms := [ ];
    
    temp := List( [ 1 .. m ], i -> List( [ 1 .. n ], j -> ZeroMorphism( D1[ i ], D2[ j ] ) ) );
    
    for i in [ 1 .. m ] do
      
      for j in [ 1 .. n ] do
        
        current_morphisms := [ ];
        
        current_temp := StructuralCopy( temp );
        
        hom := BasisOfExternalHom( D1[ i ], D2[ j ] );
       
        if hom <> [ ] then
          
          for phi in hom do
           
            current_temp[ i ][ j ] := phi;
            
            Add( current_morphisms, current_temp );
         
          od;
        
          morphisms := Concatenation( morphisms, current_morphisms );
          
        fi;
        
      od;
      
    od;
        
    return morphisms;
    
end );

##
InstallMethodWithCrispCache( COEFFICIENTS_OF_LINEAR_MORPHISM,
            [ IsList, IsQuiverRepresentationHomomorphism ],
  function( hom_basis, f )
    local Q, k, V, L, vector, mat, sol;

    if hom_basis = [ ] then
      
      return [ ];
      
    fi;
  
    Q := QuiverOfRepresentation( Source( f ) );
  
    k := LeftActingDomain( AlgebraOfRepresentation( Source( f ) ) );
  
    V := Vertices( Q );
  
    L := List( V, v -> Concatenation( [ RightMatrixOfLinearTransformation( MapForVertex( f, v ) ) ],
                                      List( hom_basis, h -> RightMatrixOfLinearTransformation( MapForVertex( h, v ) ) ) ) );
    
    L := Filtered( L, l -> ForAll( l, m -> not IsZero( DimensionsMat( m )[ 1 ]*DimensionsMat( m )[ 2 ] ) ) );
    
    L := List( L, l ->  List( l, m -> MatrixByCols( k, [ Concatenation( ColsOfMatrix( m ) ) ] ) ) );

    L := List( TransposedMat( L ), l -> StackMatricesVertically( l ) );
    
    vector := StandardVector( k, ColsOfMatrix( L[ 1 ] )[ 1 ] );
    
    mat := TransposedMat( StackMatricesHorizontally( List( [ 2 .. Length( L ) ], i -> L[ i ] ) ) );
    
    sol := SolutionMat( mat, vector );

    return AsList( sol );
  
end );


InstallMethod( MORPHISM_OF_PROJECTIVE_QUIVER_REPS_AS_LIST_OF_RECORDS,
    [ IsQuiverRepresentationHomomorphism ],
  function( f )
    local cat, A, ind, n, morphisms, func;
    
    cat := CapCategory( f );
    
    A := AlgebraOfCategory( cat );
    
    ind := IndecProjRepresentations( A );
    
    n := Length( ind );
    
    ind := List( [ 1 .. n ], i -> TwistedCotangentSheafAsQuiverRepresentation( A, i - 1 ) );
    
    morphisms := MORPHISM_OF_PROJECTIVE_QUIVER_REPS_AS_LIST_OF_MORPHISMS( f );
    
    func := function( h )
              local s, r, b, record;
              
              s := Position( ind, Source( h ) );
              
              if s = fail then
                
                s := -1;
                
              else
                
                s := s - 1;
                
              fi;
              
              r := Position( ind, Range( h ) );
              
              if r = fail then
                
                r := -1;
                
              else
                
                r := r - 1;
                
              fi;
              
              if s <> -1 and r <> -1 then
                
                b := BasisBetweenTwistedCotangentSheavesAsQuiverRepresentations( A, s, r );
                
              else
                
                b := [ ];
                
              fi;
              
              record := rec( );
              
              record!.indices := [ s, r ];
              
              record!.coefficients := COEFFICIENTS_OF_LINEAR_MORPHISM( b, h );
              
              return record;
            
              end;
    
    
    return List( morphisms, a -> List( a, b -> func( b ) ) );
    
end );

##
InstallMethod( MORPHISM_OF_PROJECTIVE_QUIVER_REPS_AS_LIST_OF_MORPHISMS,
    [ IsQuiverRepresentationHomomorphism ],
function( phi )
  local cat, source, range, list_of_sources, list_of_ranges, s, r, L;

  cat := CapCategory( phi );
  
  source := Source( phi );
  
  range := Range( phi );
  
  list_of_sources := DECOMPOSITION_OF_PROJECTIVE_QUIVER_REPRESENTATION( source );
  
  list_of_ranges := DECOMPOSITION_OF_PROJECTIVE_QUIVER_REPRESENTATION( range );
    
  if list_of_sources = [  ] then
      
    list_of_sources := [ ZeroObject( cat ) ];
        
  fi;
   
  if list_of_ranges = [  ] then
      
    list_of_ranges := [ ZeroObject( cat ) ];
        
  fi;
  
  s := Length( list_of_sources );
  
  r := Length( list_of_ranges );
  
  L := List( [ 1 .. s ],
        u -> List( [ 1 .. r ], v -> PreCompose(
                [
                    InjectionOfCofactorOfDirectSum( list_of_sources, u ),
                    phi,
                    ProjectionInFactorOfDirectSum( list_of_ranges, v )
                ]
            ) ) );
    
  return L;

end );


