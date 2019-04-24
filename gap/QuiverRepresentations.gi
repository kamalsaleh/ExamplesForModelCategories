

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

InstallGlobalFunction( GENERATORS_OF_EXTERNAL_HOM_IN_QUIVER_REPS,
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

InstallGlobalFunction( COMPUTE_LIFT_IN_QUIVER_REPS,
    function( f, g )
    local homs_basis, Q, k, V, homs_basis_composed_with_g, L, vector, mat, sol, lift, h;

    if IsZeroForObjects( Range( f ) ) then
        return ZeroMorphism( Source( f ), Source( g ) );
    fi;

    homs_basis := GENERATORS_OF_EXTERNAL_HOM_IN_QUIVER_REPS( Source( f ), Source( g ) );
    # if homs_basis = [] then there is only the zero morphism between source(f) and source(g)
    # Thus f must be zero in order for lift to exist.
    if homs_basis = [ ] then
      if IsZeroForMorphisms( f ) then
        return ZeroMorphism( Source( f ), Source( g ) );
      else
        return fail;
      fi;
    fi;
    Q := QuiverOfRepresentation( Source( f ) );
    k := LeftActingDomain( AlgebraOfRepresentation( Source( f ) ) );
    V := Vertices( Q );
    homs_basis_composed_with_g := List( homs_basis, m -> PreCompose( m, g ) );
    L := List( V, v -> Concatenation( [ RightMatrixOfLinearTransformation( MapForVertex( f, v ) ) ],
                                        List( homs_basis_composed_with_g, h -> RightMatrixOfLinearTransformation( MapForVertex( h, v ) ) ) ) );
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
    for h in homs_basis do
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
    local homs_basis, Q, k, V, homs_basis_composed_with_f, L, vector, mat, sol, colift, h;

    homs_basis := GENERATORS_OF_EXTERNAL_HOM_IN_QUIVER_REPS( Range( f ), Range( g ) );
    # if homs_basis = [] then there is only the zero morphism between range(f) and range(g)
    # Thus g must be zero in order for colift to exist.
    if homs_basis = [ ] then
      if IsZeroForMorphisms( g ) then
	    return ZeroMorphism( Range( f ), Range( g ) );
      else
	    return fail;
      fi;
    fi;
    Q := QuiverOfRepresentation( Source( f ) );
    k := LeftActingDomain( AlgebraOfRepresentation( Source( f ) ) );
    V := Vertices( Q );
    homs_basis_composed_with_f := List( homs_basis, m -> PreCompose( f, m ) );
    L := List( V, v -> Concatenation( [ RightMatrixOfLinearTransformation( MapForVertex( g, v ) ) ],
                                        List( homs_basis_composed_with_f, h -> RightMatrixOfLinearTransformation( MapForVertex( h, v ) ) ) ) );
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
    for h in homs_basis do
        if not IsZero( sol[ 1 ] ) then
            colift := colift + sol[ 1 ]*h;
        fi;
    Remove( sol, 1 );
    od;

    fi;
    return colift;
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
  function( omega_1, omega_2 )
    local A1, A2, A1_A2, matrices_1, matrices_2, identity_matrices_1, identity_matrices_2, L1, L2, U, D;
    
    A1 := AlgebraOfRepresentation( omega_1 );
    
    A2 := AlgebraOfRepresentation( omega_2 );
    
    A1_A2 := TensorProductOfAlgebras( A1, A2 );
    
    matrices_1 := MatricesOfRepresentation( omega_1 );
    
    matrices_2 := MatricesOfRepresentation( omega_2 );
    
    identity_matrices_1 := List( DimensionVector( omega_1 ), d -> IdentityMatrix( Rationals, d ) );
    
    identity_matrices_2 := List( DimensionVector( omega_2 ), d -> IdentityMatrix( Rationals, d ) );
    
    L1 := ListX( identity_matrices_1, matrices_2, KroneckerProduct );
    
    L2 := ListX( matrices_1, identity_matrices_2, KroneckerProduct );
    
    U := Concatenation( L1, L2 );
    
    D := ListX( DimensionVector( omega_1 ), DimensionVector( omega_2 ), \* );
    
    return QuiverRepresentation( A1_A2, D, U );
  
end );

InstallGlobalFunction( PRODUCT_OF_QUIVER_REPRESENTATION_HOMOMORPHISMS,
  function( phi_1, phi_2 )
    local matrices_1, matrices_2, L, a, b;
    
    matrices_1 := MatricesOfRepresentationHomomorphism( phi_1 );
    
    matrices_2 := MatricesOfRepresentationHomomorphism( phi_2 );
    
    L := ListX( matrices_1, matrices_2, KroneckerProduct );
    
    a := PRODUCT_OF_QUIVER_REPRESENTATIONS( Source( phi_1 ), Source( phi_2 ) );
    
    b := PRODUCT_OF_QUIVER_REPRESENTATIONS( Range( phi_1 ), Range( phi_2 ) );
    
    return QuiverRepresentationHomomorphism( a, b, L );
    
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

InstallGlobalFunction( GENERATORS_OF_EXTERNAL_HOM_IN_CHAINS_OF_QUIVER_REPS,
    function( C1, C2 )
    local m, n, A, R1, R2, B;

    m := Minimum( ActiveLowerBound( C1 ), ActiveLowerBound( C2 ) ) + 1;
    n := Maximum( ActiveUpperBound( C1 ), ActiveUpperBound( C2 ) ) - 1;
    if IsChainComplex( C1 ) then
        A := PRODUCT_OF_QUIVER_ALGEBRAS( AlgebraOfRepresentation( C1[m] ), n, m );
    else
        A := PRODUCT_OF_QUIVER_ALGEBRAS( AlgebraOfRepresentation( C1[m] ), m, n );
    fi;
    R1 := CONVERT_COMPLEX_OF_QUIVER_REPS_TO_QUIVER_REP( C1, A );
    R2 := CONVERT_COMPLEX_OF_QUIVER_REPS_TO_QUIVER_REP( C2, A );
    B := GENERATORS_OF_EXTERNAL_HOM_IN_QUIVER_REPS( R1, R2 );
    return List( B, mor -> CONVERT_QUIVER_REP_MORPHISM_TO_COMPLEX_MORPHISM_OF_QUIVER_REPS( C1, C2, mor, A ) );
end );

InstallGlobalFunction( "COMPUTE_LIFTS_IN_COMPLEXES_OF_QUIVER_REPS",
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

InstallGlobalFunction( "COMPUTE_COLIFTS_IN_COMPLEXES_OF_QUIVER_REPS",
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
