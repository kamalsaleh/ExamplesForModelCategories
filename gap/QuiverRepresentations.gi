

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

InstallMethod( GeneratorsOfExternalHom,
        [ IsQuiverRepresentation, IsQuiverRepresentation ],
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
        source_of_arrow := VertexNumber( Source( Arrow( Q, i ) ) );
        range_of_arrow := VertexNumber( Target( Arrow( Q, i ) ) );
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