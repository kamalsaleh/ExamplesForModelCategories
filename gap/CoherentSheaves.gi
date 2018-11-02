
BindGlobal( "is_finite_dimensional_graded_left_presentation",
    function( N )
    local hN;
    hN := LeftPresentationWithDegrees( UnderlyingMatrix( N ), GeneratorDegrees( N ) );
    return IsZero( HilbertPolynomial( hN ) );
end );

InstallMethod( CoherentSheavesOverProjectiveSpace, 
        [ IsHomalgGradedRing ],
    function( S )
    local graded_lp_cat_sym, sub_cat;
    graded_lp_cat_sym := GradedLeftPresentations( S );
    sub_cat := FullSubcategoryByMembershipFunction( graded_lp_cat_sym, is_finite_dimensional_graded_left_presentation );
    return graded_lp_cat_sym / sub_cat;
end );

InstallMethod( TwistedStructureSheafOp,
    [ IsHomalgGradedRing, IsInt ],
    function( S, i)
    return GradedFreeLeftPresentation( 1, S, [ -i ] );
end );


InstallMethodWithCache( BasisBetweenTwistedStructureSheaves,
    [ IsHomalgGradedRing, IsInt, IsInt ],
    function( S, u, v )
    local n, L, l, o_u, o_v, indeterminates;

    n := Length( IndeterminatesOfPolynomialRing( S ) );
    if u > v then
        return [ ];
    elif u = v then
        return [ IdentityMorphism( TwistedStructureSheaf( S, u ) ) ];
    else
        o_u := GradedFreeLeftPresentation( 1, S, [ -u ] );
        o_v := GradedFreeLeftPresentation( 1, S, [ -v ] );

        L := Combinations( [ 1 .. n+v-u-1 ], v-u );
        L := List( L, l -> l - [ 0 .. v-u - 1 ] );
        indeterminates := IndeterminatesOfPolynomialRing( S );
        L := List( L, indices -> Product( List( indices, index -> indeterminates[index] ) ) );
        L := List( L, l -> HomalgMatrix( [[l]], 1, 1, S ) );
        return List( L, mat -> GradedPresentationMorphism( o_u, mat, o_v ) );
    fi;
end );

InstallMethodWithCache( BasisBetweenTwistedStructureSheavesAsQuiverRepresentations, 
    [ IsQuiverAlgebra, IsInt, IsInt, IsInt ],
    function( A, i, u, v )
    local n, projectives, twists_of_projectives, u_index, v_index, current_hom, current_K,
    current_L, hom, p, t, index, indices, hom_u_u_plus_1, hom_u_plus_1_v, k, d, L;
    
    if i <> -1 then
        return BasisBetweenTwistedStructureSheavesAsQuiverRepresentations( A, -1, u-i-1, v-i-1 );
    fi;

    n := NumberOfVertices( QuiverOfAlgebra( A ) );
    projectives := ShallowCopy( IndecProjRepresentations( A ) );
    twists_of_projectives := Reversed( [ i - n + 1 .. i ] );
    Sort( projectives, function(a,b) 
                        return DimensionVector(a)[n]>DimensionVector(b)[n]; 
                        end );
    if u = i-1 and v = i then
        return GeneratorsOfExternalHom( projectives[ 2 ], projectives[ 1 ] );
    fi;

    if u > v then
        return [ ];
    fi;

    if ForAll( [ u, v ], j -> j in twists_of_projectives ) then
        if u = v then
            return [ IdentityMorphism( projectives[ Position( twists_of_projectives, u ) ] ) ];
        fi;
        
        if v - u = 1 then
            u_index := Position( twists_of_projectives, u );
            v_index := Position( twists_of_projectives, v );
            
            current_hom := GeneratorsOfExternalHom( projectives[ u_index ], projectives[ v_index ] );
            hom := [ current_hom[ 1 ] ];
            for t in [ 2 .. n ] do
                current_L := BasisBetweenTwistedStructureSheavesAsQuiverRepresentations( A, i, u + 1, v + 1 );
                current_K := List( current_L, l -> PreCompose( hom[1], l ) );
                p := Position( current_K, PreCompose( current_hom[t], current_L[1] ) );
                if p = fail then
                    Error( "This should not happen!" );
                fi;
                hom[p] := current_hom[t];
            od;
            return hom;
        fi;

        L := List( [ u .. v - 1 ], j -> BasisBetweenTwistedStructureSheavesAsQuiverRepresentations( A, i, j, j + 1 ) );
        d := v - u;
        indices := Cartesian( List( [ 1 .. d ], k -> [ 1 .. n ] ) );
        for index in indices do
            Sort( index );
        od;
        indices := Set( indices );
        return List( indices, index -> 
        PreCompose( List( [ 1 .. d ], k -> L[k][index[k]]) ) );
    fi;
    Error( "??" );
end );
