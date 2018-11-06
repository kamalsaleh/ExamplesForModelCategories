
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
    function( S, i )
    return GradedFreeLeftPresentation( 1, S, [ -i ] );
end );

InstallMethod( TwistedCotangentSheafOp,
    [ IsHomalgGradedRing, IsInt ],
    function( S, i )
    return ApplyFunctor( TwistFunctor(S,i), KoszulSyzygyModule( S, i ) );
end );

##
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

##
InstallMethodWithCache( BasisBetweenTwistedCotangentSheaves, 
        "this should return the basis of Hom( omega^i(i),omega^j(j) )",
        [ IsHomalgGradedRing, IsInt, IsInt ],
    function( S, i, j )
    local G, n, index, combinations, L;
    if i<j then
        return [];
    fi;

    if i = j then
        return [ IdentityMorphism( KoszulSyzygyModule( S, i)[i] ) ];
    fi;

    G := LIST_OF_MORPHISMS_BETWEEN_TWISTED_COTANGENT_BUNDLES( S );
    
    n := Length( IndeterminatesOfPolynomialRing( S ) );

    index := n - i;
    combinations := Combinations( [ 1 .. n ], i - j );
    combinations := List( combinations, comb -> Reversed( comb ) );

    L := List( combinations, comb -> List( [ 1 .. i - j ], k-> G[index+k-1][comb[k]] ) );
    return List( L, l -> PreCompose(l) );
end );

##
InstallMethodWithCrispCache( BasisBetweenTwistedStructureSheavesAsQuiverRepresentations, 
    [ IsQuiverAlgebra, IsInt, IsInt, IsInt ],
    function( A, i, u, v )
    local n, projectives, twists_of_projectives, u_index, v_index, hom, current_L, current_K, p, \
    L, d, indices, S, current_mor, cokernel_proj, previous_hom, summands, current_hom, t, index; 
    
    Print( "Computing Basis for: ", i,",", u,",", v, "\n" );
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
        return List( GeneratorsOfExternalHom( projectives[ 2 ], projectives[ 1 ] ), g -> StalkChainMorphism(g,0) );
    fi;

    if u > v then
        return [ ];
    fi;

    if ForAll( [ u, v ], j -> j in twists_of_projectives ) then
        if u = v then
            return [ StalkChainMorphism( IdentityMorphism( projectives[ Position( twists_of_projectives, u ) ] ), 0 ) ];
        fi;
        if v - u = 1 then
            u_index := Position( twists_of_projectives, u );
            v_index := Position( twists_of_projectives, v );
            current_hom := GeneratorsOfExternalHom( projectives[ u_index ], projectives[ v_index ] );
            current_hom := List( current_hom, c -> StalkChainMorphism(c,0) );
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
        indices := Combinations( [ 1 .. n + d - 1 ], d );
        indices := List( indices, index -> index - [ 0 .. d ] );

        return List( indices, index -> 
        PreCompose( List( [ 1 .. d ], k -> L[k][index[k]]) ) );        
    fi;

    if v > i then
        S := UnderlyingHomalgGradedPolynomialRing( A );
        current_mor := PositiveKoszulChainMorphism( S, v );
        current_mor := Source( current_mor )^1;
        L := MORPHISM_OF_TWISTED_STRUCTURE_SHEAVES_AS_LIST_OF_RECORDS( current_mor );
        L := List( L, l -> List( l, r -> RECORD_TO_MORPHISM_OF_TWISTED_STRUCTURE_SHEAVES_AS_QUIVER_REPS(A,-1,r) ) );
        current_mor := MorphismBetweenDirectSums( L );
        cokernel_proj := CokernelProjection( current_mor );
        if u = v then
            return [ IdentityMorphism( Range( cokernel_proj ) ) ];
        fi;
        if v = u + 1 then
            previous_hom := BasisBetweenTwistedStructureSheavesAsQuiverRepresentations( A, i, u-1, v-1 );
            summands := List( [ 1 .. n ], k -> Range( previous_hom[ 1 ] ) );
            return List( [ 1 .. n ], k -> PreCompose( InjectionOfCofactorOfDirectSum( summands, k ), cokernel_proj ) );
        fi;

        L := List( [ u .. v - 1 ], j -> BasisBetweenTwistedStructureSheavesAsQuiverRepresentations( A, i, j, j + 1 ) );
        d := v - u;

        indices := Combinations( [ 1 .. n + d - 1 ], d );
        indices := List( indices, index -> index - [ 0 .. d ] );

        return List( indices, index -> 
        PreCompose( List( [ 1 .. d ], k -> L[k][index[k]]) ) );
    fi;

    if u < i - n then

        if v - u = 1 then
            Error( "?" );
        fi;

    fi;

    Error( "??" );
end );

DeclareOperation( "BasisBetweenTwistedCotangentSheavesAsQuiverRepresentations", [ IsQuiverAlgebra, IsInt, IsInt ] );
InstallMethodWithCache( BasisBetweenTwistedCotangentSheavesAsQuiverRepresentations, 
        "this should return the basis of Hom( p_i, p_j )",
        [ IsQuiverAlgebra, IsInt, IsInt ],
    function( A, i, j )
    local G, n, index, combinations, L, projectives, cat;
    if i<j then
        return [ ];
    fi;
    
    projectives := Reversed( IndecProjRepresentations( A ) );
    cat := CapCategory( projectives[ 1 ] );

    n := Length( projectives );

    if i = infinity and j = infinity then
        return ZeroObjectFunctorial( cat );
    elif i = infinity then
        return ZeroMorphism( ZeroObject( cat ), projectives[ n - j ] );
    elif j = infinity then
        return ZeroMorphism( projectives[ n - i ], ZeroObject( cat ) );
    fi;

    if i = j then
        return [ IdentityMorphism( projectives[ n - i ] ) ];
    fi;

    G := LIST_OF_MORPHISMS_BETWEEN_TWISTED_COTANGENT_BUNDLES_AS_QUIVER_REPS( A );
    
    index := n - i;

    combinations := Combinations( [ 1 .. n ], i - j );
    combinations := List( combinations, comb -> Reversed( comb ) );
    L := List( combinations, comb -> List( [ 1 .. i - j ], k-> G[index+k-1][comb[k]] ) );
    return List( L, l -> PreCompose(l) );
end );

InstallMethod( TwistedStructureSheafAsQuiverRepresentation, 
    [ IsQuiverAlgebra, IsInt, IsInt ],
    function( A, i, u )
    return Source( BasisBetweenTwistedStructureSheavesAsQuiverRepresentations( A, i, u, u )[ 1 ] );
end );


##
InstallMethod( LIST_OF_MORPHISMS_BETWEEN_TWISTED_COTANGENT_BUNDLES, [ IsHomalgGradedRing ],
function( S )
local omegas, morphisms, n, k, l, j, current;
n := Length( IndeterminatesOfPolynomialRing( S ) );

omegas := List( [ 0 .. n-1 ], i -> TwistedCotangentSheaf( S, i ) );

morphisms := Reversed( List( [ 1 .. n -1 ], i -> GeneratorsOfExternalHom( omegas[i+1], omegas[i]) ) );

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

BindGlobal( "ALLOWED_INDICES_FOR_STRUCTURE_BEILINSON_ALGEBRA",
    function( A, i )
    local n,j;
    n := NumberOfVertices( QuiverOfAlgebra( A ) );
    for j in [ 1 .. n ] do
    	if j <> n then
    		if j = 1 then 
    	    	Print( "O(", i, ") <--", String( n ), "-- " );
    		else
    	    	Print( "O(", i-j+1, ") <--", String( n ), "-- " );
    		fi;
    	else
    	    Print( "O(", i-j+1, ")\n" );
    	fi;
    od;
end );

BindGlobal( "ALLOWED_INDICES_FOR_COTANGENT_BEILINSON_ALGEBRA",
    function( A )
    local n, s, i;
    n := NumberOfVertices( QuiverOfAlgebra( A ) ) - 1;
    s := "";
    for i in [ 0 .. n ] do
        if i <> n then
            s := Concatenation(s, "𝛀 ^", String(i), "(", String(i), ") <--",String( n + 1 ),"-- " );
        else
            s := Concatenation( s, "𝛀 ^", String(i), "(", String(i), ")" );
        fi;
    od;
    Print( s, "\n" );
end );

# 𝛀