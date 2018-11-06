
##
# InstallMethod( TwistFunctorOp, 
#             [ IsHomalgGradedRing, IsInt ],
#     function( S, n )
#     local cat, F;
#     cat := GradedLeftPresentations( S );
#     F := CapFunctor( Concatenation( String( n ), "-twist endofunctor in ", Name( cat ) ), cat, cat );
#     AddObjectFunction( F,
#         function( M )
#             return AsGradedLeftPresentation( UnderlyingMatrix( M ), List( GeneratorDegrees( M ), d -> d - n ) );
#         end );
#     AddMorphismFunction( F,
#         function( source, f, range )
#             return GradedPresentationMorphism( source, UnderlyingMatrix( f ), range );
#         end );    
#     return F;
# end );
    
##
InstallMethod( PositiveKoszulChainMorphismOp, 
    [ IsHomalgGradedRing, IsInt ],
    function( S, i )
    local indeterminates, n, k, C, source, range, F;
    
    if i = 0 then
        indeterminates := Indeterminates( S );
        n := Length( indeterminates );
        k := AsGradedLeftPresentation( HomalgMatrix( indeterminates, n, 1, S ), [ 0 ] );
        C := ProjectiveResolution( StalkChainComplex( k, 0 ) );
        source := ChainComplex( List( [ 2 .. n ], i-> C^i ), 1 );
        range := StalkChainComplex( C[0], 0 );
        return ChainMorphism( source, range, [ C^1 ], 0 );
    else
        F := ExtendFunctorToChainComplexCategoryFunctor( TwistFunctor( S, i ) );
        return ApplyFunctor( F, PositiveKoszulChainMorphism( S, 0 ) );
    fi;
end );

##
InstallMethod( NegativeKoszulChainMorphismOp, 
    [ IsHomalgGradedRing, IsInt ],
    function( S, i )
    local indeterminates, n, k, C, source, range, F, phi;
    
    if i = 0 then
        indeterminates := Indeterminates( S );
        n := Length( indeterminates );
        k := AsGradedLeftPresentation( HomalgMatrix( indeterminates, n, 1, S ), [ 0 ] );
        C := ProjectiveResolution( StalkChainComplex( k, 0 ) );
        source := StalkChainComplex( C[ n ], 0 );
        range := ChainComplex( List( [ 1 .. n - 1 ], i-> C^i ), -n + 2 );
        phi := ChainMorphism( source, range, [ C^n ], 0 );
        F := ExtendFunctorToChainComplexCategoryFunctor( TwistFunctor( S, n ) );
        return ApplyFunctor( F, phi );
    else
        F := ExtendFunctorToChainComplexCategoryFunctor( TwistFunctor( S, i ) );
        return ApplyFunctor( F, NegativeKoszulChainMorphism( S, 0 ) );
    fi;
end );

InstallMethod( MORPHISM_OF_TWISTED_STRUCTURE_SHEAVES_AS_LIST_OF_RECORDS, 
    [ IsGradedLeftPresentationMorphism ],
function( phi )
local source, range, S, n, zero_obj, L, s, r, mat, vec, degrees_source, degrees_range, 
list_of_ranges, list_of_sources, degree_of_source, degree_of_range;

source := Source( phi );
range := Range( phi );

S := UnderlyingHomalgRing( phi );
n := Length( IndeterminatesOfPolynomialRing( S ) );

degrees_source := GeneratorDegrees( source );
s := Length( degrees_source );

degrees_range := GeneratorDegrees( range );
r := Length( degrees_range );

if s > 1 or r > 1 then
    list_of_sources := List( degrees_source, d -> GradedFreeLeftPresentation( 1, S, [ d ] ) );
    list_of_ranges := List( degrees_range, d -> GradedFreeLeftPresentation( 1, S, [ d ] ) );
    L := List( [ 1 .. s ], u -> 
            List( [ 1 .. r ], v -> PreCompose(
                [
                    InjectionOfCofactorOfDirectSum( list_of_sources, u ),
                    phi,
                    ProjectionInFactorOfDirectSum( list_of_ranges, v )
                ]
            )));
        return List( L, l -> List( l, m -> MORPHISM_OF_TWISTED_STRUCTURE_SHEAVES_AS_LIST_OF_RECORDS(m)[1][1] ) );
fi;

if s=0 then
    degree_of_source := -infinity;
else
    degree_of_source := Int( String( degrees_source[ 1 ] ) );
fi;

if r=0 then
    degree_of_range := -infinity;
else
    degree_of_range := Int( String( degrees_range[ 1 ] ) );
fi;

if degree_of_source < degree_of_range or IsZeroForMorphisms( phi ) then
    return [ [ rec( indices := [-degree_of_source, -degree_of_range ], coefficients := [] ) ] ];
fi;

mat := BasisBetweenTwistedStructureSheaves( S, -degree_of_source, -degree_of_range );
mat := List( mat, UnderlyingMatrix );
mat := UnionOfRows( mat );
vec := UnderlyingMatrix( phi );
return [ [ rec( indices := [-degree_of_source, -degree_of_range], coefficients := EntriesOfHomalgMatrix( RightDivide( vec, mat ) ) ) ] ];
end );

InstallMethodWithCache( RECORD_TO_MORPHISM_OF_TWISTED_STRUCTURE_SHEAVES_AS_QUIVER_REPS, 
        [ IsQuiverAlgebra, IsInt, IsRecord ],
    function( A, i, record )
    local cat, projectives, coefficients, u, v, source, range;

    cat := CategoryOfQuiverRepresentations( A );
    
    u := record!.indices[ 1 ];
    v := record!.indices[ 2 ];

    if u = infinity and v = infinity then
        return ZeroMorphism( ZeroObject( cat ), ZeroObject( cat ) );
    elif u = infinity then
        return UniversalMorphismFromZeroObject( TwistedStructureSheafAsQuiverRepresentation( A, i, u ) );
    elif  v = infinity then
        return UniversalMorphismIntoZeroObject( TwistedStructureSheafAsQuiverRepresentation( A, i, v ) );
    fi;

    if record!.coefficients = [] then
        source := TwistedStructureSheafAsQuiverRepresentation( A, i, u );
        range := TwistedStructureSheafAsQuiverRepresentation( A, i, v );
        return ZeroMorphism( source, range );
    else
        coefficients := List( record!.coefficients, c -> Rat( String( c ) ) );
        return coefficients*BasisBetweenTwistedStructureSheavesAsQuiverRepresentations( A, i, u, v );
    fi;

end );

InstallMethodWithCache( LIST_OF_RECORDS_TO_MORPHISM_OF_TWISTED_STRUCTURE_SHEAVES_AS_QUIVER_REPS,
        [ IsQuiverAlgebra, IsInt, IsList ],
    function( A, i, L )
    return MorphismBetweenDirectSums(
        List( L, l -> List( l, m -> RECORD_TO_MORPHISM_OF_TWISTED_STRUCTURE_SHEAVES_AS_QUIVER_REPS( A, i, m ) ) ) );
end );

InstallMethodWithCache( GENERATORS_OF_EXTERNAL_HOM_IN_CHAINS_OF_GRADED_LEFT_PRESENTATIONS, 
        [ IsBoundedChainComplex, IsBoundedChainComplex ],
    function( C, D )
    local H, kernel_mor_of_H, kernel_obj_of_H, morphisms_C_to_D, 
	morphisms_from_R_to_kernel, morphisms_from_T_to_H, T, U, cat, 
    chains_graded_lp_cat_sym;
    chains_graded_lp_cat_sym := CapCategory( C );
    cat := UnderlyingCategory( chains_graded_lp_cat_sym );
    U := TensorUnit( cat );
    H := InternalHomOnObjects( C, D );
    kernel_mor_of_H := CyclesAt( H, 0 );
    kernel_obj_of_H := Source( kernel_mor_of_H );
    morphisms_from_R_to_kernel := GetGenerators( Hom( AsPresentationInHomalg( U ), AsPresentationInHomalg( kernel_obj_of_H ) ) );
    morphisms_from_R_to_kernel := List( morphisms_from_R_to_kernel, AsPresentationMorphismInCAP );
    T := TensorUnit( chains_graded_lp_cat_sym );
    morphisms_from_T_to_H := List( morphisms_from_R_to_kernel, m -> ChainMorphism( T, H, [ PreCompose( m, kernel_mor_of_H) ], 0 ) );
    return List( morphisms_from_T_to_H, m-> InternalHomToTensorProductAdjunctionMap( C, D, m ) );
end );

InstallMethod( MORPHISM_INTO_CANONICAL_TWISTED_COTANGENT_SHEAF,
    [ IsGradedLeftPresentation ],
    function( some_omega )
    local mat, S, n, L, index, G;

    mat := UnderlyingMatrix( some_omega );
    S := UnderlyingHomalgRing( some_omega );
    n := Length( IndeterminatesOfPolynomialRing( S ) );

    if NrColumns( mat ) = 1 and NrRows( mat ) = n then
        SetMORPHISM_FROM_CANONICAL_TWISTED_COTANGENT_SHEAF( some_omega, UniversalMorphismFromZeroObject( some_omega ) );
        return UniversalMorphismIntoZeroObject( some_omega );
    fi;
    
    if NrRows( mat ) = 0 then
        SetMORPHISM_FROM_CANONICAL_TWISTED_COTANGENT_SHEAF( some_omega, IdentityMorphism( some_omega ) );
        return IdentityMorphism( some_omega );
    fi;
    
    L := List( [ 0 .. n - 1 ], i-> [ Binomial( n, i-1 ), Binomial( n, i ) ] );
    index := n - Position( L, [ NrRows(mat), NrColumns(mat) ] );
    
    if IsEqualForObjects( some_omega, TwistedCotangentSheaf( S, index ) ) then
        G := [ IdentityMorphism( some_omega ) ];
    else
        G := GeneratorsOfExternalHom( some_omega, TwistedCotangentSheaf( S, index ) );
    fi;

    if Length( G ) <> 1 then
        Error( "unexpected thing happend" );
    fi;

    SetMORPHISM_FROM_CANONICAL_TWISTED_COTANGENT_SHEAF( some_omega, Inverse( G[1] ) );
    return G[1];
end );


InstallMethod( CANONICALIZE_SOME_TWISTED_COTANGENT_SHEAF, [ IsGradedLeftPresentation ],
function( some_omega )
local mat, S, n, L, index, K;

mat := UnderlyingMatrix( some_omega );
S := UnderlyingHomalgRing( some_omega );
n := Length( IndeterminatesOfPolynomialRing( S ) );
if NrColumns( mat ) = 1 and NrRows( mat ) = n then
    ZeroObject( CapCategory( some_omega ) )!.index := -1;
    return ZeroObject( CapCategory( some_omega ) );
fi;
if NrRows( mat ) = 0 then
    some_omega!.index := n - 1;
    return some_omega;
fi;

L := List( [ 0 .. n - 1 ], i-> [ Binomial( n, i-1 ), Binomial( n, i ) ] );
index := n - Position( L, [ NrRows(mat), NrColumns(mat) ] );
K := TwistedCotangentSheaf( S, index );
K!.index := index;
return K;
end );

InstallMethod( CANONICALIZE_SOME_TWISTED_COTANGENT_SHEAVES_MORPHISM, [ IsGradedLeftPresentationMorphism ],
function( phi )
# this is important in order to set needed attributes for source( phi ).

MORPHISM_INTO_CANONICAL_TWISTED_COTANGENT_SHEAF( Source( phi ) );
return PreCompose( [ 
    MORPHISM_FROM_CANONICAL_TWISTED_COTANGENT_SHEAF( Source( phi ) ),
    phi,
    MORPHISM_INTO_CANONICAL_TWISTED_COTANGENT_SHEAF( Range( phi ) )
] );
end );

DeclareAttribute( "DECOMPOSE_DIRECT_SUM_OF_NON_CANONICAL_TWISTED_COTANGENT_SHEAVES", IsGradedLeftPresentation );
InstallMethod( DECOMPOSE_DIRECT_SUM_OF_NON_CANONICAL_TWISTED_COTANGENT_SHEAVES, [ IsGradedLeftPresentation ],
function( M )
local mat, S, n, L, non_zeros, length_non_zeros, degrees, current_degrees, current_mat, p, omega, N, irrelevant_module;

S := UnderlyingHomalgRing( M );
n := Length( IndeterminatesOfPolynomialRing( S ) );
L := List( [ 0 .. n - 1 ], i-> [ Binomial( n, i-1 ), Binomial( n, i ) ] );
mat := UnderlyingMatrix( M );

if NrRows(mat) = 0 and NrColumns(mat) <> 0 then
    return List( [ 1 .. NrColumns(mat) ], i -> GradedFreeLeftPresentation(1,S,[ GeneratorDegrees(M)[i] ] ) );
fi;

if NrRows(mat) = 0 and NrColumns(mat) = 0 then
    return [ ZeroObject( M ) ];
fi;

non_zeros := Filtered( EntriesOfHomalgMatrix( CertainColumns( mat, [1] ) ), e -> IsZero(e)<> true );
length_non_zeros := Length( non_zeros );

if length_non_zeros = n then
    non_zeros := HomalgMatrix( non_zeros, n, 1, S );
    irrelevant_module := AsGradedLeftPresentation( non_zeros, GeneratorDegrees(M){[1]} );

    degrees := GeneratorDegrees(M){[2..NrColumns(mat)]};
    mat := CertainColumns( CertainRows( mat, [ n + 1 .. NrRows( mat ) ] ), [ 2 .. NrColumns( mat ) ] );
    N := AsGradedLeftPresentation( mat, degrees );
    return Concatenation( [ irrelevant_module ], DECOMPOSE_DIRECT_SUM_OF_NON_CANONICAL_TWISTED_COTANGENT_SHEAVES( N ) );
else
    p := length_non_zeros + 1;
    current_degrees := GeneratorDegrees(M){[ 1 .. L[p][2] ] };
    current_mat := CertainColumns( CertainRows( mat, [ 1 .. L[p][1] ] ), [ 1 .. L[p][2] ] );
    omega := AsGradedLeftPresentation( current_mat, current_degrees );
    current_degrees := GeneratorDegrees(M){[ L[p][2]+1 .. NrColumns(mat) ] };
    current_mat := CertainColumns( CertainRows( mat, [ L[p][1]+1 .. NrRows( mat ) ] ), [ L[p][2]+1 .. NrColumns( mat ) ] );
    N := AsGradedLeftPresentation( current_mat, current_degrees );
    return Concatenation( [ omega ], DECOMPOSE_DIRECT_SUM_OF_NON_CANONICAL_TWISTED_COTANGENT_SHEAVES( N ) );
fi;

end );

DeclareAttribute( "DECOMPOSE_MORPHISM_OF_DIRECT_SUM_OF_NON_CANONICAL_TWISTED_COTANGENT_SHEAVES", IsGradedLeftPresentationMorphism );

InstallMethod( DECOMPOSE_MORPHISM_OF_DIRECT_SUM_OF_NON_CANONICAL_TWISTED_COTANGENT_SHEAVES, [ IsGradedLeftPresentationMorphism ],
    function( phi )
    local direct_summand_of_range, direct_summand_of_source, L;
    direct_summand_of_source := DECOMPOSE_DIRECT_SUM_OF_NON_CANONICAL_TWISTED_COTANGENT_SHEAVES( Source( phi ) );
    direct_summand_of_range := DECOMPOSE_DIRECT_SUM_OF_NON_CANONICAL_TWISTED_COTANGENT_SHEAVES( Range( phi ) );
    L := List( [ 1 .. Length( direct_summand_of_source ) ], 
        i -> List( [ 1 .. Length( direct_summand_of_range ) ],
            j -> PreCompose(
                [
                    InjectionOfCofactorOfDirectSum(direct_summand_of_source, i),
                    phi,
                    ProjectionInFactorOfDirectSum(direct_summand_of_range, j )
                ]
            )));
    return L;
end );


DeclareAttribute( "CANONICALIZE_GRADED_LEFT_PRESENTATION", IsGradedLeftPresentation );
InstallMethod( CANONICALIZE_GRADED_LEFT_PRESENTATION, 
    [ IsGradedLeftPresentation ],
    function( M )
    local L;
    L := DECOMPOSE_DIRECT_SUM_OF_NON_CANONICAL_TWISTED_COTANGENT_SHEAVES( M );
    L := List( L, CANONICALIZE_SOME_TWISTED_COTANGENT_SHEAF );
    if L = [] then
        return ZeroObject( CapCategory( M ) );
    fi;
    return DirectSum( L );
end );

DeclareAttribute( "CANONICALIZE_GRADED_LEFT_PRESENTATION_MORPHISM", IsGradedLeftPresentationMorphism );
InstallMethod( CANONICALIZE_GRADED_LEFT_PRESENTATION_MORPHISM,
    [ IsGradedLeftPresentationMorphism ],
function( phi )
local L, source, range;
source := CANONICALIZE_GRADED_LEFT_PRESENTATION( Source( phi ) );
range := CANONICALIZE_GRADED_LEFT_PRESENTATION( Range( phi ) );

if IsZero( phi ) then 
    return ZeroMorphism( source, range );
fi;

L := DECOMPOSE_MORPHISM_OF_DIRECT_SUM_OF_NON_CANONICAL_TWISTED_COTANGENT_SHEAVES( phi );
L := List( L, l -> List( l, CANONICALIZE_SOME_TWISTED_COTANGENT_SHEAVES_MORPHISM ) );
return MorphismBetweenDirectSums( L );

end );



InstallMethodWithCrispCache( BeilinsonReplacement, 
    [ IsGradedLeftPresentation ],
    function( M )
    local S, n, graded_lp_cat_sym, chains_graded_lp_cat_sym, cochains_graded_lp_cat_sym, cochains_cochains_graded_lp_cat_sym, 
    bicomplexes_of_graded_lp_cat_sym, TT, LL, ChLL, Trunc_leq_m1, ChTrunc_leq_m1, ChCh_to_Bi_sym, Cochain_of_ver_coho_sym, cochain_to_chain_functor,
    L, rep, diffs, C;

    S := UnderlyingHomalgRing( M );
    n := Length( IndeterminatesOfPolynomialRing( S ) );
    
	graded_lp_cat_sym := GradedLeftPresentations( S );
	chains_graded_lp_cat_sym := ChainComplexCategory( graded_lp_cat_sym );
	cochains_graded_lp_cat_sym := CochainComplexCategory( graded_lp_cat_sym );
	cochains_cochains_graded_lp_cat_sym := CochainComplexCategory( cochains_graded_lp_cat_sym );
	bicomplexes_of_graded_lp_cat_sym := AsCategoryOfBicomplexes( cochains_cochains_graded_lp_cat_sym );

	TT := TateFunctor( S );
	LL := LFunctor( S );
	ChLL := ExtendFunctorToCochainComplexCategoryFunctor( LL );
    Trunc_leq_m1 := BrutalTruncationAboveFunctor( cochains_graded_lp_cat_sym, -1 );;
    ChTrunc_leq_m1 := ExtendFunctorToCochainComplexCategoryFunctor( Trunc_leq_m1 );;

	ChCh_to_Bi_sym := ComplexOfComplexesToBicomplexFunctor( 
			cochains_cochains_graded_lp_cat_sym, bicomplexes_of_graded_lp_cat_sym );

	Cochain_of_ver_coho_sym := ComplexOfVerticalCohomologiesFunctorAt( bicomplexes_of_graded_lp_cat_sym, -1 );
    cochain_to_chain_functor := CochainToChainComplexFunctor( cochains_graded_lp_cat_sym, chains_graded_lp_cat_sym );
    L := [ TT, ChLL, ChTrunc_leq_m1, ChCh_to_Bi_sym, Cochain_of_ver_coho_sym, cochain_to_chain_functor ];
    rep := ApplyFunctor( PreCompose( L ), M );
    diffs := Differentials( rep );
    diffs := MapLazy( diffs, d -> CANONICALIZE_GRADED_LEFT_PRESENTATION_MORPHISM(d), 1 );
    C := ChainComplex( graded_lp_cat_sym, diffs );
    SetLowerBound( C, -n );
    SetUpperBound( C, n );
    return C;
end );

InstallMethodWithCrispCache( BeilinsonReplacement, 
    [ IsGradedLeftPresentationMorphism ],
    function( phi )
    local S, n, graded_lp_cat_sym, chains_graded_lp_cat_sym, cochains_graded_lp_cat_sym, cochains_cochains_graded_lp_cat_sym, 
    bicomplexes_of_graded_lp_cat_sym, TT, LL, ChLL, Trunc_leq_m1, ChTrunc_leq_m1, ChCh_to_Bi_sym, Cochain_of_ver_coho_sym, cochain_to_chain_functor,
    L, rep, morphisms, mor, source, range;

    S := UnderlyingHomalgRing( phi );
    n := Length( IndeterminatesOfPolynomialRing( S ) );
    
	graded_lp_cat_sym := GradedLeftPresentations( S );
	chains_graded_lp_cat_sym := ChainComplexCategory( graded_lp_cat_sym );
	cochains_graded_lp_cat_sym := CochainComplexCategory( graded_lp_cat_sym );
	cochains_cochains_graded_lp_cat_sym := CochainComplexCategory( cochains_graded_lp_cat_sym );
	bicomplexes_of_graded_lp_cat_sym := AsCategoryOfBicomplexes( cochains_cochains_graded_lp_cat_sym );

	TT := TateFunctor( S );
	LL := LFunctor( S );
	ChLL := ExtendFunctorToCochainComplexCategoryFunctor( LL );
    Trunc_leq_m1 := BrutalTruncationAboveFunctor( cochains_graded_lp_cat_sym, -1 );;
    ChTrunc_leq_m1 := ExtendFunctorToCochainComplexCategoryFunctor( Trunc_leq_m1 );;

	ChCh_to_Bi_sym := ComplexOfComplexesToBicomplexFunctor( 
			cochains_cochains_graded_lp_cat_sym, bicomplexes_of_graded_lp_cat_sym );

	Cochain_of_ver_coho_sym := ComplexOfVerticalCohomologiesFunctorAt( bicomplexes_of_graded_lp_cat_sym, -1 );
    cochain_to_chain_functor := CochainToChainComplexFunctor( cochains_graded_lp_cat_sym, chains_graded_lp_cat_sym );
    L := [ TT, ChLL, ChTrunc_leq_m1, ChCh_to_Bi_sym, Cochain_of_ver_coho_sym, cochain_to_chain_functor ];
    rep := ApplyFunctor( PreCompose( L ), phi );
    morphisms := Morphisms( rep );
    morphisms := MapLazy( morphisms, d -> CANONICALIZE_GRADED_LEFT_PRESENTATION_MORPHISM(d), 1 );
    source := BeilinsonReplacement( Source( phi ) );
    range := BeilinsonReplacement( Range( phi ) );
    mor := ChainMorphism( source, range, morphisms );
    return mor;
end );

DeclareOperation( "view", [ IsGradedLeftPresentation ] );
InstallMethod( view, [ IsGradedLeftPresentation ],
function( M )
local mat, s, i, degrees;
mat := UnderlyingMatrix( M );
s := "";
if NrRows( mat ) = 0 then
    degrees := GeneratorDegrees( M );
    if degrees = [ ] then
        Print( "0" );
    else
        for i in degrees do 
            s := Concatenation( s, "S(",String(-i),")+" );
        od;
        Remove( s, Length(s) );
        Print( s );
    fi;
else
    View( M );
fi;
end );
