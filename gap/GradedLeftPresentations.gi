
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