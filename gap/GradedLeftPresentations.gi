
BindGlobal( "EXAMPLES_FOR_MODEL_CATEGORIES",
  rec( QQ := HomalgFieldOfRationals( ), ZZ := HomalgRingOfIntegers( ) ) );

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
    local indeterminates, n, k, C, source, range, F, L, A;

    n := Length( Indeterminates( S ) );
    A := KoszulDualRing( S );
    L := LCochainFunctor( S );
    if i = 0 then
        C := AsChainComplex( ApplyFunctor( L, TwistedOmegaModule( A, 0 ) ) );
        source := ChainComplex( List( [ 2 .. n ], i-> C^i ), 1 );
        range := StalkChainComplex( C[0], 0 );
        return ChainMorphism( source, range, [ C^1 ], 0 );
    else
        F := ExtendFunctorToChainComplexCategories( TwistFunctor( S, i ) );
        return ApplyFunctor( F, PositiveKoszulChainMorphism( S, 0 ) );
    fi;
end );

##
InstallMethod( NegativeKoszulChainMorphismOp, 
    [ IsHomalgGradedRing, IsInt ],
    function( S, i )
    local indeterminates, n, k, C, source, range, F, phi, A, L;
   
    n := Length( Indeterminates( S ) );
    A := KoszulDualRing( S );
    L := LCochainFunctor( S );

    if i = 0 then
        C := AsChainComplex( ApplyFunctor( L, TwistedOmegaModule( A, 0 ) ) );
        source := StalkChainComplex( C[ n ], 0 );
        range := ChainComplex( List( [ 1 .. n - 1 ], i-> C^i ), -n + 2 );
        phi := ChainMorphism( source, range, [ C^n ], 0 );
        F := ExtendFunctorToChainComplexCategories( TwistFunctor( S, n ) );
        return ApplyFunctor( F, phi );
    else
        F := ExtendFunctorToChainComplexCategories( TwistFunctor( S, i ) );
        return ApplyFunctor( F, NegativeKoszulChainMorphism( S, 0 ) );
    fi;
end );

##
InstallMethod( MORPHISM_OF_TWISTED_STRUCTURE_SHEAVES_AS_LIST_OF_MORPHISMS, 
    [ IsGradedLeftPresentationMorphism ],
function( phi )
  local source, range, S, cat, n, degrees_source, s, degrees_range, r, list_of_sources, list_of_ranges, L;

  source := Source( phi );
  
  range := Range( phi );

  S := UnderlyingHomalgRing( phi );
  
  cat := GradedLeftPresentations( S );
  
  n := Length( IndeterminatesOfPolynomialRing( S ) );

  degrees_source := GeneratorDegrees( source );
  
  s := Length( degrees_source );

  degrees_range := GeneratorDegrees( range );
  
  r := Length( degrees_range );

  list_of_sources := List( degrees_source, d -> GradedFreeLeftPresentation( 1, S, [ d ] ) );
    
  if list_of_sources = [  ] then
      
    list_of_sources := [ ZeroObject( cat ) ];
        
  fi;
    
  list_of_ranges := List( degrees_range, d -> GradedFreeLeftPresentation( 1, S, [ d ] ) );
    
  if list_of_ranges = [  ] then
      
    list_of_ranges := [ ZeroObject( cat ) ];
        
  fi;
  
  L := List( [ 1 .. Maximum(1,s) ], u -> 
            List( [ 1 .. Maximum(1,r) ], v -> PreCompose(
                [
                    InjectionOfCofactorOfDirectSum( list_of_sources, u ),
                    phi,
                    ProjectionInFactorOfDirectSum( list_of_ranges, v )
                ]
            ) ) );
    
  return L;

end );

##
InstallMethod( MORPHISM_OF_TWISTED_STRUCTURE_SHEAVES_AS_LIST_OF_RECORDS, 
    [ IsGradedLeftPresentationMorphism ],
function( phi )
local source, range, S, n, zero_obj, L, s, r, mat, vec, degrees_source, degrees_range, 
list_of_ranges, list_of_sources, degree_of_source, degree_of_range, cat;

source := Source( phi );
range := Range( phi );

S := UnderlyingHomalgRing( phi );
cat := GradedLeftPresentations( S );
n := Length( IndeterminatesOfPolynomialRing( S ) );

degrees_source := GeneratorDegrees( source );
s := Length( degrees_source );

degrees_range := GeneratorDegrees( range );
r := Length( degrees_range );

if s > 1 or r > 1 then
    list_of_sources := List( degrees_source, d -> GradedFreeLeftPresentation( 1, S, [ d ] ) );
    if list_of_sources = [  ] then
        list_of_sources := [ ZeroObject( cat ) ];
    fi;
    list_of_ranges := List( degrees_range, d -> GradedFreeLeftPresentation( 1, S, [ d ] ) );
    if list_of_ranges = [  ] then
        list_of_ranges := [ ZeroObject( cat ) ];
    fi;
    L := List( [ 1 .. Maximum(1,s) ], u -> 
            List( [ 1 .. Maximum(1,r) ], v -> PreCompose(
                [
                    InjectionOfCofactorOfDirectSum( list_of_sources, u ),
                    phi,
                    ProjectionInFactorOfDirectSum( list_of_ranges, v )
                ]
            )));
        #Error( "3" );
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
    #Error( "1" );
    return [ [ rec( indices := [-degree_of_source, -degree_of_range ], coefficients := [] ) ] ];
fi;

mat := BasisBetweenTwistedStructureSheaves( S, -degree_of_source, -degree_of_range );
mat := List( mat, UnderlyingMatrix );
mat := UnionOfRows( mat );
vec := UnderlyingMatrix( phi );
    #Error( "2" );
return [ [ rec( indices := [-degree_of_source, -degree_of_range], coefficients := EntriesOfHomalgMatrix( RightDivide( vec, mat ) ) ) ] ];
end );

InstallMethodWithCache( RECORD_TO_MORPHISM_OF_TWISTED_STRUCTURE_SHEAVES_AS_QUIVER_REPS, 
        [ IsQuiverAlgebra, IsInt, IsRecord ],
    function( A, i, record )
    local cat, projectives, coefficients, u, v, source, range, B;

    cat := CategoryOfQuiverRepresentations( A );
    
    u := record!.indices[ 1 ];
    v := record!.indices[ 2 ];

    if u = infinity and v = infinity then
        return ZeroMorphism( ZeroObject( cat ), ZeroObject( cat ) );
    elif u = infinity then
        return UniversalMorphismFromZeroObject( TwistedStructureSheafAsQuiverRepresentation( A, i, v ) );
    elif  v = infinity then
        return UniversalMorphismIntoZeroObject( TwistedStructureSheafAsQuiverRepresentation( A, i, u ) );
    fi;

    if record!.coefficients = [] then
        source := TwistedStructureSheafAsQuiverRepresentation( A, i, u );
        range := TwistedStructureSheafAsQuiverRepresentation( A, i, v );
        return ZeroMorphism( source, range );
    else
        coefficients := List( record!.coefficients, c -> Rat( String( c ) ) );
        B := BasisBetweenTwistedStructureSheavesAsQuiverRepresentations( A, i, u, v );
        return coefficients*B;
    fi;

end );


InstallMethodWithCache( RECORD_TO_MORPHISM_OF_TWISTED_COTANGENT_SHEAVES_AS_QUIVER_REPS,
        [ IsQuiverAlgebra, IsRecord ],
    function( A, record )
    local cat, projectives, coefficients, u, v, source, range;

    cat := CategoryOfQuiverRepresentations( A );
    
    u := record!.indices[ 1 ];
    v := record!.indices[ 2 ];

    if u = -1 and v = -1 then
        return ZeroMorphism( ZeroObject( cat ), ZeroObject( cat ) );
    elif v = -1 then
        return UniversalMorphismIntoZeroObject( TwistedCotangentSheafAsQuiverRepresentation( A, u ) );
    elif  u = -1 then
        return UniversalMorphismFromZeroObject( TwistedCotangentSheafAsQuiverRepresentation( A, v ) );
    fi;

    if record!.coefficients = [] then
        source := TwistedCotangentSheafAsQuiverRepresentation( A, u );
        range :=  TwistedCotangentSheafAsQuiverRepresentation( A, v );
        return ZeroMorphism( source, range );
    else
        coefficients := List( record!.coefficients, c -> Rat( String( c ) ) );
        return coefficients*BasisBetweenTwistedCotangentSheavesAsQuiverRepresentations( A, u, v );
    fi;                     

end );

InstallMethodWithCache( LIST_OF_RECORDS_TO_MORPHISM_OF_TWISTED_STRUCTURE_SHEAVES_AS_QUIVER_REPS,
        [ IsQuiverAlgebra, IsInt, IsList ],
    function( A, i, L )
    return MorphismBetweenDirectSums(
        List( L, l -> List( l, m -> RECORD_TO_MORPHISM_OF_TWISTED_STRUCTURE_SHEAVES_AS_QUIVER_REPS( A, i, m ) ) ) );
end );

InstallMethodWithCache( LIST_OF_RECORDS_TO_MORPHISM_OF_TWISTED_COTANGENT_SHEAVES_AS_QUIVER_REPS,
        [ IsQuiverAlgebra, IsList ],
    function( A, L )
    local mor;
    mor :=  MorphismBetweenDirectSums(
        List( L, l -> List( l, m -> RECORD_TO_MORPHISM_OF_TWISTED_COTANGENT_SHEAVES_AS_QUIVER_REPS( A, m ) ) ) );
    mor!.UNDERLYING_LIST_OF_RECORDS := L;
    return mor;
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

InstallMethod( DECOMPOSE_DIRECT_SUM_OF_NON_CANONICAL_TWISTED_COTANGENT_SHEAVES, [ IsGradedLeftPresentation ],
function( M )
local mat, S, n, L, non_zeros, length_non_zeros, degrees, current_degrees, current_mat, p, omega, N, irrelevant_module, T;

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


InstallMethod( CANONICALIZE_DIRECT_SUM_OF_NON_CANONICAL_COTANGENT_SHEAVES, 
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

InstallMethod( CANONICALIZE_GRADED_LEFT_PRESENTATION_MORPHISM_BETWEEN_DIRECT_SUMS_OF_NON_CANONICAL_COTANGENT_SHEAVES,
    [ IsGradedLeftPresentationMorphism ],
function( phi )
local L, source, range;
source := CANONICALIZE_DIRECT_SUM_OF_NON_CANONICAL_COTANGENT_SHEAVES( Source( phi ) );
range := CANONICALIZE_DIRECT_SUM_OF_NON_CANONICAL_COTANGENT_SHEAVES( Range( phi ) );

if IsZero( phi ) then 
    return ZeroMorphism( source, range );
fi;

L := DECOMPOSE_MORPHISM_OF_DIRECT_SUM_OF_NON_CANONICAL_TWISTED_COTANGENT_SHEAVES( phi );
L := List( L, l -> List( l, CANONICALIZE_SOME_TWISTED_COTANGENT_SHEAVES_MORPHISM ) );
return MorphismBetweenDirectSums( L );

end );

##
InstallMethod( MORPHISM_OF_TWISTED_COTANGENT_SHEAVES_AS_LIST_OF_RECORDS, 
    [ IsGradedLeftPresentationMorphism ],
function( phi)
  local source, range, G, mat, n, L, i, j, zero_obj, S;

  source := Source( phi );
  range := Range( phi );

  S := UnderlyingHomalgRing( phi );
  n := Length( IndeterminatesOfPolynomialRing( S ) );

  L := List( [ 1 .. n ], k -> TwistedCotangentSheaf( S, k - 1 ) );

  zero_obj := ZeroObject( CapCategory( phi ) );
  L := Concatenation( [ zero_obj ], L );

  if Position( L, source ) = fail or Position( L, range ) = fail then
    # Well here phi is supposed to be morphism between direct sum of canonical twisted cotangent sheaves
    L := DECOMPOSE_MORPHISM_OF_DIRECT_SUM_OF_NON_CANONICAL_TWISTED_COTANGENT_SHEAVES( phi );
    return List( L, l -> List( l, f -> MORPHISM_OF_TWISTED_COTANGENT_SHEAVES_AS_LIST_OF_RECORDS( f )[1][1] ) );
  fi;

  i := Position( L, source ) - 2;
  j := Position( L, range ) - 2;

  if i = -1 or j = -1 then
    
    return [ [ rec( indices := [ i, j ], coefficients := [ ] ) ] ];
    
  fi;

  if i < j then
    
    return [ [ rec( indices := [ i, j ], coefficients := [ ] ) ] ];
    
  fi;

  G := ShallowCopy( BasisBetweenTwistedCotangentSheaves( S, i, j ) );
  
  G := List( G, UnderlyingMatrix );
  
  G := UnionOfRows( List( G,
    g -> UnionOfColumns( List( [ 1 .. NrRows( g ) ], i -> CertainRows( g, [i] ) ) ) ) );
  
  mat := UnderlyingMatrix( phi );
  
  mat := UnionOfColumns( List( [ 1 .. NrRows( mat ) ], i -> CertainRows( mat, [i] ) ) );
  
  return [ [ rec( indices := [ i, j ], coefficients := EntriesOfHomalgMatrix( RightDivide( mat, G) ) ) ] ];
  
end );       

