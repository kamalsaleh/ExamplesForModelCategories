LoadPackage( "ExamplesForModelCategories" );

n := InputFromUser( "P^n, for n = " );
AQ := CotangentBeilinsonQuiverAlgebra( Rationals, n );
S := UnderlyingHomalgGradedPolynomialRing( AQ );
A := UnderlyingHomalgGradedExteriorRing( AQ );
L := LFunctor( S );
cochains := CochainComplexCategory( GradedLeftPresentations( S ) );
Tr := BrutalTruncationAboveFunctor( cochains, -1 );
H_m1 := CohomologyFunctorAt( cochains, GradedLeftPresentations( S ), -1 );


OLD_L := function( S )
    local cat_lp_ext, cat_lp_sym, cochains, ind_ext, ind_sym, L, KS, n, name;

    n := Length( IndeterminatesOfPolynomialRing( S ) );
    KS := KoszulDualRing( S );
    ind_ext := IndeterminatesOfExteriorRing( KS );
    ind_sym := IndeterminatesOfPolynomialRing( S );

    cat_lp_sym := GradedLeftPresentations( S );
    cat_lp_ext := GradedLeftPresentations( KS );
    cochains := CochainComplexCategory( cat_lp_sym );
    name := Concatenation( "L functor from ", Name( cat_lp_ext ), " to ", Name( cochains ) );
    L := CapFunctor( name, cat_lp_ext, cochains );

    AddObjectFunction( L,
        function( M )
        local hM, diffs, C, d;
        hM := AsPresentationInHomalg( M );
        diffs := MapLazy( IntegersList,
            function( i )
            local l, source, range;
            l := List( ind_ext, e -> RepresentationMapOfRingElement( e, hM, -i ) );
            l := List( l, m -> S * MatrixOfMap( m, 1, 1 ) );
            l := Sum( List( [ 1 .. n ], j -> ind_sym[ j ]* l[ j ] ) );
            source := GradedFreeLeftPresentation( NrRows( l ), S, List( [ 1 .. NrRows( l ) ], j -> -i ) );
            range := GradedFreeLeftPresentation( NrColumns( l ), S, List( [ 1 .. NrColumns( l ) ], j -> -i - 1 ) );
            return GradedPresentationMorphism( source, l, range );
            end, 1 );
        C :=  CochainComplex( cat_lp_sym, diffs );

        d := ShallowCopy( GeneratorDegrees( M ) );

        # the output of GeneratorDegrees is in general not integer.
        Apply( d, String );
        Apply( d, Int );

        if Length( d ) = 0 then
            SetLowerBound( C, 0 );
            SetUpperBound( C, 0 );
        else
            SetLowerBound( C, -Maximum( d ) - 1 );
            SetUpperBound( C, -Minimum( d ) + n + 1);
        fi;

        return C;

        end );

    AddMorphismFunction( L,
        function( new_source, f, new_range )
        local M, N, G1, G2, mors;
        M := Source( f );
        N := Range( f );
        mors := MapLazy( IntegersList,
                 function( k )
                local hM, hN, hMk, hNk, hMk_, hNk_, iMk, iNk, l;
                # There is a reason to write the next two lines like this
                # See AdjustedGenerators.
                hM := LeftPresentationWithDegrees( UnderlyingMatrix( M ), GeneratorDegrees( M ) );
                hN := LeftPresentationWithDegrees( UnderlyingMatrix( N ), GeneratorDegrees( N ) );
                hMk := HomogeneousPartOverCoefficientsRing( -k, hM );
                hNk := HomogeneousPartOverCoefficientsRing( -k, hN );
                G1 := GetGenerators( hMk );
                G2 := GetGenerators( hNk );
                if Length( G1 ) = 0 or Length( G2 ) = 0 then
                    return ZeroMorphism( new_source[ k ], new_range[ k ] );
                fi;
                hMk_ := UnionOfRows( G1 )* KS;
                hNk_ := UnionOfRows( G2 )* KS;
                iMk := GradedPresentationMorphism( GradedFreeLeftPresentation( NrRows( hMk_ ), KS, List( [1..NrRows( hMk_ ) ], i -> -k ) ), hMk_, M );
                iNk := GradedPresentationMorphism( GradedFreeLeftPresentation( NrRows( hNk_ ), KS, List( [1..NrRows( hNk_ ) ], i -> -k ) ), hNk_, N );
                l := Lift( PreCompose( iMk, f ), iNk );
                return GradedPresentationMorphism( new_source[ k ], UnderlyingMatrix( l ) * S, new_range[ k ] );
                end, 1 );

        return CochainMorphism( new_source, new_range, mors );
        end );
    return L;
end;

old_L := OLD_L(S);

for i in [ 0 .. n ] do
    for j in [ 0 .. i ] do
        Print( "i = ", i, ", j = ", j, "\n" );
        B := BasisBetweenTwistedOmegaModules( A, i, j );
        for f in B do
            Print( IsEqualForMorphisms( ApplyFunctor( L, f ), ApplyFunctor( old_L, f ) ), "\n" );
            if not IsWellDefined( ApplyFunctor( L, f ) ) then
              Error( "L is not well-defined here" );
            fi;
        od;
        Print( "----------\n" );
    od;
od;

