LoadPackage( "ExamplesForModelCategories" );

n := InputFromUser( "P^n, for n = " );
AQ := CotangentBeilinsonQuiverAlgebra( Rationals, n );
S := UnderlyingHomalgGradedPolynomialRing( AQ );
A := UnderlyingHomalgGradedExteriorRing( AQ );
L := LFunctor( S );
cochains := CochainComplexCategory( GradedLeftPresentations( S ) );
Tr := BrutalTruncationAboveFunctor( cochains, -1 );
H_m1 := CohomologyFunctorAt( cochains, GradedLeftPresentations( S ), -1 );

for i in [ 0 .. n ] do
    for j in [ 0 .. i ] do
        Print( "i = ", i, ", j = ", j, "\n" );
        B := BasisBetweenTwistedCotangentSheaves( S, i, j );
        for f in B do
            Print( IsEqualForMorphisms( f, ApplyFunctor( PreCompose( [ L, Tr, H_m1 ] ), TateResolution(f)[0] ) ), "\n" );
            if not IsWellDefined( ApplyFunctor( L, TateResolution(f)[0] ) ) then
              Error( "L is not well-defined here" );
            fi;
        od;
        Print( "----------\n" );
    od;
od;

