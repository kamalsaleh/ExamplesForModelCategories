LoadPackage( "ExamplesForModelCategories" );

A := CotangentBeilinsonQuiverAlgebra( Rationals, 2 );
S := UnderlyingHomalgGradedPolynomialRing( A );
graded_lp_cat := GradedLeftPresentations( S );
coh := CoherentSheavesOverProjectiveSpace( S );

F := _CotangentBeilinsonFunctor(A);;
U := _ProjectiveQuiverRepsToTwistedCotangentSheavesFunctor(A);;

homotopy_quivers := AsCapCategory( Range( F ) );
SetRangeCategoryOfHomomorphismStructure( coh, RangeCategoryOfHomomorphismStructure( homotopy_quivers ) );

HOMOMORPHISM_STRUCTURE_ON_OBJECTS :=
  function( a, b )
    coh := CapCategory( a );
    B := CotangentBeilinsonQuiverAlgebra( Rationals, 2 );
end;

