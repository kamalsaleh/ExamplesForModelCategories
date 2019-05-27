LoadPackage( "ExamplesForModel" );

m := InputFromUser( "Working over P^m, m := " );

AQ := CotangentBeilinsonQuiverAlgebra( Rationals, m );
S := UnderlyingHomalgGradedPolynomialRing( AQ );;
A := UnderlyingHomalgGradedExteriorRing( AQ );;

graded_lp_cat_sym := GradedLeftPresentations( S );

coh := CoherentSheavesOverProjectiveSpace( S );
Sh := CanonicalProjection( coh );

f := RandomMorphism( graded_lp_cat_sym, 3 );
Tf := TateResolution( f );
Bf := BeilinsonReplacement( f );

Display( f );
Display( Bf );

