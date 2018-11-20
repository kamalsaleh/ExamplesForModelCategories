LoadPackage( "ExamplesForModelCategories" );

AQ := CotangentBeilinsonQuiverAlgebra( Rationals, 4 );
S := UnderlyingHomalgGradedPolynomialRing( AQ );
A := UnderlyingHomalgGradedExteriorRing( AQ );

coh := CoherentSheavesOverProjectiveSpace( S );
Sh := CanonicalProjection( coh );

mat := HomalgMatrix( "[ \
e1*e4, e2*e0, e3*e1, e4*e2, e0*e3, \
e2*e3, e3*e4, e4*e0, e0*e1, e1*e2  \
]", 2, 5, A );

A2 := GradedFreeLeftPresentation( 2, A, [ 3, 3 ] );
A5 := GradedFreeLeftPresentation( 5, A, [ 5, 5, 5, 5, 5 ] );
phi := GradedPresentationMorphism( A2, mat, A5 );
P := KernelObject( phi );
B := BeilinsonReplacement( P );
M := HomologyAt( B, 0 );
# The sheafification of M is the Horrocks Mumford Bundle

hM := AsPresentationInHomalg( M );
ByASmallerPresentation( hM );

D := BettiDiagram( TateResolution( hM, -5, 5 ) );
Display( D );
