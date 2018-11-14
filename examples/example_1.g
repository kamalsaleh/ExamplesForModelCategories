LoadPackage( "ExamplesForModelCategories" );

A := CotangentBeilinsonQuiverAlgebra( Rationals, 2 );
S := UnderlyingHomalgGradedPolynomialRing( A );

c0 := Random( BasisBetweenTwistedStructureSheaves( S, -1, 1 ) );
C := ChainComplex( [ c0 ], 0 );

d1 := Random( BasisBetweenTwistedStructureSheaves( S, 0, 2 ) );
D := ChainComplex( [ d1 ], 1 );

h_m1 := Random( BasisBetweenTwistedStructureSheaves( S, 1, 2 ) );
h_0 := Random( BasisBetweenTwistedStructureSheaves( S, -1, 0 ) );

phi_0 := PreCompose( h_0, d1 ) + PreCompose( c0, h_m1 );
phi := ChainMorphism( C, D, [ phi_0 ], 0 );

IsNullHomotopic( phi );
H_phi := HomotopyMorphisms( phi );

B := BeilinsonReplacement( phi );
IsNullHomotopic( B );
H_B := HomotopyMorphisms( B );

F := CotangentBeilinsonFunctor( A );
psi := ApplyFunctor( F, phi );
IsZeroForMorphisms( psi );

rep_psi := UnderlyingReplacement( psi );
IsNullHomotopic( rep_psi );
H_rep_psi := HomotopyMorphisms( rep_psi );

Display( psi );
