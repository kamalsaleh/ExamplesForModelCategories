

DeclareAttribute( "CoherentSheavesOverProjectiveSpace", IsHomalgGradedRing );

KeyDependentOperation( "TwistedStructureSheaf", IsHomalgGradedRing, IsInt, ReturnTrue );
KeyDependentOperation( "TwistedCotangentSheaf", IsHomalgGradedRing, IsInt, ReturnTrue );

DeclareOperation( "BasisBetweenTwistedStructureSheaves", [ IsHomalgGradedRing, IsInt, IsInt ] );
DeclareOperation( "BasisBetweenTwistedCotangentSheaves", [ IsHomalgGradedRing, IsInt, IsInt ] );

DeclareOperation( "TwistedStructureSheafAsQuiverRepresentation", [ IsQuiverAlgebra, IsInt, IsInt ] );

DeclareOperation( "BasisBetweenTwistedStructureSheavesAsQuiverRepresentations", [ IsQuiverAlgebra, IsInt, IsInt, IsInt ] );
