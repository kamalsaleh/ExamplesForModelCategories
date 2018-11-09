

DeclareAttribute( "CoherentSheavesOverProjectiveSpace", IsHomalgGradedRing );

KeyDependentOperation( "TwistedStructureSheaf", IsHomalgGradedRing, IsInt, ReturnTrue );
KeyDependentOperation( "TwistedCotangentSheaf", IsHomalgGradedRing, IsInt, ReturnTrue );

DeclareOperation( "BasisBetweenTwistedStructureSheaves", [ IsHomalgGradedRing, IsInt, IsInt ] );
DeclareOperation( "BasisBetweenTwistedCotangentSheaves", [ IsHomalgGradedRing, IsInt, IsInt ] );

DeclareOperation( "TwistedStructureSheafAsQuiverRepresentation", [ IsQuiverAlgebra, IsInt, IsInt ] );
KeyDependentOperation( "TwistedCotangentSheafAsQuiverRepresentation", IsQuiverAlgebra, IsInt, ReturnTrue );
KeyDependentOperation( "TwistedCotangentSheafAsChain", IsHomalgGradedRing, IsInt, ReturnTrue );

DeclareOperation( "BasisBetweenTwistedStructureSheavesAsQuiverRepresentations", [ IsQuiverAlgebra, IsInt, IsInt, IsInt ] );
