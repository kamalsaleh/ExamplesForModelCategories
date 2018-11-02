

DeclareAttribute( "CoherentSheavesOverProjectiveSpace", IsHomalgGradedRing );

KeyDependentOperation( "TwistedStructureSheaf", IsHomalgGradedRing, IsInt, ReturnTrue );

DeclareOperation( "BasisBetweenTwistedStructureSheaves", [ IsHomalgGradedRing, IsInt, IsInt ] );

DeclareOperation( "BasisBetweenTwistedStructureSheavesAsQuiverRepresentations", [ IsQuiverAlgebra, IsInt, IsInt, IsInt ] );
