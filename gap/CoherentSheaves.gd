
DeclareOperation( "TwistedStructureSheafAsQuiverRepresentation", [ IsQuiverAlgebra, IsInt, IsInt ] );
KeyDependentOperation( "TwistedCotangentSheafAsQuiverRepresentation", IsQuiverAlgebra, IsInt, ReturnTrue );

DeclareOperation( "BasisBetweenTwistedStructureSheavesAsQuiverRepresentations", [ IsQuiverAlgebra, IsInt, IsInt, IsInt ] );
DeclareOperation( "BasisBetweenTwistedCotangentSheavesAsQuiverRepresentations", [ IsQuiverAlgebra, IsInt, IsInt ] );

DeclareAttribute( "CotangentBeilinsonFunctor", IsQuiverAlgebra );
DeclareAttribute( "StructureBeilinsonFunctor", IsQuiverAlgebra );

# KeyDependentOperation( "BASIS_BETWEEN_TWISTED_COTANGENT_BUNDLES_AS_CHAINS", IsHomalgGradedRing, IsInt, ReturnTrue );
