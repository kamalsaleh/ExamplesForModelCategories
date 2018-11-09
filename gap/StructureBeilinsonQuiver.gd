



KeyDependentOperation( "StructureBeilinsonQuiverAlgebra", IsField, IsInt, ReturnTrue );

DeclareAttribute( "UnderlyingHomalgGradedPolynomialRing", IsQuiverAlgebra );
DeclareAttribute( "UnderlyingHomalgGradedExteriorRing", IsQuiverAlgebra );

DeclareOperation( "TwistedStructureSheaf", [ IsQuiverAlgebra, IsInt, IsInt ] );
DeclareOperation( "HOMALG_GRADED_POLYNOMIAL_RING", [ IsInt ] );
DeclareGlobalFunction( "PREPARE_CATEGORIES_OF_HOMALG_GRADED_POLYNOMIAL_RING" );
