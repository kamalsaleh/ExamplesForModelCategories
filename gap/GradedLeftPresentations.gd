



# KeyDependentOperation( "TwistFunctor", IsHomalgGradedRing, IsInt, ReturnTrue );

KeyDependentOperation( "PositiveKoszulChainMorphism", IsHomalgGradedRing, IsInt, ReturnTrue );
KeyDependentOperation( "NegativeKoszulChainMorphism", IsHomalgGradedRing, IsInt, ReturnTrue );

DeclareAttribute( "MORPHISM_OF_TWISTED_STRUCTURE_SHEAVES_AS_LIST_OF_RECORDS", IsGradedLeftPresentationMorphism );
DeclareOperation( "RECORD_TO_MORPHISM_OF_TWISTED_STRUCTURE_SHEAVES_AS_QUIVER_REPS", [ IsQuiverAlgebra, IsInt, IsRecord ] );
DeclareOperation( "LIST_OF_RECORDS_TO_MORPHISM_OF_TWISTED_STRUCTURE_SHEAVES_AS_QUIVER_REPS", [ IsQuiverAlgebra, IsInt, IsList ] );
DeclareOperation( "GENERATORS_OF_EXTERNAL_HOM_IN_CHAINS_OF_GRADED_LEFT_PRESENTATIONS", [ IsBoundedChainComplex, IsBoundedChainComplex ] );
DeclareAttribute( "LIST_OF_MORPHISMS_BETWEEN_TWISTED_COTANGENT_BUNDLES_AS_QUIVER_REPS", IsQuiverAlgebra );
