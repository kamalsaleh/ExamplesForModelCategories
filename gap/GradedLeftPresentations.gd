



# KeyDependentOperation( "TwistFunctor", IsHomalgGradedRing, IsInt, ReturnTrue );

KeyDependentOperation( "PositiveKoszulChainMorphism", IsHomalgGradedRing, IsInt, ReturnTrue );
KeyDependentOperation( "NegativeKoszulChainMorphism", IsHomalgGradedRing, IsInt, ReturnTrue );

DeclareAttribute( "BeilinsonReplacement", IsGradedLeftPresentation );
DeclareAttribute( "BeilinsonReplacement", IsGradedLeftPresentationMorphism );

DeclareAttribute( "MORPHISM_OF_TWISTED_STRUCTURE_SHEAVES_AS_LIST_OF_RECORDS", IsGradedLeftPresentationMorphism );
DeclareOperation( "RECORD_TO_MORPHISM_OF_TWISTED_STRUCTURE_SHEAVES_AS_QUIVER_REPS", [ IsQuiverAlgebra, IsInt, IsRecord ] );
DeclareOperation( "LIST_OF_RECORDS_TO_MORPHISM_OF_TWISTED_STRUCTURE_SHEAVES_AS_QUIVER_REPS", [ IsQuiverAlgebra, IsInt, IsList ] );
DeclareOperation( "GENERATORS_OF_EXTERNAL_HOM_IN_CHAINS_OF_GRADED_LEFT_PRESENTATIONS", [ IsBoundedChainComplex, IsBoundedChainComplex ] );
DeclareAttribute( "LIST_OF_MORPHISMS_BETWEEN_TWISTED_COTANGENT_BUNDLES_AS_QUIVER_REPS", IsQuiverAlgebra );

DeclareAttribute( "MORPHISM_INTO_CANONICAL_TWISTED_COTANGENT_SHEAF", IsGradedLeftPresentation );
DeclareAttribute( "MORPHISM_FROM_CANONICAL_TWISTED_COTANGENT_SHEAF", IsGradedLeftPresentation );

DeclareAttribute( "CANONICALIZE_SOME_TWISTED_COTANGENT_SHEAF", IsGradedLeftPresentation );
DeclareAttribute( "CANONICALIZE_SOME_TWISTED_COTANGENT_SHEAVES_MORPHISM", IsGradedLeftPresentationMorphism );