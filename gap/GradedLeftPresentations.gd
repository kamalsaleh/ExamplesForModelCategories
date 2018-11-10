# KeyDependentOperation( "TwistFunctor", IsHomalgGradedRing, IsInt, ReturnTrue );

KeyDependentOperation( "PositiveKoszulChainMorphism", IsHomalgGradedRing, IsInt, ReturnTrue );
KeyDependentOperation( "NegativeKoszulChainMorphism", IsHomalgGradedRing, IsInt, ReturnTrue );

DeclareAttribute( "BeilinsonReplacement", IsGradedLeftPresentation );
DeclareAttribute( "BeilinsonReplacement", IsGradedLeftPresentationMorphism );

DeclareAttribute( "MORPHISM_OF_TWISTED_STRUCTURE_SHEAVES_AS_LIST_OF_RECORDS", IsGradedLeftPresentationMorphism );
DeclareAttribute( "MORPHISM_OF_TWISTED_COTANGENT_SHEAVES_AS_LIST_OF_RECORDS", IsGradedLeftPresentationMorphism );
DeclareAttribute( "MORPHISM_OF_TWISTED_OMEGA_MODULES_AS_LIST_OF_RECORDS", IsGradedLeftPresentationMorphism );
DeclareOperation( "RECORD_TO_MORPHISM_OF_TWISTED_STRUCTURE_SHEAVES_AS_QUIVER_REPS", [ IsQuiverAlgebra, IsInt, IsRecord ] );
DeclareOperation( "RECORD_TO_MORPHISM_OF_TWISTED_COTANGENT_SHEAVES_AS_QUIVER_REPS", [ IsQuiverAlgebra, IsRecord ] );

DeclareOperation( "LIST_OF_RECORDS_TO_MORPHISM_OF_TWISTED_STRUCTURE_SHEAVES_AS_QUIVER_REPS", [ IsQuiverAlgebra, IsInt, IsList ] );
DeclareOperation( "LIST_OF_RECORDS_TO_MORPHISM_OF_TWISTED_COTANGENT_SHEAVES_AS_QUIVER_REPS", [ IsQuiverAlgebra, IsList ] );

DeclareOperation( "GENERATORS_OF_EXTERNAL_HOM_IN_CHAINS_OF_GRADED_LEFT_PRESENTATIONS", [ IsBoundedChainComplex, IsBoundedChainComplex ] );
DeclareAttribute( "LIST_OF_MORPHISMS_BETWEEN_TWISTED_COTANGENT_BUNDLES_AS_QUIVER_REPS", IsQuiverAlgebra );

DeclareAttribute( "MORPHISM_INTO_CANONICAL_TWISTED_COTANGENT_SHEAF", IsGradedLeftPresentation );
DeclareAttribute( "MORPHISM_FROM_CANONICAL_TWISTED_COTANGENT_SHEAF", IsGradedLeftPresentation );

DeclareAttribute( "CANONICALIZE_SOME_TWISTED_COTANGENT_SHEAF", IsGradedLeftPresentation );
DeclareAttribute( "CANONICALIZE_SOME_TWISTED_COTANGENT_SHEAVES_MORPHISM", IsGradedLeftPresentationMorphism );

DeclareAttribute( "DECOMPOSE_DIRECT_SUM_OF_NON_CANONICAL_TWISTED_COTANGENT_SHEAVES", IsGradedLeftPresentation );
DeclareAttribute( "DECOMPOSE_MORPHISM_OF_DIRECT_SUM_OF_NON_CANONICAL_TWISTED_COTANGENT_SHEAVES", IsGradedLeftPresentationMorphism );
DeclareAttribute( "CANONICALIZE_DIRECT_SUM_OF_NON_CANONICAL_COTANGENT_SHEAVES", IsGradedLeftPresentation );
DeclareAttribute( "CANONICALIZE_GRADED_LEFT_PRESENTATION_MORPHISM_BETWEEN_DIRECT_SUMS_OF_NON_CANONICAL_COTANGENT_SHEAVES", IsGradedLeftPresentationMorphism );

DeclareOperation( "TwistedOmegaModule", [ IsExteriorRing, IsInt ] );
DeclareOperation( "BasisBetweenTwistedOmegaModules", [ IsExteriorRing, IsInt, IsInt ] );

