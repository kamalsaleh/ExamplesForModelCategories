

#DeclareGlobalFunction( "LINEAR_QUIVER" );
#DeclareGlobalFunction( "LINEAR_LEFT_QUIVER" );
#DeclareGlobalFunction( "LINEAR_RIGHT_QUIVER" );

#DeclareGlobalFunction( "PRODUCT_OF_QUIVER_ALGEBRAS" );

DeclareGlobalFunction( "PRODUCT_OF_QUIVER_REPRESENTATIONS" );

DeclareGlobalFunction( "PRODUCT_OF_QUIVER_REPRESENTATION_HOMOMORPHISMS" );

DeclareGlobalFunction( "BASIS_OF_EXTERNAL_HOM_BETWEEN_PROJECTIVE_QUIVER_REPRESENTATIONS" );

DeclareAttribute( "DECOMPOSITION_OF_PROJECTIVE_QUIVER_REPRESENTATION", IsQuiverRepresentation );

if not IsBound( BasisOfExternalHom ) then
  
  DeclareOperation( "BasisOfExternalHom", [ IsCapCategoryObject, IsCapCategoryObject ] );
  
fi;

if not IsBound( CoefficientsOfLinearMorphism ) then
  
  DeclareAttribute( "CoefficientsOfLinearMorphism", IsCapCategoryMorphism );
  
fi;

DeclareOperation( "COEFFICIENTS_OF_LINEAR_MORPHISM", [ IsList, IsCapCategoryMorphism ] );


if not IsBound( FieldForHomomorphismStructure ) then
  
  DeclareAttribute( "FieldForHomomorphismStructure", IsCapCategory );
  
fi;

if not IsBound( MultiplyWithElementInFieldForHomomorphismStructure ) then
  
  DeclareOperation( "MultiplyWithElementInFieldForHomomorphismStructure", [ IsMultiplicativeElement, IsCapCategoryMorphism ]  );
  
fi;

# This method is absolete, its alternative is BasisOfHom.
# It can be used for debugging.
#DeclareGlobalFunction( "BASIS_OF_EXTERNAL_HOM_IN_QUIVER_REPS" );
#DeclareGlobalFunction( "BASIS_OF_EXTERNAL_HOM_IN_QUIVER_REPS_OVER_HOMALG_FIELD" );
#DeclareGlobalFunction( "BASIS_OF_EXTERNAL_HOM_IN_QUIVER_REPS_OVER_DEFAULT_HOMALG_FIELD" );

#DeclareGlobalFunction( "COMPUTE_LIFT_IN_QUIVER_REPS" );
#DeclareGlobalFunction( "COMPUTE_COLIFT_IN_QUIVER_REPS" );

#DeclareGlobalFunction( "COMPUTE_LIFT_IN_COMPLEXES_OF_QUIVER_REPS" );
#DeclareGlobalFunction( "COMPUTE_COLIFT_IN_COMPLEXES_OF_QUIVER_REPS" );

#DeclareGlobalFunction( "CONVERT_COMPLEX_OF_QUIVER_REPS_TO_QUIVER_REP" );
#DeclareGlobalFunction( "CONVERT_COMPLEX_MORPHISM_OF_QUIVER_REPS_TO_QUIVER_REP_MORPHISM" );

#DeclareGlobalFunction( "CONVERT_QUIVER_REP_MORPHISM_TO_COMPLEX_MORPHISM_OF_QUIVER_REPS" );
DeclareGlobalFunction( "COMPUTE_HOMOTOPY_IN_COMPLEXES_OF_QUIVER_REPS" );

#DeclareGlobalFunction( "STACK_LISTLIST_QPA_MATRICES" );

DeclareAttribute( "MORPHISM_OF_PROJECTIVE_QUIVER_REPS_AS_LIST_OF_MORPHISMS", IsQuiverRepresentationHomomorphism );

DeclareAttribute( "MORPHISM_OF_PROJECTIVE_QUIVER_REPS_AS_LIST_OF_RECORDS",
IsQuiverRepresentationHomomorphism );

#DeclareOperation( "StackMatricesDiagonally", [ IsQPAMatrix, IsQPAMatrix ] );
#DeclareOperation( "StackMatricesDiagonally", [ IsDenseList ] );
