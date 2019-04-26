

DeclareGlobalFunction( "LINEAR_QUIVER" );
DeclareGlobalFunction( "LINEAR_LEFT_QUIVER" );
DeclareGlobalFunction( "LINEAR_RIGHT_QUIVER" );

DeclareGlobalFunction( "PRODUCT_OF_QUIVER_ALGEBRAS" );
DeclareGlobalFunction( "PRODUCT_OF_QUIVER_REPRESENTATIONS" );
DeclareGlobalFunction( "PRODUCT_OF_QUIVER_REPRESENTATION_HOMOMORPHISMS" );

if not IsBound( BasisOfExternalHom ) then
  
  DeclareOperation( "BasisOfExternalHom", [ IsCapCategoryObject, IsCapCategoryObject ] );
  
fi;

if not IsBound( CoefficientsOfLinearMorphism ) then
  
  DeclareAttribute( "CoefficientsOfLinearMorphism", IsCapCategoryMorphism );
  
fi;

if not IsBound( FieldForHomomorphismStructure ) then
  
  DeclareAttribute( "FieldForHomomorphismStructure", IsCapCategory );
  
fi;

if not IsBound( MultiplyWithElementInFieldForHomomorphismStructure ) then
  
  DeclareOperation( "MultiplyWithElementInFieldForHomomorphismStructure", [ IsMultiplicativeElement, IsCapCategoryMorphism ]  );
  
fi;
 
DeclareGlobalFunction( "GENERATORS_OF_EXTERNAL_HOM_IN_QUIVER_REPS" );
DeclareGlobalFunction( "GENERATORS_OF_EXTERNAL_HOM_IN_CHAINS_OF_QUIVER_REPS" );

DeclareGlobalFunction( "COMPUTE_LIFT_IN_QUIVER_REPS" );
DeclareGlobalFunction( "COMPUTE_COLIFT_IN_QUIVER_REPS" );

DeclareGlobalFunction( "COMPUTE_LIFTS_IN_COMPLEXES_OF_QUIVER_REPS" );
DeclareGlobalFunction( "COMPUTE_COLIFTS_IN_COMPLEXES_OF_QUIVER_REPS" );

DeclareGlobalFunction( "CONVERT_COMPLEX_OF_QUIVER_REPS_TO_QUIVER_REP" );
DeclareGlobalFunction( "CONVERT_COMPLEX_MORPHISM_OF_QUIVER_REPS_TO_QUIVER_REP_MORPHISM" );

DeclareGlobalFunction( "CONVERT_QUIVER_REP_MORPHISM_TO_COMPLEX_MORPHISM_OF_QUIVER_REPS" );
