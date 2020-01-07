# Installing external basis methods for vector spaces
#

if not IsBound( BasisOfExternalHom ) then
  
  DeclareOperation( "BasisOfExternalHom", [ IsCapCategoryObject, IsCapCategoryObject ] );

fi;

##
InstallMethod( BasisOfExternalHom,
    [ IsVectorSpaceObject, IsVectorSpaceObject ],
  function( a, b )
    local cat, hom_ab, D, B;
    
    cat := CapCategory( a );
    
    hom_ab := HomomorphismStructureOnObjects( a, b );
    
    D := DistinguishedObjectOfHomomorphismStructure( cat );
    
    B := List( [ 1 .. Dimension( hom_ab ) ],
          i -> List( [ 1 .. Dimension( hom_ab ) ],
            function( j )
              
              if i = j then
                
                return 1;
              
              else
                
                return 0;
              
              fi;
            
            end ) );
    
    B := List( B, mat -> VectorSpaceMorphism( D, mat, hom_ab ) );
    
    return List( B, mor -> InterpretMorphismFromDistinguishedObjectToHomomorphismStructureAsMorphism( a, b, mor ) );
    
end );

##
InstallMethod( BasisOfExternalHom,
    [ IsHomotopyCategoryObject, IsHomotopyCategoryObject ],
  function( a, b )
    local hom_a_b, D, B;
    
    hom_a_b := HomomorphismStructureOnObjects( a, b );
    
    D := DistinguishedObjectOfHomomorphismStructure( CapCategory( hom_a_b ) );
    
    B := BasisOfExternalHom( D, hom_a_b );
    
    return List( B, f -> InterpretMorphismFromDistinguishedObjectToHomomorphismStructureAsMorphism( a, b, f ) );
    
end );

if not IsBound( FieldForHomomorphismStructure ) then
  
  DeclareAttribute( "FieldForHomomorphismStructure", IsCapCategory );

fi;

##
InstallMethod( FieldForHomomorphismStructure, [ IsCapCategory ], CommutativeRingOfLinearCategory );
 
if not IsBound( CoefficientsOfLinearMorphism ) then
  
  DeclareAttribute( "CoefficientsOfLinearMorphism", IsCapCategoryMorphism );
 
fi;
 
##
InstallMethod( CoefficientsOfLinearMorphism,
      [ IsVectorSpaceMorphism ],
    function( phi )
      
      return EntriesOfHomalgMatrix(
                UnderlyingMatrix( 
                  InterpretMorphismAsMorphismFromDistinguishedObjectToHomomorphismStructure( phi )
                                ) );
end );

##
InstallMethod( CoefficientsOfLinearMorphism,
      [ IsHomotopyCategoryMorphism ],
  function( phi )
    return EntriesOfHomalgMatrix( 
              UnderlyingMatrix(
                InterpretMorphismAsMorphismFromDistinguishedObjectToHomomorphismStructure( phi )
                              ) );
end );

if not IsBound( MultiplyWithElementOfCommutativeRingForMorphisms ) then 
  
  DeclareOperation( "MultiplyWithElementInFieldForHomomorphismStructure", [ IsMultiplicativeElement, IsCapCategoryMorphism ] );
  
fi;

##
InstallMethod( MultiplyWithElementInFieldForHomomorphismStructure,
  [ IsMultiplicativeElement, IsVectorSpaceMorphism ], MultiplyWithElementOfCommutativeRingForMorphisms );

