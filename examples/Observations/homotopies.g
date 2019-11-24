LoadPackage( "ExamplesForModel" );

TEST_HOMOTOPY :=
function( C, N )
  local H, i, l;
  
  H := HomotopyMorphisms( C );
  
  for i in [ ActiveLowerBound( C ) .. ActiveUpperBound( C ) ] do
    
    l := List( [ -N .. N ], n ->
      
      IsZero( PreCompose( H[i][n], H[i-2][n+1] ) )
            
             );
    
    Display( l );
    
  od;
  
end;
