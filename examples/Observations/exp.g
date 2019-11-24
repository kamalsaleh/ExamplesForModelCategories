LoadPackage( "ExamplesForMo" );

A := CotangentBeilinsonQuiverAlgebra( Rationals, 2 );
S := UnderlyingHomalgGradedPolynomialRing( A );
graded_lp_cat := GradedLeftPresentations( S );


random_endomorphism := function(S,n,random)
  local o, L, M, G;

  o := GradedFreeLeftPresentation( 1, S, [ 0 ] );
  
  L := List( [ -n .. n ], i -> o[ i ] );
  
  M := DirectSum( L );
  
  G := GeneratorsOfExternalHom( M, M );
  
  return Sum( G{List( [ 1 .. random ], i -> Random([ 1 .. Length(G)]) )} );
  
end;

next_endomorphism := function(f, n, random)
  local S, pi, o, L, M, G;
  
  S := UnderlyingHomalgRing(f);
  
  pi := CokernelProjection( f );
  
  o := GradedFreeLeftPresentation( 1, S, [ 0 ] );
  
  L := List( [ -n .. n ], i -> o[ i ] );
  
  M := DirectSum( L );
  
  G := GeneratorsOfExternalHom( Range( pi ), M );
  
  if Length( G ) = 0 then
    
    Error( "Please choose larger n\n" );
    
  fi;
  
  return PreCompose( pi, Sum( G{List( [ 1 .. random ], i -> Random([ 1 .. Length(G)]) )} ) );
  
end;


L := [ random_endomorphism(S,2,10) ];
Add( L, next_endomorphism( L[1], 2, 10 ), 1 );
# same


