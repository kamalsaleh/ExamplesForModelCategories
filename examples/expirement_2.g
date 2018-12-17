LoadPackage( "ExamplesForModel" );

m := InputFromUser( "Working over P^m, m := " );

AQ := CotangentBeilinsonQuiverAlgebra( Rationals, m );
S := UnderlyingHomalgGradedPolynomialRing( AQ );;
A := UnderlyingHomalgGradedExteriorRing( AQ );;

graded_lp_cat_sym := GradedLeftPresentations( S );
graded_lp_cat_ext := GradedLeftPresentations( A );

cochains := CochainComplexCategory( graded_lp_cat_sym );

coh := CoherentSheavesOverProjectiveSpace( S );

Sh := CanonicalProjection( coh );
L := LCochainFunctor( S );;

f := RandomGradedPresentationMorphism( S, 2, 3, 3, 3, [ -1 .. 2 ] );

M := Source( f );
r := CastelnuovoMumfordRegularity( M );

nat := function(M,i)
  return ApplyNaturalTransformation( NatTransFromTruncationUsingHomalgToIdentityFunctor( S, i ), M );
end;

i := r + Random( [ 1 .. 5 ] );
emb_M_i := nat( M, i );
emb_M_i_plus_1 := nat( M, i + 1 );
t := AsCochainComplex( TateResolution( M ) )^i;
Lt := ApplyFunctor( L, t );
H := PreCompose( Lt[ -i - 1 ], EpimorphismFromSomeProjectiveObject( Source( emb_M_i_plus_1 ) ) );
V := PreCompose( Source( Lt )^( -i - 1 ), EpimorphismFromSomeProjectiveObject( Source( emb_M_i ) ) );
G := GeneralizedMorphismBySpan( H, V );
l := HonestRepresentative( G );
IsEqualForMorphisms( PreCompose( l, emb_M_i ), emb_M_i_plus_1 );
IsEqualForMorphisms( PreCompose( l, emb_M_i ), -emb_M_i_plus_1 );

