LoadPackage( "ExamplesForModel" );

m := InputFromUser( "Working over P^m, m := " );

Display( "MAGMA? y/n " );

stream := InputTextUser(  );
WITH_MAGMA := CharInt( ReadByte( stream ) );

AQ := CotangentBeilinsonQuiverAlgebra( Rationals, m );
S := UnderlyingHomalgGradedPolynomialRing( AQ );;
A := UnderlyingHomalgGradedExteriorRing( AQ );;

graded_lp_cat_sym := GradedLeftPresentations( S );

coh := CoherentSheavesOverProjectiveSpace( S );
Sh := CanonicalProjection( coh );

H0 := HomologyFunctorAt( ChainComplexCategory( graded_lp_cat_sym ), graded_lp_cat_sym, 0 );

test := function( N )
local u, v, m_u, m_v, M, i, reg;

for i in [ 1 .. N ] do

Print( "Test ", i, " out of ", N, ":\n" );

M := RandomObject( graded_lp_cat_sym );

while IsZero( M ) do
  M := RandomObject( graded_lp_cat_sym );
od;

Print( "Random object is created!\n" );
Print( "With regularity: " );
reg := HomalgElementToInteger( CastelnuovoMumfordRegularity( M ) );
Print( reg, "\n" );

u := Maximum( 1,  reg + 1 );

Print( "u = ", u );

v := u + Random( [ 1 .. 3 ] );

Print( ", v = ", v, "\n" );

m_u := MORPHISM_FROM_ZEROTH_HOMOLOGY_OF_BEILINSON_REPLACEMENT_TO_GLP( u, M );;

Print( "m_u has been computed!\n" );

m_v := MORPHISM_FROM_ZEROTH_HOMOLOGY_OF_BEILINSON_REPLACEMENT_TO_GLP( v, M );;

Print( "m_v has been computed!\n" );

	if not IsCongruentForMorphisms( m_u, m_v ) then
		Error( "ALARAM!" );
		break;
	else
		Print( "OK\n\n" );
	fi;
od;
end;

test_cotangent_sheaves := function( )
local reg, u, v, m_u, m_v, M, i;

for i in [ 0 .. m ] do

Print( "Test ", i, " out of ", m, ":\n" );

M := TwistedCotangentSheaf( S, i );

reg := HomalgElementToInteger( CastelnuovoMumfordRegularity( M ) );

u := Maximum( 1, reg + 1 );

Print( "u = ", u, "\n" );
m_u := MORPHISM_FROM_GLP_TO_ZEROTH_HOMOLOGY_OF_BEILINSON_REPLACEMENT(u,M);;
Print( "m_u has been computed!\n" );
 
for v in [ u + 1 .. u + 4 ] do
  Print( "  v = ", v, "\n" ); 
  m_v := MORPHISM_FROM_GLP_TO_ZEROTH_HOMOLOGY_OF_BEILINSON_REPLACEMENT(v,M);;
  Print( "  m_v has been computed!\n" );

  if IsCongruentForMorphisms( m_u, m_v ) then
        Print( "Ok!\n" );
  elif IsCongruentForMorphisms( m_u, AdditiveInverse( m_v  ) ) then
		Print( "Alaram 1\n" );
		break;
  else
        Print( "Alaram 2\n" );
  fi;
od;
od;
end;

test_natural_transformation := function( f )
  local sf, u, v, h0, i;

u := MorphismFromZerothHomologyOfBeilinsonReplacementToGLP( Source( f ) );
Display( "u is computed" );

v := MorphismFromZerothHomologyOfBeilinsonReplacementToGLP( Range( f ) );
Display( "v is computed" );

h0 := ApplyFunctor( PreCompose( H0, Sh ), BeilinsonReplacement( f ) );
Display( "h0 is computed" );

sf := ApplyFunctor( Sh, f );

if not IsCongruentForMorphisms( PreCompose( u, sf ), PreCompose( h0, v ) ) then
  Error( "Alarammmmm" );
else
  Display( "OK" );
fi;

end;





