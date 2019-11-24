LoadPackage( "ExamplesForModelCategories" );

A := CotangentBeilinsonQuiverAlgebra( Rationals, 1 );

S := UnderlyingHomalgGradedPolynomialRing( A );

F := _CotangentBeilinsonFunctor_Modified(A);

f := function( c ) return ApplyFunctor( F, c ); end;

o := GradedFreeLeftPresentation( 1, S, [ 0 ] );

T := TateResolution( o );

# To compute H^i( P^1, M[ j ] ) we use
# DimensionOfTateCohomology( TateResolution( M ), i, j );

DimensionOfTateCohomology( T, 0, 0 );
# 1
DimensionOfTateCohomology( T, 0, 1 );
# 2

# We have Ext^i( o( p ), o( q ) ) = Ext^i( o, o[ q - p ] ) = H^i( P^1, o[ q - p ] )
# Ext^i( o( p ), o( q ) ) = Ext^i( f( o( p ) ), f( o( q ) ) )
#                         = Hom_D( f( o( p ) ), Shift( f( o( q ) ), 1 ) )

p := 2; q := -1;

DimensionOfTateCohomology( T, 1, q - p );
# 2
HomomorphismStructureOnObjects( f( o[ p ] ), Shift( f( o[ q ] ), 1 ) );
# 2

