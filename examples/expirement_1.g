LoadPackage( "ExamplesForModel" );

RandomGradedPresentationMorphism := function( R, m, u, n, v, D )
  local d_A_1, d_A_2, d_B_1, d_B_2, d_C_1, d_C_2, A, B, C, M, N;
  if HasIsExteriorRing( R ) and IsExteriorRing( R ) then
    d_A_1 := List( [ 1 .. m ], i -> Random( D ) );
    d_A_2 := List( [ 1 .. n ], i -> Maximum( d_A_1 ) + Random( [ -1 .. 2 ] ) );
    d_B_1 := d_A_2;
    d_B_2 := List( [ 1 .. u ], i -> Maximum( d_B_1 ) + Random( [ -1 .. 2 ] ) );
    d_C_1 := d_B_2;
    d_C_2 := List( [ 1 .. v ], i -> Maximum( d_C_1 ) + Random( [ -1 .. 2 ] ) );

    A := RandomMatrixBetweenGradedFreeLeftModules( d_A_1, d_A_2, R );
    B := RandomMatrixBetweenGradedFreeLeftModules( d_B_1, d_B_2, R );
    C := RandomMatrixBetweenGradedFreeLeftModules( d_C_1, d_C_2, R );
    M := AsGradedLeftPresentation( A*B, d_B_2 );
    N := AsGradedLeftPresentation( B*C, d_C_2 );
    return GradedPresentationMorphism( M, C, N );
  else
    d_A_1 := List( [ 1 .. m ], i -> Random( D ) );
    d_A_2 := List( [ 1 .. n ], i -> Minimum( d_A_1 ) + Random( [ -2 .. 1 ] ) );
    d_B_1 := d_A_2;
    d_B_2 := List( [ 1 .. u ], i -> Minimum( d_B_1 ) + Random( [ -2 .. 1 ] ) );
    d_C_1 := d_B_2;
    d_C_2 := List( [ 1 .. v ], i -> Minimum( d_C_1 ) + Random( [ -2 .. 1 ] ) );

    A := RandomMatrixBetweenGradedFreeLeftModules( d_A_1, d_A_2, R );
    B := RandomMatrixBetweenGradedFreeLeftModules( d_B_1, d_B_2, R );
    C := RandomMatrixBetweenGradedFreeLeftModules( d_C_1, d_C_2, R );
    M := AsGradedLeftPresentation( A*B, d_B_2 );
    N := AsGradedLeftPresentation( B*C, d_C_2 );
    return GradedPresentationMorphism( M, C, N );
  fi;
end;

m := InputFromUser( "Working over P^m, m := " );

AQ := CotangentBeilinsonQuiverAlgebra( Rationals, m );
S := UnderlyingHomalgGradedPolynomialRing( AQ );;
A := UnderlyingHomalgGradedExteriorRing( AQ );;

graded_lp_cat_sym := GradedLeftPresentations( S );
graded_lp_cat_ext := GradedLeftPresentations( A );

cochains := CochainComplexCategory( graded_lp_cat_sym );
coh := CoherentSheavesOverProjectiveSpace(S);

Sh := CanonicalProjection( coh );
L := LCochainFunctor( S );;
Tr := BrutalTruncationAboveFunctor( cochains, -1 );;
Cok := CokernelObjectFunctor( cochains, graded_lp_cat_sym, -2 );;
B := PreCompose( [ L, Tr, Cok ] );;
ChB := ExtendFunctorToCochainComplexCategoryFunctor(B);;

f := RandomGradedPresentationMorphism( S, 1, 3, 2, 4, [ -2 .. 2 ] );

t := function( M, u, v )
  local coh, graded_lp_cat_sym, graded_lp_cat_ext, L, tM, diffs, CM, G, span_to_three_arrows, T, Sh;
  
  if u > v then
    Error( "the second argument should be less or equal to the third argument" );
  fi;

  coh := CoherentSheavesOverProjectiveSpace( UnderlyingHomalgRing( M ) );
  Sh := CanonicalProjection( coh );

  graded_lp_cat_sym := CapCategory( M );
  graded_lp_cat_ext := GradedLeftPresentations( KoszulDualRing( UnderlyingHomalgRing( M ) ) );

  if u = v then
    T := TruncationFunctorUsingTateResolution( UnderlyingHomalgRing( M ), u );
    return ApplyFunctor( Sh, IdentityMorphism( ApplyFunctor( T, M ) ) );
  fi;

  L := LCochainFunctor( UnderlyingHomalgRing( M ) );
  tM := AsCochainComplex( TateResolution( M ) );
  
  diffs := MapLazy( IntegersList, function( i )
    if i < u - 2 or i > v then
      return ZeroObjectFunctorial( graded_lp_cat_ext );
    elif i = u-2 then
      return UniversalMorphismFromZeroObject( KernelObject( tM^u ) );
    elif i = u-1 then
      return KernelEmbedding( tM^u );
    elif i >= u and i < v-1 then
      return tM^i;
    elif i = v-1 then
      return KernelLift( tM^v, tM^(v-1) );
    elif i = v then
      return UniversalMorphismIntoZeroObject( KernelObject( tM^v ) );
    fi;
    end, 1 );

  CM := CochainComplex( graded_lp_cat_ext, diffs );
  SetLowerBound( CM, u - 2 );
  SetUpperBound( CM, v + 1 );
  
  G := List( [ u-1 .. v-1 ],
  function( i )
    local H, V;
    if i = u - 1 then
      H :=  ApplyFunctor( L, CM^( u-1 ) )[ -u ];
      V :=  CokernelProjection( ApplyFunctor( L, CM[ u-1 ] )^( -u - 1 ) );
      return GeneralizedMorphismBySpan( H, V );
    elif i = v-1 then
      H :=  PreCompose( ApplyFunctor( L, CM^( v-1 ) )[ -v ], CokernelProjection( ApplyFunctor( L, CM[ v ] )^( -v-1 ) ) );
      V :=  ApplyFunctor( L, CM[ v-1 ] )^( -v );
      return GeneralizedMorphismBySpan( H, V );
    else
      H :=  ApplyFunctor( L, CM^( i ) )[ -i - 1 ];
      V :=  ApplyFunctor( L, CM[ i ] )^( -i - 1 );
    return GeneralizedMorphismBySpan( H, V );
    fi;
  end );

  span_to_three_arrows := FunctorFromSpansToThreeArrows( graded_lp_cat_sym );;
  G := List( G, l -> ApplyFunctor( span_to_three_arrows, l ) );
  return SerreQuotientCategoryMorphism( coh, PostCompose( G ) );
end;

Test_Natural_Transformation := function( nat, f )
  local F, G, F_f, G_f, nat_source_f, nat_range_f;
  
  F := Source( nat );
  G := Range( nat );

  F_f := ApplyFunctor( F, f );
  G_f := ApplyFunctor( G, f );

  nat_source_f := ApplyNaturalTransformation( nat, Source( f ) );
  nat_range_f := ApplyNaturalTransformation( nat, Range( f ) );

  return [ IsCongruentForMorphisms( PreCompose( F_f, nat_range_f ), PostCompose( G_f, nat_source_f ) ), nat_source_f, nat_range_f ];

end;



 #L_cospan := List( [ u .. v-1 ], 
 #            function( i )
 #              local h, v;
 #              h := ApplyFunctor( L, CM^( i - 1 ) )[ -i ];
 #              v := ApplyFunctor( L, CM[ i ] )^( -i - 1 );
 #              return GeneralizedMorphismByCospan( v, h );
 #            end );


