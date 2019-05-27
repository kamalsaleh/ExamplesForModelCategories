##
InstallMethodWithCrispCache( BasisBetweenTwistedStructureSheavesAsQuiverRepresentations, 
    [ IsQuiverAlgebra, IsInt, IsInt, IsInt ],
    function( A, i, u, v )
    local n, projectives, twists_of_projectives, u_index, v_index, hom, current_L, current_K, p, \
    L, d, indices, S, current_mor, cokernel_proj, previous_hom, summands, current_hom, t, index; 
    
    #Print( "Computing Basis for: ", i,",", u,",", v, "\n" );
    if i <> -1 then
        return BasisBetweenTwistedStructureSheavesAsQuiverRepresentations( A, -1, u-i-1, v-i-1 );
    fi;

    n := NumberOfVertices( QuiverOfAlgebra( A ) );
    projectives := ShallowCopy( IndecProjRepresentations( A ) );
    twists_of_projectives := Reversed( [ i - n + 1 .. i ] );
    Sort( projectives, function(a,b) 
                        return DimensionVector(a)[n]>DimensionVector(b)[n]; 
                        end );
    if u = i-1 and v = i then
        return BasisOfExternalHom( projectives[ 2 ], projectives[ 1 ] );
    fi;

    if u > v then
        return [ ];
    fi;

    if ForAll( [ u, v ], j -> j in twists_of_projectives ) then
        if u = v then
            return [ IdentityMorphism( projectives[ Position( twists_of_projectives, u ) ] ) ];
        fi;
        if v - u = 1 then
            u_index := Position( twists_of_projectives, u );
            v_index := Position( twists_of_projectives, v );
            current_hom := BasisOfExternalHom( projectives[ u_index ], projectives[ v_index ] );
            hom := [ current_hom[ 1 ] ];
            for t in [ 2 .. n ] do
                current_L := BasisBetweenTwistedStructureSheavesAsQuiverRepresentations( A, i, u + 1, v + 1 );
                current_K := List( current_L, l -> PreCompose( hom[1], l ) );
                p := Position( current_K, PreCompose( current_hom[t], current_L[1] ) );
                if p = fail then
                    Error( "This should not happen!" );
                fi;
                hom[p] := current_hom[t];
            od;
            return hom;
        fi;
        L := List( [ u .. v - 1 ], j -> BasisBetweenTwistedStructureSheavesAsQuiverRepresentations( A, i, j, j + 1 ) );
        d := v - u;
        indices := Combinations( [ 1 .. n + d - 1 ], d );
        indices := List( indices, index -> index - [ 0 .. d ] );

        return List( indices, index -> 
        PreCompose( List( [ 1 .. d ], k -> L[k][index[k]]) ) );        
    fi;

    if v > i then
        S := UnderlyingHomalgGradedPolynomialRing( A );
        current_mor := PositiveKoszulChainMorphism( S, v );
        current_mor := Source( current_mor )^1;
        L := MORPHISM_OF_TWISTED_STRUCTURE_SHEAVES_AS_LIST_OF_RECORDS( current_mor );
        L := List( L, l -> List( l, r -> RECORD_TO_MORPHISM_OF_TWISTED_STRUCTURE_SHEAVES_AS_QUIVER_REPS(A,-1,r) ) );
        current_mor := MorphismBetweenDirectSums( L );
        cokernel_proj := CokernelProjection( current_mor );
        if u = v then
            return [ IdentityMorphism( Range( cokernel_proj ) ) ];
        fi;
        if v = u + 1 then
            previous_hom := BasisBetweenTwistedStructureSheavesAsQuiverRepresentations( A, i, u-1, v-1 );
            summands := List( [ 1 .. n ], k -> Range( previous_hom[ 1 ] ) );
            return List( [ 1 .. n ], k -> PreCompose( InjectionOfCofactorOfDirectSum( summands, k ), cokernel_proj ) );
        fi;

        L := List( [ u .. v - 1 ], j -> BasisBetweenTwistedStructureSheavesAsQuiverRepresentations( A, i, j, j + 1 ) );
        d := v - u;

        indices := Combinations( [ 1 .. n + d - 1 ], d );
        indices := List( indices, index -> index - [ 0 .. d ] );

        return List( indices, index -> 
        PreCompose( List( [ 1 .. d ], k -> L[k][index[k]]) ) );
    fi;

    if u < i - n then

        if v - u = 1 then
            Error( "?" );
        fi;

    fi;

    Error( "??" );
end );

InstallMethodWithCache( BasisBetweenTwistedCotangentSheavesAsQuiverRepresentations, 
        "this should return the basis of Hom( p_i, p_j )",
        [ IsQuiverAlgebra, IsInt, IsInt ],
    function( A, i, j )
    local G, n, index, combinations, L, projectives, cat;
    if i<j then
        return [ ];
    fi;
    
    projectives := Reversed( IndecProjRepresentations( A ) );
    cat := CapCategory( projectives[ 1 ] );

    n := Length( projectives );

    if i = infinity and j = infinity then
        return ZeroObjectFunctorial( cat );
    elif i = infinity then
        return ZeroMorphism( ZeroObject( cat ), projectives[ n - j ] );
    elif j = infinity then
        return ZeroMorphism( projectives[ n - i ], ZeroObject( cat ) );
    fi;

    if i = j then
        return [ IdentityMorphism( projectives[ n - i ] ) ];
    fi;

    G := LIST_OF_MORPHISMS_BETWEEN_TWISTED_COTANGENT_BUNDLES_AS_QUIVER_REPS( A );
    
    index := n - i;

    combinations := Combinations( [ 1 .. n ], i - j );
    L := List( combinations, comb -> List( [ 1 .. i - j ], k-> G[index+k-1][comb[k]] ) );
    return List( L, l -> PreCompose(l) );
end );

InstallMethod( TwistedStructureSheafAsQuiverRepresentation, 
    [ IsQuiverAlgebra, IsInt, IsInt ],
    function( A, i, u )
    return Source( BasisBetweenTwistedStructureSheavesAsQuiverRepresentations( A, i, u, u )[ 1 ] );
end );

InstallMethod( TwistedCotangentSheafAsQuiverRepresentationOp, 
    [ IsQuiverAlgebra, IsInt ],
    function( A, u )
    return Source( BasisBetweenTwistedCotangentSheavesAsQuiverRepresentations( A, u, u )[ 1 ] );
end );

InstallMethod( CotangentBeilinsonFunctor,
    [ IsQuiverAlgebra ],
    function( A )
    local S, graded_lp_cat_sym, chains_graded_lp_cat_sym, quiver_reps, chains_quiver_reps,
    homotopy_cat, name, F;
    S := UnderlyingHomalgGradedPolynomialRing( A );
    graded_lp_cat_sym := GradedLeftPresentations( S );
    chains_graded_lp_cat_sym := ChainComplexCategory( graded_lp_cat_sym );
    quiver_reps := CategoryOfQuiverRepresentations( A );
    chains_quiver_reps := ChainComplexCategory( quiver_reps );
    homotopy_cat := HomotopyCategory( chains_quiver_reps );
    name := Concatenation( "Cotangent Beilinson functor from ", Name( chains_graded_lp_cat_sym ),
    " to ", Name( homotopy_cat ) );
    F := CapFunctor( name, chains_graded_lp_cat_sym, homotopy_cat );
    AddObjectFunction( F,
        function( C )
        local TC, n, diff, diffs, rep, L, obj;
        TC := TateResolution( C );
        n := Length( IndeterminatesOfPolynomialRing( S ) );
        diff := function(i)
            if i> ActiveUpperBound(C)+n-1 or i<= ActiveLowerBound(C)-n+1 then
                return ZeroObjectFunctorial( quiver_reps );
            else
                L := MORPHISM_OF_TWISTED_OMEGA_MODULES_AS_LIST_OF_RECORDS( TC^i );
                return LIST_OF_RECORDS_TO_MORPHISM_OF_TWISTED_COTANGENT_SHEAVES_AS_QUIVER_REPS( A, L );
            fi;
            end;
        diffs := MapLazy( IntegersList, diff, 1 );
        rep := ChainComplex( quiver_reps, diffs );
        SetUpperBound( rep, ActiveUpperBound(C)+n-1 );
        SetLowerBound( rep, ActiveLowerBound(C)-n+1 );
        obj := AsObjectInHomotopyCategory( rep );
        SetUnderlyingReplacement( obj, rep );
        return obj;
    end );
    
    AddMorphismFunction( F,
        function( source, phi, range )
        local rep_source, rep_range, Tphi, mor, mors, rep, L, u, l;
        Tphi := TateResolution( phi );
        rep_source := UnderlyingReplacement( source );
        rep_range :=  UnderlyingReplacement( range );
        l := Maximum( ActiveLowerBound( rep_source ), ActiveLowerBound( rep_range ) );
        u := Minimum( ActiveUpperBound( rep_source ), ActiveUpperBound( rep_range ) );
        mor :=  function( i )
            if i>=u or i<=l then
                return ZeroMorphism( rep_source[i], rep_range[i] );
            else
                L := MORPHISM_OF_TWISTED_OMEGA_MODULES_AS_LIST_OF_RECORDS( Tphi[i] );
                return LIST_OF_RECORDS_TO_MORPHISM_OF_TWISTED_COTANGENT_SHEAVES_AS_QUIVER_REPS( A, L );
            fi;
            end;
        mors := MapLazy( IntegersList, mor, 1 );
        rep := ChainMorphism( rep_source, rep_range, mors );
        return AsMorphismInHomotopyCategoryByReplacement( rep_source, rep, rep_range );
        end );
    return F;
end );

BindGlobal( "_CotangentBeilinsonFunctorFromChains",
#    [ IsQuiverAlgebra ],
    function( A )
    local S, graded_lp_cat_sym, chains_graded_lp_cat_sym, quiver_reps, chains_quiver_reps,
    homotopy_cat, name, F;
    
    S := UnderlyingHomalgGradedPolynomialRing( A );
    
    graded_lp_cat_sym := GradedLeftPresentations( S );
    
    chains_graded_lp_cat_sym := ChainComplexCategory( graded_lp_cat_sym );
    
    quiver_reps := CategoryOfQuiverRepresentations( A );
    
    chains_quiver_reps := ChainComplexCategory( quiver_reps );
    
    homotopy_cat := HomotopyCategory( quiver_reps );
    
    name := Concatenation( "Cotangent Beilinson functor from ", Name( chains_graded_lp_cat_sym ), " to ", Name( homotopy_cat ) );
    
    F := CapFunctor( name, chains_graded_lp_cat_sym, homotopy_cat );
    
    AddObjectFunction( F,
      function( C )
        local TC, n, diff, diffs, rep, L, obj;
        
        TC := TateResolution( C );
        
        n := Length( IndeterminatesOfPolynomialRing( S ) );
        
        diff := function(i)
        
            if i > ActiveUpperBound(C) + n - 1 or i <= ActiveLowerBound( C ) - n + 1 then
              
              return ZeroObjectFunctorial( quiver_reps );
            
            else
              
              L := MORPHISM_OF_TWISTED_OMEGA_MODULES_AS_LIST_OF_RECORDS( TC^i );
              
              return LIST_OF_RECORDS_TO_MORPHISM_OF_TWISTED_COTANGENT_SHEAVES_AS_QUIVER_REPS( A, L );
              
            fi;
          
        end;
        
        diffs := MapLazy( IntegersList, diff, 1 );
        
        rep := ChainComplex( quiver_reps, diffs );
        
        SetUpperBound( rep, ActiveUpperBound( C ) + n - 1 );
        
        SetLowerBound( rep, ActiveLowerBound( C ) - n + 1 );
        
        obj := HomotopyCategoryObject( homotopy_cat, rep );
        
        return obj;
        
    end );
    
    AddMorphismFunction( F,
    
      function( source, phi, range )
        local rep_source, rep_range, Tphi, mor, mors, rep, L, u, l;
        
        Tphi := TateResolution( phi );
        
        rep_source := source;
        
        rep_range := range;
        
        l := Maximum( ActiveLowerBound( rep_source ), ActiveLowerBound( rep_range ) );
        
        u := Minimum( ActiveUpperBound( rep_source ), ActiveUpperBound( rep_range ) );
        
        mor :=  function( i )
        
            if i>=u or i<=l then
              
                return ZeroMorphism( rep_source[ i ], rep_range[ i ] );
                
            else
              
              L := MORPHISM_OF_TWISTED_OMEGA_MODULES_AS_LIST_OF_RECORDS( Tphi[ i ] );
              
              return LIST_OF_RECORDS_TO_MORPHISM_OF_TWISTED_COTANGENT_SHEAVES_AS_QUIVER_REPS( A, L );
              
            fi;
            
          end;
        
        mors := MapLazy( IntegersList, mor, 1 );
        
        rep := ChainMorphism( rep_source, rep_range, mors );
        
        return HomotopyCategoryMorphism( homotopy_cat, rep );
        
        end );
    
    return F;
    
end );

BindGlobal( "_CotangentBeilinsonFunctor",
#    [ IsQuiverAlgebra ],
    function( A )
    local S, graded_lp_cat_sym, quiver_reps, chains_quiver_reps, homotopy_cat, name, F;
    
    S := UnderlyingHomalgGradedPolynomialRing( A );
    
    graded_lp_cat_sym := GradedLeftPresentations( S );
    
    quiver_reps := CategoryOfQuiverRepresentations( A );
    
    homotopy_cat := HomotopyCategory( quiver_reps );
    
    name := Concatenation( "Cotangent Beilinson functor from ", Name( graded_lp_cat_sym ), " to ", Name( homotopy_cat ) );
    
    F := CapFunctor( name, graded_lp_cat_sym, homotopy_cat );
    
    AddObjectFunction( F,
      function( C )
        local TC, n, diff, diffs, rep, L, obj;
        
        TC := TateResolution( C );
        
        n := Length( IndeterminatesOfPolynomialRing( S ) );
        
        diff := function(i)
        
            if i > n or i <= - n then
              
              return ZeroObjectFunctorial( quiver_reps );
            
            else
              
              L := MORPHISM_OF_TWISTED_OMEGA_MODULES_AS_LIST_OF_RECORDS( TC^i );
              
              return LIST_OF_RECORDS_TO_MORPHISM_OF_TWISTED_COTANGENT_SHEAVES_AS_QUIVER_REPS( A, L );
              
            fi;
          
        end;
        
        diffs := MapLazy( IntegersList, diff, 1 );
        
        rep := ChainComplex( quiver_reps, diffs );
        
        SetUpperBound( rep, n );
        
        SetLowerBound( rep, -n );
        
        obj := HomotopyCategoryObject( homotopy_cat, rep );
        
        return obj;
        
    end );
    
    AddMorphismFunction( F,
    
      function( source, phi, range )
        local rep_source, rep_range, Tphi, mor, mors, rep, L, u, l;
        
        Tphi := TateResolution( phi );
        
        rep_source := UnderlyingCapCategoryObject( source );
        
        rep_range := UnderlyingCapCategoryObject( range );
        
        l := Maximum( ActiveLowerBound( rep_source ), ActiveLowerBound( rep_range ) );
        
        u := Minimum( ActiveUpperBound( rep_source ), ActiveUpperBound( rep_range ) );
        
        mor :=  function( i )
        
            if i>=u or i<=l then
              
                return ZeroMorphism( rep_source[ i ], rep_range[ i ] );
                
            else
              
              L := MORPHISM_OF_TWISTED_OMEGA_MODULES_AS_LIST_OF_RECORDS( Tphi[ i ] );
              
              return LIST_OF_RECORDS_TO_MORPHISM_OF_TWISTED_COTANGENT_SHEAVES_AS_QUIVER_REPS( A, L );
              
            fi;
            
          end;
        
        mors := MapLazy( IntegersList, mor, 1 );
        
        rep := ChainMorphism( rep_source, rep_range, mors );
        
        return HomotopyCategoryMorphism( homotopy_cat, rep );
        
        end );
    
    return F;
    
end );

##
DeclareAttribute( "_TwistedCotangentSheavesToProjectiveQuiverRepsFunctor", IsQuiverAlgebra );

InstallMethod( _TwistedCotangentSheavesToProjectiveQuiverRepsFunctor,
  [ IsQuiverAlgebra ],
  function( A )
    local S, quivers, graded_lp_cat, F;
  
    S := UnderlyingHomalgGradedPolynomialRing( A );
  
    quivers := CategoryOfQuiverRepresentations( A );
    graded_lp_cat := GradedLeftPresentations( S );
  
    F := CapFunctor( "to be named", graded_lp_cat, quivers );
  
    AddObjectFunction( F,
      function( M )
        local h;
      
        h := UniversalMorphismIntoZeroObject( M );
      
        h := MORPHISM_OF_TWISTED_COTANGENT_SHEAVES_AS_LIST_OF_RECORDS( h );
      
        h := LIST_OF_RECORDS_TO_MORPHISM_OF_TWISTED_COTANGENT_SHEAVES_AS_QUIVER_REPS( A, h );
      
        return Source( h );
      
      end );
  
    AddMorphismFunction( F,
      function( s, phi, r )
        local h;
       
        h := MORPHISM_OF_TWISTED_COTANGENT_SHEAVES_AS_LIST_OF_RECORDS( phi );
      
        h := LIST_OF_RECORDS_TO_MORPHISM_OF_TWISTED_COTANGENT_SHEAVES_AS_QUIVER_REPS( A, h );
      
        return h;
      
      end );
  
    return F;
  
end );

##
DeclareAttribute( "_ProjectiveQuiverRepsToTwistedCotangentSheavesFunctor", IsQuiverAlgebra );

InstallMethod( _ProjectiveQuiverRepsToTwistedCotangentSheavesFunctor,
  [ IsQuiverAlgebra ],
  function( A )
    local S, quivers, graded_lp_cat, F;
  
    S := UnderlyingHomalgGradedPolynomialRing( A );
  
    quivers := CategoryOfQuiverRepresentations( A );
    graded_lp_cat := GradedLeftPresentations( S );
  
    F := CapFunctor( "to be named", quivers, graded_lp_cat );
  
    AddObjectFunction( F,
      function( M )
        local h;
      
        h := UniversalMorphismIntoZeroObject( M );
      
        h := MORPHISM_OF_PROJECTIVE_QUIVER_REPS_AS_LIST_OF_RECORDS( h );
      
        h := LIST_OF_RECORDS_TO_MORPHISM_OF_TWISTED_COTANGENT_SHEAVES( S, h );
      
        return Source( h );
      
      end );
  
    AddMorphismFunction( F,
      function( s, phi, r )
        local h;
       
        h := MORPHISM_OF_PROJECTIVE_QUIVER_REPS_AS_LIST_OF_RECORDS( phi );
      
        h := LIST_OF_RECORDS_TO_MORPHISM_OF_TWISTED_COTANGENT_SHEAVES( S, h );
      
        return h;
      
      end );
  
    return F;
  
end );

InstallMethod( StructureBeilinsonFunctor,
    [ IsQuiverAlgebra ],
    function( A )
    local S, graded_lp_cat_sym, chains_graded_lp_cat_sym, quiver_reps, chains_quiver_reps,
    homotopy_cat, name, F;
    S := UnderlyingHomalgGradedPolynomialRing( A );
    graded_lp_cat_sym := GradedLeftPresentations( S );
    chains_graded_lp_cat_sym := ChainComplexCategory( graded_lp_cat_sym );
    quiver_reps := CategoryOfQuiverRepresentations( A );
    chains_quiver_reps := ChainComplexCategory( quiver_reps );
    homotopy_cat := HomotopyCategory( chains_quiver_reps );
    name := Concatenation( "Structure Beilinson functor from ", Name( chains_graded_lp_cat_sym ),
    " to ", Name( homotopy_cat ) );
    F := CapFunctor( name, chains_graded_lp_cat_sym, homotopy_cat );
    AddObjectFunction( F,
        function( C )
        local B, diff, diffs, rep, obj;
        B := BeilinsonReplacement( C );
        B := CofibrantModel( B );
        diff := function(i)
                local L;
            if i> ActiveUpperBound( B ) or i<= ActiveLowerBound(B) then
                return ZeroObjectFunctorial( quiver_reps );
            else
                L := MORPHISM_OF_TWISTED_STRUCTURE_SHEAVES_AS_LIST_OF_RECORDS( B^i );
                return LIST_OF_RECORDS_TO_MORPHISM_OF_TWISTED_STRUCTURE_SHEAVES_AS_QUIVER_REPS( A, 0, L );
            fi;
            end;
        diffs := MapLazy( IntegersList, diff, 1 );
        rep := ChainComplex( quiver_reps, diffs );
        SetUpperBound( rep, ActiveUpperBound( B ) );
        SetLowerBound( rep, ActiveLowerBound( B ) );
        obj := AsObjectInHomotopyCategory( rep );
        SetUnderlyingReplacement( obj, rep );
        return obj;
    end );
    
    AddMorphismFunction( F,
        function( source, phi, range )
        local rep_source, rep_range, mor, mors, rep, L, u, l, B;
        B := BeilinsonReplacement( phi );
        B := MorphismBetweenCofibrantModels( B );
        rep_source := UnderlyingReplacement( source );
        rep_range :=  UnderlyingReplacement( range );
        l := Maximum( ActiveLowerBound( rep_source ), ActiveLowerBound( rep_range ) );
        u := Minimum( ActiveUpperBound( rep_source ), ActiveUpperBound( rep_range ) );
        mor :=  function( i )
            if i>=u or i<=l then
                return ZeroMorphism( rep_source[i], rep_range[i] );
            else
                L := MORPHISM_OF_TWISTED_STRUCTURE_SHEAVES_AS_LIST_OF_RECORDS( B[i] );
                return LIST_OF_RECORDS_TO_MORPHISM_OF_TWISTED_STRUCTURE_SHEAVES_AS_QUIVER_REPS( A, 0, L );
            fi;
            end;
        mors := MapLazy( IntegersList, mor, 1 );
        rep := ChainMorphism( rep_source, rep_range, mors );
        return AsMorphismInHomotopyCategoryByReplacement( rep_source, rep, rep_range );
        end );
    return F;
end );

BindGlobal( "ALLOWED_INDICES_FOR_STRUCTURE_BEILINSON_ALGEBRA",
    function( A, i )
    local n,j;
    n := NumberOfVertices( QuiverOfAlgebra( A ) );
    for j in [ 1 .. n ] do
    	if j <> n then
    		if j = 1 then 
    	    	Print( "O(", i, ") <--", String( n ), "-- " );
    		else
    	    	Print( "O(", i-j+1, ") <--", String( n ), "-- " );
    		fi;
    	else
    	    Print( "O(", i-j+1, ")\n" );
    	fi;
    od;
end );

BindGlobal( "ALLOWED_INDICES_FOR_COTANGENT_BEILINSON_ALGEBRA",
    function( A )
    local n, s, i;
    n := NumberOfVertices( QuiverOfAlgebra( A ) ) - 1;
    s := "";
    for i in [ 0 .. n ] do
        if i <> n then
            s := Concatenation(s, "𝛀 ^", String(i), "(", String(i), ") <--",String( n + 1 ),"-- " );
        else
            s := Concatenation( s, "𝛀 ^", String(i), "(", String(i), ")" );
        fi;
    od;
    Print( s, "\n" );
end );

