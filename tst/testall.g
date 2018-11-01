#
# ExamplesForModelCategories: Package the provides many example of homotopy categoie Examples for Homotopy categories of Quillen Model categories and functors between them.
#
# This file runs package tests. It is also referenced in the package
# metadata in PackageInfo.g.
#
LoadPackage( "ExamplesForModelCategories" );

TestDirectory(DirectoriesPackageLibrary( "ExamplesForModelCategories", "tst" ),
  rec(exitGAP := true));

FORCE_QUIT_GAP(1); # if we ever get here, there was an error
