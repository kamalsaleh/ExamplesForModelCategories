#
# ExamplesForModelCategories: Package the provides many example of homotopy categoie Examples for Homotopy categories of Quillen Model categories and functors between them.
#
# This file is a script which compiles the package manual.
#
if fail = LoadPackage("AutoDoc", "2018.02.14") then
    Error("AutoDoc version 2018.02.14 or newer is required.");
fi;

AutoDoc( rec( scaffold := true, autodoc := true ) );
