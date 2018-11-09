#
# ExamplesForModelCategories: Package the provides many example of homotopy categoie Examples for Homotopy categories of Quillen Model categories and functors between them.
#
# This file contains package meta data. For additional information on
# the meaning and correct usage of these fields, please consult the
# manual of the "Example" package as well as the comments in its
# PackageInfo.g file.
#
SetPackageInfo( rec(

PackageName := "ExamplesForModelCategories",
Subtitle := "Package the provides many example of homotopy categoie Examples for Homotopy categories of Quillen Model categories and functors between them.",
Version := "0.1",
Date := "01/11/2018", # dd/mm/yyyy format

Persons := [
  rec(
    IsAuthor := true,
    IsMaintainer := true,
    FirstNames := "Kamal",
    LastName := "Saleh",
    WWWHome := "https://github.com/kamalsaleh/",
    Email := "kamal.saleh@uni-siegen.de",
    PostalAddress := "Walterfelx 3 ",
    Place := "Siegen",
    Institution := "University of Siegen",
  ),
],

SourceRepository := rec(
    Type := "git",
    URL := "https://github.com/kamalsaleh/ExamplesForModelCategories",
),
IssueTrackerURL := Concatenation( ~.SourceRepository.URL, "/issues" ),
PackageWWWHome  := "https://kamalsaleh.github.io/ExamplesForModelCategories/",
PackageInfoURL  := Concatenation( ~.PackageWWWHome, "PackageInfo.g" ),
README_URL      := Concatenation( ~.PackageWWWHome, "README.md" ),
ArchiveURL      := Concatenation( ~.SourceRepository.URL,
                                 "/releases/download/v", ~.Version,
                                 "/", ~.PackageName, "-", ~.Version ),

ArchiveFormats := ".tar.gz",

##  Status information. Currently the following cases are recognized:
##    "accepted"      for successfully refereed packages
##    "submitted"     for packages submitted for the refereeing
##    "deposited"     for packages for which the GAP developers agreed
##                    to distribute them with the core GAP system
##    "dev"           for development versions of packages
##    "other"         for all other packages
##
Status := "dev",

AbstractHTML   :=  "",

PackageDoc := rec(
  BookName  := "ExamplesForModelCategories",
  ArchiveURLSubset := ["doc"],
  HTMLStart := "doc/chap0.html",
  PDFFile   := "doc/manual.pdf",
  SixFile   := "doc/manual.six",
  LongTitle := "Package the provides many example of homotopy categoie Examples for Homotopy categories of Quillen Model categories and functors between them.",
),

Dependencies := rec(
  GAP := ">= 4.9",
  NeededOtherPackages := [
  [ "BBGG", ">= 0" ],
  [ "GradedModulePresentationsForCAP", ">= 0" ],
	[ "ModelCategories", " >= 2017.07.01" ],
	[ "QPA", ">= 2.0-dev" ],
  [ "GradedModules", ">= 0" ],
  [ "StableCategoriesForCAP", ">= 0" ],
	],
  SuggestedOtherPackages := [ ],
  ExternalConditions := [ ],
),

AvailabilityTest := ReturnTrue,

TestFile := "tst/testall.g",

#Keywords := [ "TODO" ],

));
