module ParsePackage

import Derive.Prelude
import Data.List1
import Package
import Text.ILex

%default total
%language ElabReflection

public export
data PkgVersion = MkPkgVersion (List1 Nat)

public export
record PkgVersionBounds where
  constructor MkPkgVersionBounds
  lowerBound : Maybe PkgVersion
  lowerInclusive : Bool -- >= if true
  upperBound : Maybe PkgVersion
  upperInclusive : Bool -- <= if true

-- public export
-- data DescField  : Type where
--   PVersion      : PkgVersion -> DescField
--   PLangVersions : PkgVersionBounds -> DescField
--   PVersionDep   : String -> DescField
--   PAuthors      : String -> DescField
--   PMaintainers  : String -> DescField
--   PLicense      : String -> DescField
--   PBrief        : String -> DescField
--   PReadMe       : String -> DescField
--   PHomePage     : String -> DescField
--   PSourceLoc    : String -> DescField
--   PBugTracker   : String -> DescField
--   PDepends      : List Depends -> DescField
--   PModules      : List ModuleIdent -> DescField
--   PMainMod      : ModuleIdent -> DescField
--   PExec         : String -> DescField
--   POpts         : String -> DescField
--   PSourceDir    : String -> DescField
--   PBuildDir     : String -> DescField
--   POutputDir    : String -> DescField
--   PPrebuild     : String -> DescField
--   PPostbuild    : String -> DescField
--   PPreinstall   : String -> DescField
--   PPostinstall  : String -> DescField
--   PPreclean     : String -> DescField
--   PPostclean    : String -> DescField

-- field : String -> Rule DescField
-- field fname
--       = strField PAuthors "authors"
--     <|> strField PMaintainers "maintainers"
--     <|> strField PLicense "license"
--     <|> strField PBrief "brief"
--     <|> strField PReadMe "readme"
--     <|> strField PHomePage "homepage"
--     <|> strField PSourceLoc "sourceloc"
--     <|> strField PBugTracker "bugtracker"
--     <|> strField POpts "options"
--     <|> strField POpts "opts"
--     <|> strField PSourceDir "sourcedir"
--     <|> strField PBuildDir "builddir"
--     <|> strField POutputDir "outputdir"
--     <|> strField PPrebuild "prebuild"
--     <|> strField PPostbuild "postbuild"
--     <|> strField PPreinstall "preinstall"
--     <|> strField PPostinstall "postinstall"
--     <|> strField PPreclean "preclean"
--     <|> strField PPostclean "postclean"
--     <|> do start <- location
--            ignore $ exactProperty "version"
--            mustWork $ do
--              equals
--              vs <- choose stringLit (sepBy1 dot' integerLit)
--              end <- location
--              the (EmptyRule _) $ case vs of
--                 Left v   => pure (PVersionDep (MkFC (PhysicalPkgSrc fname) start end) v)
--                 Right vs => pure (PVersion (MkFC (PhysicalPkgSrc fname) start end)
--                                     (MkPkgVersion (fromInteger <$> vs)))
--     <|> do start <- location
--            ignore $ exactProperty "langversion"
--            mustWork $ do
--              lvs <- langversions
--              end <- location
--              pure (PLangVersions (MkFC (PhysicalPkgSrc fname) start end) lvs)
--     <|> do start <- location
--            ignore $ exactProperty "version"
--            mustWork $ do
--              equals
--              v <- stringLit
--              end <- location
--              pure (PVersionDep (MkFC (PhysicalPkgSrc fname) start end) v)
--     <|> do ignore $ exactProperty "depends"
--            mustWork $ do
--              equals
--              ds <- sep depends
--              pure (PDepends ds)
--     <|> do ignore $ exactProperty "modules"
--            mustWork $ do
--              equals
--              ms <- sep (do start <- location
--                            m <- moduleIdent
--                            end <- location
--                            pure (MkFC (PhysicalPkgSrc fname) start end, m))
--              pure (PModules ms)
--     <|> do ignore $ exactProperty "main"
--            mustWork $ do
--              equals
--              start <- location
--              m <- moduleIdent
--              end <- location
--              pure (PMainMod (MkFC (PhysicalPkgSrc fname) start end) m)
--     <|> do ignore $ exactProperty "executable"
--            mustWork $ do
--              equals
--              e <- (stringLit <|> packageName)
--              pure (PExec e)
--   where
--     data Bound = LT PkgVersion Bool | GT PkgVersion Bool
--
--     bound : Rule (List Bound)
--     bound
--         = do lte
--              vs <- sepBy1 dot' integerLit
--              pure [LT (MkPkgVersion (fromInteger <$> vs)) True]
--       <|> do gte
--              vs <- sepBy1 dot' integerLit
--              pure [GT (MkPkgVersion (fromInteger <$> vs)) True]
--       <|> do lt
--              vs <- sepBy1 dot' integerLit
--              pure [LT (MkPkgVersion (fromInteger <$> vs)) False]
--       <|> do gt
--              vs <- sepBy1 dot' integerLit
--              pure [GT (MkPkgVersion (fromInteger <$> vs)) False]
--       <|> do eqop
--              vs <- sepBy1 dot' integerLit
--              pure [LT (MkPkgVersion (fromInteger <$> vs)) True,
--                    GT (MkPkgVersion (fromInteger <$> vs)) True]
--
--     mkBound : List Bound -> PkgVersionBounds -> EmptyRule PkgVersionBounds
--     mkBound (LT b i :: bs) pkgbs
--         = maybe (mkBound bs ({ upperBound := Just b,
--                                upperInclusive := i } pkgbs))
--                 (\_ => fail "Dependency already has an upper bound")
--                 pkgbs.upperBound
--     mkBound (GT b i :: bs) pkgbs
--         = maybe (mkBound bs ({ lowerBound := Just b,
--                                lowerInclusive := i } pkgbs))
--                 (\_ => fail "Dependency already has a lower bound")
--                 pkgbs.lowerBound
--     mkBound [] pkgbs = pure pkgbs
--
--     langversions : EmptyRule PkgVersionBounds
--     langversions
--         = do bs <- sepBy andop bound
--              mkBound (concat bs) anyBounds
--
--     depends : Rule Depends
--     depends
--         = do name <- packageName
--              bs <- sepBy andop bound
--              pure (MkDepends name !(mkBound (concat bs) anyBounds))
--
--     strField : (FC -> String -> DescField) -> String -> Rule DescField
--     strField fieldConstructor fieldName
--         = do start <- location
--              ignore $ exactProperty fieldName
--              mustWork $ do
--                equals
--                str <- stringLit
--                end <- location
--                pure $ fieldConstructor (MkFC (PhysicalPkgSrc fname) start end) str
