{-# LANGUAGE TemplateHaskell #-}
{- |
   Module     : SealModule
   Copyright  : Copyright (C) 2010 Joachim Breitner
   License    : BSD3

   Maintainer : Joachim Breitner <mail@joachim-breitner.de>
   Stability  : experimental
   Portability: portable


This provides a Template Haskell function to convert a set of function
declarations which use global constants into function declarations that take
these constants as parameters.

The goal is to make it more convenient to write pure, non-monadic code that
deep in the call stack requires some configuration data without having to
pass these paramters around explicitly.
-}

module SealModule (
-- * Example
-- $example

-- * Record Wildcards
-- $rec

-- * API
    sealedParam,
    sealModule

-- * Problems
-- $problems
    )
where

import Language.Haskell.TH
import Control.Applicative ((<$>))

import Data.Maybe
import Debug.Trace
import Control.Monad

-- | 'sealedParam' turns a toplevel declaration into a sealed parameter. It
-- must only be used inside a call to 'sealModule' and there only in the form
-- of a top level declaration of the form
--
-- @
-- name = sealedParam
-- @
--
-- A type signature for @name@ may be given, and is a prerequisite for the
-- generated functions having type signatures.
sealedParam :: a
sealedParam = error "sealedParam used outside of sealModule or used incorrectly inside"

-- | 'sealModule' modifies the passed top level declarations to have additional
-- parameters for each declaration bound to 'sealedParam', in the order of
-- their appearance. The parameter declarations and their type signature, if
-- present, are removed from the list of declarations.
--
-- The generated functions will have a type signature if and only they have a
-- type signature and all parameters have type signatures.
sealModule :: Q [Dec] -> Q [Dec]
sealModule declQ = do
    comb <- newName "mod"
    decl <- declQ
    let paramNames = findParamName decl

    let real = filter (\dec -> not (any (\name -> dec `defines` name) paramNames)) decl
    let definedNames = findDefinedNames real

    fn <- funD comb [
            clause (map varP paramNames)
                   (normalB (tupE (map (return . VarE) definedNames)))
                   (map return real)
            ]
    let types = case findParamTypes paramNames decl of
                    Nothing -> []
                    Just paramTypes -> mapMaybe (prependType paramTypes) real

    accessors <- forM definedNames $ \name ->
        funD name [
            clause (map varP paramNames)
                   (normalB (letE
                        [valD (tupP (map varP definedNames))
                              (normalB (appsE (map varE (comb : paramNames ))))
                              []
                        ]
                        (varE name)))
                    []
            ]
    return $ [fn] ++ types ++ accessors

findParamName :: [Dec] -> [Name]
findParamName = mapMaybe go
  where go (ValD (VarP name) (NormalB (VarE arg)) []) | arg == 'sealedParam 
            = Just name
        go (ValD (AsP name _) (NormalB (VarE arg)) []) | arg == 'sealedParam 
            = Just name
        go x = Nothing

findParamTypes :: [Name] -> [Dec] -> Maybe [Type]
findParamTypes [] _ = Just []
findParamTypes _ [] = Nothing
findParamTypes (n:ns) (SigD n' t:ds) | n == n' = (t:) <$> findParamTypes ns ds
findParamTypes ns (_:ds) = findParamTypes ns ds

findDefinedNames :: [Dec] -> [Name]
findDefinedNames = mapMaybe go
  where go (ValD (VarP name) _ _)  = Just name
        go (FunD name        _ )   = Just name
        go x = Nothing

defines :: Dec -> Name -> Bool
defines (FunD name' _) name = name == name'
defines (SigD name' _) name = name == name'
defines (ValD (VarP name') _ _) name = name == name'
defines _ _ = False

prependType :: [Type] -> Dec -> Maybe Dec
prependType typs (SigD name typ) = Just (SigD name (foldr arrow typ typs))
  where arrow t1 t2 = AppT (AppT ArrowT t1) t2
prependType _ _ = Nothing

{- $example
Consider the following minimal example:

@
\{\-\# LANGUAGE TemplateHaskell \#\-\}
@

>module Example1 where
>import SealModule
>import Control.Monad
>
>sealModule [d|
>    verbose :: Bool
>    verbose = sealedParam
>    
>    worker :: Int -> IO Int
>    worker n = do
>        when verbose $ putStrLn $ "Got " ++ show n
>        return $ Suc n
>    |]

The function @verbose@ will be removed from the module, and the function
@worker@ will be equivalent to

>worker :: Bool -> Int -> IO Int
>worker verbose n = do
>    when verbose $ putStrLn $ "Got " ++ show n
>    return $ Suc n

This also works if @worker@ had called @foo@, @foo@ had called @bar@ and only
@bar@ would use the configuration parameter @verbose@.
-}


{- $rec
'sealModule' supports more than one 'sealedParam', they are added to the
paramter list in the order in which they appear in the declaration list. But if
you want to be able to conveniently add further parameters without changing the
functions' signature, you can use record wildcards:

@
\{\-\# LANGUAGE TemplateHaskell, RecordWildCards #\-\}
@

>module Example2 where
>import SealModule
>import Control.Monad
>
>data Config = Config { verbose :: Bool, increment :: Int }
>
>sealModule [d|
>    config :: Config
>    config = sealedParam
>    Config{..} = config
>
>    worker :: Int -> IO Int
>    worker n = do
>        when verbose $ putStrLn $ "Got " ++ show n
>        return $ n + increment
>    |]

This way, the fields of the @Config@ record appear as top-level declarations
inside the sealed module. Each function is exposed with one additional
parameter of type @Config@. If you later need an additional configuration value
anywhere in the module, all you have to do is add it to the @Config@ record
data type. No function signatures change this way.
-}

{- $problems
 * The code passed to 'sealModule' has to be indented.

 * Although the modified functions will apear in haddock documentation if they
   and all parameters have type signatures, Haddock annotations inside
   'sealModule' are lost. A work around is the approach shown in the following
   listing. It is important that no type signature is given inside the
   'sealModule', otherwise the compiler will complain about duplicate type
   signatures, and that the signatures are given after 'sealModule'.

@
\{\-\# LANGUAGE TemplateHaskell \#\-\}
@

>module Example1 where
>import SealModule
>import Control.Monad
>
>sealModule [d|
>    verbose :: Bool
>    verbose = sealedParam
>
>    worker n = do
>        when verbose $ putStrLn $ "Got " ++ show n
>        return $ Suc n
>    |]
>
>-- | This is the documentation for 'worker'.
>worker :: Bool -> Int -> IO Int
-}

