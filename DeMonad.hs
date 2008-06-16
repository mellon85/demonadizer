module DeMonad 
    (workFile
    ,workModule
    ,workFileToFile) where

import Language.Haskell.Parser
import Language.Haskell.Syntax
import Language.Haskell.Pretty
import IO
import Monad

fakeSrc = SrcLoc "" 0 0

convert workMod = convertHsModule workMod
    where
        monad = head $ filterMonads workMod
        fun_binds  = foldr ((++).(filterFunBind)) [] ((\(HsInstDecl _ _ _ _ x) -> x) monad)
        ret_decls  = filterFunBindsByName "return" fun_binds
        bind_decls = filterFunBindsByName ">>="    fun_binds
        seq_decls  = filterFunBindsByName ">>"     fun_binds
        filterFunBind (HsFunBind xs) = xs
        filterFunBind _ = []
        
        ret_match  = transformListToMatch ret_decls
        bind_match = transformListToMatch bind_decls
        seq_match  = seq_decls
        
        ret_fun  = transformMatchToFunctor ret_match
        bind_fun = transformMatchToFunctor bind_match
        seq_fun  = case seq_match of
                        [] -> (\[f1,f2] -> (HsApp (HsParen  (HsLambda fakeSrc [HsPWildCard] f2)) f1))
                        _  -> transformMatchToFunctor $ transformListToMatch seq_match

        convertHsModule (HsModule x y z w d) = HsModule x y z w (map convertHsDecl d)
        convertHsExp x = case x of
            HsNegApp e            -> HsNegApp $ convertHsExp e
            HsLambda s pats e     -> HsLambda s pats $ convertHsExp e
            HsLet decls e         -> HsLet (map convertHsDecl decls) (convertHsExp e)
            HsIf a b c            -> HsIf (convertHsExp a) (convertHsExp b) (convertHsExp c)
            HsCase a e            -> HsCase (convertHsExp a) (map convertHsAlt e)
            HsTuple a             -> HsTuple $ map convertHsExp a
            HsList a              -> HsList $ map convertHsExp a
            HsParen a             -> HsParen $ convertHsExp a
            HsLeftSection a o     -> HsLeftSection (convertHsExp a) o
            HsRightSection o a    -> HsRightSection o (convertHsExp a)
            HsRecConstr o a       -> HsRecConstr o (map convertHsFieldUpdate a)
            HsRecUpdate a b       -> HsRecUpdate (convertHsExp a) (map convertHsFieldUpdate b)
            HsEnumFrom a          -> HsEnumFrom $ convertHsExp a
            HsEnumFromTo a b      -> HsEnumFromTo (convertHsExp a) (convertHsExp b)
            HsEnumFromThen a b    -> HsEnumFromThen (convertHsExp a) (convertHsExp b)
            HsEnumFromThenTo a b c-> HsEnumFromThenTo (convertHsExp a) (convertHsExp b) (convertHsExp c)
            HsListComp a s        -> HsListComp (convertHsExp a) (map convertHsStmt s)
            HsExpTypeSig s a q    -> HsExpTypeSig s (convertHsExp a) q
            HsAsPat s a           -> HsAsPat s $ convertHsExp a
            HsWildCard            -> HsWildCard
            HsIrrPat a            -> HsIrrPat $ convertHsExp a
            HsApp (HsVar (UnQual (HsIdent "return"))) b -> ret_fun [b]
            HsInfixApp a (HsQVarOp (UnQual (HsSymbol ">>="))) b -> bind_fun [convertHsExp (HsParen b),convertHsExp (HsParen a)]
            HsInfixApp a (HsQVarOp (UnQual (HsSymbol ">>"))) b -> seq_fun [convertHsExp (HsParen a),convertHsExp (HsParen b)]
            HsApp a b         -> (HsApp (convertHsExp a) (convertHsExp b))
            HsInfixApp a o b      -> HsInfixApp (convertHsExp a) o (convertHsExp b)
            HsDo stmts        -> convertHsExp res
                where
                    (Just res) = foldr conv Nothing stmts
                                 where
                                    conv (HsGenerator src pat e) (Just next) = Just $
                                        (HsInfixApp (convertHsExp e) (HsQVarOp (UnQual (HsSymbol ">>="))) (HsLambda src [pat] next))
                                    conv (HsLetStmt decls) (Just next) = Just $
                                        (HsLet decls next)
                                    conv (HsQualifier e) (Just next) = Just $
                                        (HsInfixApp (convertHsExp e) (HsQVarOp (UnQual (HsSymbol ">>"))) next)
                                    conv (HsQualifier e) Nothing = Just $
                                        (convertHsExp e)
            a                                  -> a

        convertHsDecl a = case a of
            HsFunBind  matches              -> HsFunBind $ map convertHsMatch matches
            HsPatBind  src pat rhs decls    -> HsPatBind src pat (convertHsRhs rhs) (map convertHsDecl decls)
            HsInstDecl s ctx qn types decls -> HsInstDecl s ctx qn types (map convertHsDecl decls)
            a               -> a
        convertHsMatch (HsMatch s q ps rhs decls)       = HsMatch s q ps (convertHsRhs rhs) (map convertHsDecl decls)
        convertHsRhs a = case a of
            HsUnGuardedRhs a    -> HsUnGuardedRhs $ convertHsExp a
            HsGuardedRhss a     -> HsGuardedRhss  $ map convertHsGuardedRhs a
        convertHsGuardedRhs (HsGuardedRhs s g e)        = HsGuardedRhs s (convertHsExp g) (convertHsExp e)
        convertHsGuardedAlts a = case a of
            HsUnGuardedAlt a    -> HsUnGuardedAlt $ convertHsExp a
            HsGuardedAlts a     -> HsGuardedAlts $ map convertHsGuardedAlt a
        convertHsGuardedAlt (HsGuardedAlt src a b)      = HsGuardedAlt src (convertHsExp a) (convertHsExp b)
        convertHsFieldUpdate (HsFieldUpdate q a)        = HsFieldUpdate q $ convertHsExp a
        convertHsStmt a = case a of
            HsGenerator src pat e   -> HsGenerator src pat $ convertHsExp e
            HsQualifier a           -> HsQualifier $ convertHsExp a
            HsLetStmt   a           -> HsLetStmt   $ map convertHsDecl a
        convertHsAlt (HsAlt src pat alt decls)          = HsAlt src pat (convertHsGuardedAlts alt) (map convertHsDecl decls)

-- In case the sequencer definition is not specified a default one is returned (f1 >> f2 = (\_ -> f2) f1)
getSequencerFunctor [] = (\[f1,f2] -> (HsApp (HsParen  (HsLambda fakeSrc [HsPWildCard] f2)) f1))
getSequencerFunctor ss = transformMatchToFunctor $ head ss
-- for now the head call is necessary, since the case pattern matching system is not ready yet

-- generates a function that packs n parameters in a tuple of size n
-- f a b c d = f (a,b,c,d)
--pack_generator n | n > 0 = (HsParen (HsLambda fakeSrc [params] (code)))

-- Transforms an HsMatch in a function which will substitute the parameter to the formal parameters
transformMatchToFunctor (HsMatch _ _ pats rhs _) = functorizer (rhs_to_exp rhs) pats
    where
        rhs_to_exp (HsUnGuardedRhs e) = e
        rhs_to_exp (HsGuardedRhss es) = rhss_to_exp es
        {-
        rhs_to_exp (HsGuardedRhss es) =  (HsCase (HsLit (HsInt 0))
            [HsAlt fakeSrc (HsPWildCard) (HsGuardedAlts (rhss_to_exp es)) []]) 
        rhss_to_exp [(HsGuardedRhs _ c@(HsVar (UnQual (HsIdent "otherwise")))  d)]   = [(HsGuardedAlt fakeSrc c d)]
        rhss_to_exp ((HsGuardedRhs _ c@(HsVar (UnQual (HsIdent "otherwise")))  d):_) = [(HsGuardedAlt fakeSrc c d)]
        rhss_to_exp [(HsGuardedRhs _ c d)]    = [(HsGuardedAlt fakeSrc c d)]
        rhss_to_exp ((HsGuardedRhs _ c d):es) = (HsGuardedAlt fakeSrc c d):(rhss_to_exp es)-}
        first_pat = head pats
    
        rhss_to_exp [(HsGuardedRhs _ c d)]    = HsIf c d (generate_match_exception d)
        rhss_to_exp ((HsGuardedRhs _ c d):es) = HsIf c d (HsParen (rhss_to_exp es))
        generate_match_exception d = HsParen (HsApp (HsParen (HsLambda fakeSrc [HsPVar (HsIdent "a")] (HsCase (HsVar (UnQual (HsIdent "a"))) [HsAlt fakeSrc (HsPLit (HsInt 0)) (HsUnGuardedAlt d) []]))) (HsLit (HsInt 1)))


{- @TODO why?
f 0 z c = z
f a b _ | a > b     = 0
        | b > a     = 1
        | otherwise = 2

p0,..,pn are variable names, when i call function f

g p0 p1 p2 = case (p0,p1,p2) of
            (0,z,c) -> z
            (a,b,_) | a > b     -> 0
                    | b > a     -> 1
                    | otherwise -> 2
-}

transformListToMatch = head

filterFunBindsByName name = filter testFunBind 
    where
        testFunBind (HsMatch _ (HsIdent ident) _ _ _)   =  ident == name
        testFunBind (HsMatch _ (HsSymbol symbol) _ _ _) = symbol == name
        
functorizer i ps xs = applyl functorize i ps xs

{--- functorize ---
    Given a piece of haskell code functorize and a variable will generate a
    function to substitute the reccourences of the name with the first parameter
    passed.
    
     - If the variable is a wildcard it is ignored
     - If is  just a variable it is substituted in the code
     - If the variable is a pattern matching a lambda expression is used
-}

functorize HsPWildCard code = (\_ -> code)
functorize (HsPVar (HsIdent var)) code = (\new -> replace var new code)
functorize var code = (\new -> (HsApp (HsParen (HsLambda fakeSrc [parentetizeHsPApp var] code)) new))
    where
        parentetizeHsPApp c@(HsPApp _ _) = (HsPParen c)
        parentetizeHsPApp x = x

{— applyl —  
 i <- code  
 f <- functorize  
 p <- formal parameter  
 x <- substitue with this  
  
from a list of functions f1,…,fn and a list of parameters p1,…,pn  
they are applied (f1 (f2 (… (fn i p1) p2)…) pn)  
Used by functorize to substitue parameters in the correct order  
-}
applyl f i ps xs = result
    where
        (result,_)      = apply_ (zipWith (\f p -> f p) (repeat f) ps) i
        apply_ (f:fs) i = applyFromTuple f (apply_ fs i)
        apply_ []     i = (i,xs)
        applyFromTuple f (i,(x:xs)) = (f i x,xs)


{----- Class Replace ---------------------------------------------------------
replace method substitute a variable (1) with the value (2) passed in the 
code passed (3)
-------------------------------------------------------------------------------}

class Replace a where
    replace :: String -> HsExp -> a -> a
    
instance Replace a => Replace [a] where
    replace n d = map (replace n d)
    
instance Replace HsModule where
    replace n d (HsModule x y z w decls) = (HsModule x y z w (replace n d decls))

instance Replace HsExp where
    replace n d a = case a of
        c@(HsVar (UnQual (HsIdent x)))  -> if x == n then d else c
        c@(HsVar (UnQual (HsSymbol x))) -> if x == n then d else c
        HsInfixApp a o b       -> HsInfixApp (replace n d a) o (replace n d b)
        HsApp e1 e2            -> HsApp (replace n d e1) (replace n d e2)
        HsNegApp e             -> HsNegApp $ replace n d e
        HsLambda s pats e      -> HsLambda s pats (replace n d e)
        HsLet decls e          -> HsLet (replace n d decls) (replace n d e)
        HsIf a b c             -> HsIf (replace n d a) (replace n d b) (replace n d c)
        HsCase a e             -> HsCase (replace n d a) (replace n d e)
        HsDo a                 -> HsDo    $ replace n d a
        HsTuple a              -> HsTuple $ replace n d a
        HsList a               -> HsList  $ replace n d a
        HsParen a              -> HsParen $ replace n d a
        HsLeftSection a o      -> HsLeftSection (replace n d a) o
        HsRightSection o a     -> HsRightSection o (replace n d a)
        HsRecConstr o a        -> HsRecConstr o (replace n d a)
        HsRecUpdate a b        -> HsRecUpdate (replace n d a) (replace n d b)
        HsEnumFrom a           -> HsEnumFrom $ replace n d a
        HsEnumFromTo a b       -> HsEnumFromTo (replace n d a) (replace n d b)
        HsEnumFromThen a b     -> HsEnumFromThen (replace n d a) (replace n d b)
        HsEnumFromThenTo a b c -> HsEnumFromThenTo (replace n d a) (replace n d b) (replace n d c)
        HsListComp a s         -> HsListComp (replace n d a) (replace n d s)
        HsExpTypeSig s a q     -> HsExpTypeSig s (replace n d a) q
        HsAsPat s a            -> HsAsPat s $ replace n d a
        HsWildCard             -> HsWildCard
        HsIrrPat a             -> HsIrrPat $ replace n d a
    ---- @CHECK these must be substituted ?? ------
        c@(HsVar (Qual _ (HsIdent x)))  -> if x == n then d else c
        c@(HsVar (Qual _ (HsSymbol x))) -> if x == n then d else c
    ------------------------------------------------------------------
        a              -> a

instance Replace HsDecl where
    replace n d a = case a of
        HsFunBind matches               -> HsFunBind $ replace n d matches
        HsPatBind src pat rhs decl      -> HsPatBind src pat (replace n d rhs) (replace n d decl)
        HsInstDecl s ctx qn types decls -> HsInstDecl s ctx qn types $ replace n d decls
        a               -> a

instance Replace HsMatch where
    replace n d (HsMatch s q ps rhs decls) = HsMatch s q ps (replace n d rhs) (replace n d decls)

instance Replace HsRhs where
    replace n d a = case a of
        HsUnGuardedRhs x  -> HsUnGuardedRhs $ replace n d x
        HsGuardedRhss  xs -> HsGuardedRhss  $ replace n d xs

instance Replace HsGuardedRhs where
    replace n d (HsGuardedRhs s a b) = HsGuardedRhs s (replace n d a) (replace n d b)

instance Replace HsGuardedAlts where
    replace   n d a = case a of
        HsUnGuardedAlt e -> HsUnGuardedAlt $ replace n d e
        HsGuardedAlts  l -> HsGuardedAlts  $ replace n d l

instance Replace HsGuardedAlt where
    replace n d (HsGuardedAlt src a b) = HsGuardedAlt src (replace n d a) (replace n d b)

instance Replace HsFieldUpdate where
    replace n d (HsFieldUpdate q a) = HsFieldUpdate q (replace n d a)

instance Replace HsStmt where
    replace n d a = case a of
        HsGenerator src pat e -> HsGenerator src pat (replace n d e)
        HsQualifier a         -> HsQualifier (replace n d a)
        HsLetStmt   a         -> HsLetStmt (replace n d a)

instance Replace HsAlt where
    replace n d (HsAlt src pat rhs decls) = HsAlt src pat (replace n d rhs) (replace n d decls)


{----- Module DeMonad ---------------------------------------------------
Module main functions
------------------------------------------------------------------------}

-- Rewrites an Haskell module to avoid the use of the Monad class
workModule :: HsModule -> Maybe HsModule
workModule workMod = (\m -> if (length m) == 1 then
                                Just $ cleanCodeFromMonad $ convert workMod
                            else
                                Nothing) (filterMonads workMod)

-- Rewrites an Haskell file to avoid the use of the Monad class
workFileToFile :: FilePath -> FilePath -> IO ()
workFileToFile src dst = do converted <- workFileInternal src
                            file <- openFile dst WriteMode
                            hPutStrLn file converted
                            hClose file

-- Converts an haskell file and returns it as a parsed module
workFile :: FilePath -> IO String
workFile src = do converted <- workFileInternal src
                  return converted

{----- Module DeMonad internal utility ----------------------------------
Module main utility functions
------------------------------------------------------------------------}

-- Function that does the rewrite work
workFileInternal src = 
    do module_data <- readFile src
       case (parseModuleWithMode (ParseMode src) module_data) of
            (ParseOk workMod)     -> (\m -> if (length m) == 1
                then return $ prettyPrint $ cleanCodeFromMonad $ convert workMod
                                else fail "No monads or too much monads found") $ filterMonads workMod
            (ParseFailed loc msg) -> do fail ("Errore " ++  msg ++ " "++(showSrcLoc loc))
         where
            showSrcLoc (SrcLoc f r c) = show f ++ ":" ++ show r ++ ":" ++ show c

-- Removes the monad import code and the monad instances from the haskell module
cleanCodeFromMonad (HsModule a b c d e) = (HsModule a b c (filter isNotMonadImport d) (removeMonad e))
    where
        -- filters out monad class import command
        isNotMonadImport (HsImportDecl _ (Module "Monad") _ _ _) = False
        isNotMonadImport _ = True
        -- filters out the monad definition
        removeMonad decls = filter (not . isMonadInstance) decls

-- Returns all the monads in a parsed file
filterMonads (HsModule _ _ _ _ decls) = filter isMonadInstance decls

-- Test is an instance of a class is an instance of the Monad class
isMonadInstance (HsInstDecl _ _ (UnQual (HsIdent "Monad")) _ _) = True
isMonadInstance _ = False

{- test function, prints a module
pm name = do t <- readFile name
             putStrLn $ show $ parseModule t -}
