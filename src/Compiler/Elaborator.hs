module Compiler.Elaborator where

import           Control.Monad   (foldM)
import           Data.Maybe      (fromMaybe)

import qualified Compiler.Lambda as Lambda
import qualified Compiler.Syntax as Syntax
import qualified Compiler.Type   as Type

elaborate :: Syntax.Program -> Lambda.Program
elaborate p = runM m emptyK [] emptyEnv 0
  where m = do n <- gather p
               r <- update n
               withRename r $ do
                 populateEnv
                 convert p


--------------------------------------------------------------------------------
-- Gather will collect all module-level names in the program. It must expand
-- units.
--------------------------------------------------------------------------------

data Name = Name
              { nameUnits        :: [(String, Name)]
              , nameModules      :: [(String, Name)]
              , nameVariants     :: [String]
              , nameConstructors :: [(String, Int)]
              , nameFunctions    :: [String]
              }
            deriving (Eq, Show)

emptyName :: Name
emptyName = Name [] [] [] [] []

builtinName :: Name
builtinName = Name [ ( "Escape"
                     , Name []
                            []
                            []
                            []
                            [ "Throw"
                            , "Catch"
                            ]
                     )
                   ]
                   []
                   ["Output", "String"]
                   [ ("Continue", 1)
                   , ("Exit", 0)
                   , ("Write", 2)
                   ]
                   [ "Concatenate"
                   , "Continue"
                   , "Exit"
                   , "Show"
                   , "Write"
                   , "Unreachable"
                   ]

nameWithUnit :: Name -> String -> Name -> Name
nameWithUnit (Name x1s x2s x3s x4s x5s) s n = Name ((s, n) : x1s) x2s x3s x4s x5s

nameWithModule :: Name -> String -> Name -> Name
nameWithModule (Name x1s x2s x3s x4s x5s) s n = Name x1s ((s, n) : x2s) x3s x4s x5s

nameWithVariant :: Name -> String -> Name
nameWithVariant (Name x1s x2s x3s x4s x5s) s = Name x1s x2s (s:x3s) x4s x5s

nameWithConstructor :: Name -> String -> Int -> Name
nameWithConstructor (Name x1s x2s x3s x4s x5s) s i = Name x1s x2s x3s ((s,i):x4s) x5s

nameWithFunction :: Name -> String -> Name
nameWithFunction (Name x1s x2s x3s x4s x5s) s = Name x1s x2s x3s x4s (s:x5s)

namesLookupUnit :: [Name] -> [String] -> Name
namesLookupUnit [] q = error $ "namesLookupUnit: " ++ show q
namesLookupUnit (n:ns) q = fromMaybe (namesLookupUnit ns q) (nameLookupUnit n q)

nameLookupUnit :: Name -> [String] -> Maybe Name
nameLookupUnit n [] = error "nameLookupUnit"
nameLookupUnit n [s] = lookup s (nameUnits n)
nameLookupUnit n (s:q) = do n <- lookup s (nameModules n)
                            nameLookupUnit n q

gather :: Syntax.Program -> M Name
gather p = return $ gatherProgram p

gatherProgram :: Syntax.Program -> Name
gatherProgram (Syntax.Program ds) = foldl (gatherDec []) builtinName ds

gatherDec :: [Name] -> Name -> Syntax.Dec -> Name
gatherDec ns n (Syntax.FunDec _ s _ _ _ _) = nameWithFunction n s
gatherDec ns n (Syntax.ModDec _ s ds)      = nameWithModule n s (foldl (gatherDec (n:ns)) emptyName ds)
gatherDec ns n (Syntax.NewDec _ s q _)     = nameWithModule n s (namesLookupUnit (n:ns) q)
gatherDec ns n (Syntax.SumDec _ s _ cs)    = foldl gatherConstructor (nameWithVariant n s) (zip cs [0..])
gatherDec ns n (Syntax.UnitDec _ s _ ds)   = nameWithUnit n s (foldl (gatherDec (n:ns)) emptyName ds)

gatherConstructor :: Name -> ((Syntax.Pos, String, [Syntax.Typ]) , Int) -> Name
gatherConstructor n ((_, s, _), i) = nameWithFunction (nameWithConstructor n s i) s


--------------------------------------------------------------------------------
-- Update will generate unique identifiers for all names.
--------------------------------------------------------------------------------

data Rename = Rename
                { renameUnits        :: [(String, UnitClosureIdent)]
                , renameMods         :: [(String, Rename)]
                , renameVariants     :: [(String, Lambda.VariantIdent)]
                , renameConstructors :: [(String, Lambda.ConstructorIndex)]
                , renameFunctions    :: [(String, Lambda.TagIdent)]
                , renameTypes        :: [(String, Lambda.Type)]
                , renameValues       :: [(String, Lambda.ValueIdent)]
                }
              deriving (Eq, Show)

emptyRename :: Rename
emptyRename = Rename [] [] [] [] [] [] []

update :: Name -> M Rename
update (Name x1s x2s x3s x4s x5s) = do
  x1s <- mapM updateUnit x1s
  x2s <- mapM updateModule x2s
  x3s <- mapM updateName x3s
  x5s <- mapM updateName x5s
  return $ Rename x1s x2s x3s x4s x5s [] []

updateUnit :: (String, Name) -> M (String, Int)
updateUnit (s, _) = updateName s

updateModule :: (String, Name) -> M (String, Rename)
updateModule (s, n) = do
  r <- update n
  return (s, r)

updateName :: String -> M (String, Int)
updateName s = do
  d <- gen
  return (s, d)


--------------------------------------------------------------------------------
-- Convert uses the rename structure to manage naming while it exports
-- declarations.
--------------------------------------------------------------------------------

data Env = Env
             { envUnitClosures :: [(Int, UnitClosure)]
             , envTags         :: [(Int, Lambda.Tag)]
             , envVariants     :: [(Int, Lambda.Variant)]
             , envFunctions    :: [(Int, Lambda.Function)]
             }
           deriving (Show)

-- Ignore the unit closures when checking equality. Equality is only used for
-- testing.

instance Eq Env where
  Env x1s x2s x3s x4s == Env y1s y2s y3s y4s = x2s == y2s
                                            && x3s == y3s
                                            && x4s == y4s

type UnitClosureIdent = Int

data UnitClosure = UnitClosure ([Lambda.Type] -> Rename -> M ())

instance Show UnitClosure where
  show _ = "UnitClosure"

unitClosure :: [Rename] -> [String] -> [Syntax.Dec] -> UnitClosure
unitClosure rs ss ds = UnitClosure f
  where f tys r =
          withRenameStack rs $
            withTypeRenames ss tys $
              withRename r $
                mapM_ convertDec ds

unitClosureApply :: UnitClosure -> [Lambda.Type] -> Rename -> M ()
unitClosureApply (UnitClosure f) = f

emptyEnv :: Env
emptyEnv = Env [] [] [] []

populateEnv :: M ()
populateEnv = do

  d <- lookupVariant ["Output"]
  exportVariant d (Lambda.Variant [] ["Output"] [[]])

  -- Dunno about this.
  d <- lookupVariant ["String"]
  exportVariant d (Lambda.Variant [] ["String"] [[]])

  d <- lookupUnit ["Escape"]
  exportUnitClosure d (UnitClosure f)

  d <- lookupFunction ["Concatenate"]
  d1 <- gen
  d2 <- gen
  d3 <- gen
  d4 <- gen
  exportFunction d (Lambda.Function [] undefined
                     (Lambda.LambdaTerm d2 (Lambda.TupleType [undefined, undefined])
                       (Lambda.UntupleTerm [d3, d4] (Lambda.VariableTerm d2)
                         (Lambda.ConcatenateTerm (Lambda.VariableTerm d3) (Lambda.VariableTerm d4)))))

  d <- lookupFunction ["Continue"]
  d1 <- gen
  exportFunction d (Lambda.Function [] undefined
                     (Lambda.LambdaTerm d1 Lambda.StringType
                       (Lambda.ConstructorTerm undefined [] 1 [Lambda.VariableTerm d1])))

  d <- lookupFunction ["Exit"]
  exportFunction d (Lambda.Function [] undefined (Lambda.ConstructorTerm undefined [] 0 []))

  d <- lookupFunction ["Show"]
  d1 <- gen
  d2 <- gen
  exportFunction d (Lambda.Function [d1] undefined
                     (Lambda.LambdaTerm d2 (Lambda.VariableType d1)
                       (Lambda.ShowTerm (Lambda.VariableType d1) (Lambda.VariableTerm d2))))

  d <- lookupFunction ["Write"]
  d1 <- gen
  d2 <- gen
  exportFunction d (Lambda.Function [] undefined
                     (Lambda.LambdaTerm d1 undefined
                       (Lambda.LambdaTerm d2 undefined
                         (Lambda.ConstructorTerm undefined [] 2 [Lambda.VariableTerm d1, Lambda.VariableTerm d2]))))

  d <- lookupFunction ["Unreachable"]
  exportFunction d (Lambda.Function [] undefined (Lambda.UnreachableTerm undefined))


  where f [ty1, ty2] r =
          withRenameStack [r] $ do
            d1 <- gen
            exportTag d1 (Lambda.Tag ty1 ty2)
            d2 <- lookupFunction ["Throw"]
            d3 <- gen
            exportFunction d2 $
              Lambda.Function [] (Lambda.ArrowType ty1 ty2) $
                Lambda.LambdaTerm d3 undefined $
                  Lambda.ThrowTerm (Lambda.TagTerm d1) (Lambda.VariableTerm d3)
            d4 <- lookupFunction ["Catch"]
            d5 <- gen
            d6 <- gen
            d7 <- gen
            d8 <- gen
            d9 <- gen
            exportFunction d4 $
              Lambda.Function [d5] undefined $
                Lambda.LambdaTerm d6 undefined $
                  Lambda.LambdaTerm d7 undefined $
                    Lambda.CatchTerm (Lambda.TagTerm d1)
                      (Lambda.ApplyTerm (Lambda.VariableTerm d6) Lambda.UnitTerm)
                      d8
                      d9
                      (Lambda.ApplyTerm (Lambda.ApplyTerm (Lambda.VariableTerm d7)
                                                          (Lambda.VariableTerm d8))
                                        (Lambda.VariableTerm d9))
        f _ _ = error "populateEnv"

envAddUnitClosure :: Env -> Int -> UnitClosure -> Env
envAddUnitClosure (Env x1s x2s x3s x4s) d x = Env ((d,x):x1s) x2s x3s x4s

envAddTag :: Env -> Int -> Lambda.Tag -> Env
envAddTag (Env x1s x2s x3s x4s) d x = Env x1s ((d,x):x2s) x3s x4s

envAddVariant :: Env -> Lambda.VariantIdent -> Lambda.Variant -> Env
envAddVariant (Env x1s x2s x3s x4s) d x = Env x1s x2s ((d,x):x3s) x4s

envAddFunction :: Env -> Lambda.FunctionIdent -> Lambda.Function -> Env
envAddFunction (Env x1s x2s x3s x4s) d x = Env x1s x2s x3s ((d,x):x4s)

convert :: Syntax.Program -> M Lambda.Program
convert (Syntax.Program ds) = do mapM_ convertDec ds
                                 d <- lookupFunction ["Main"]
                                 Env _ x2s x3s x4s <- getEnv
                                 return $ Lambda.Program x2s x3s x4s d

convertDec :: Syntax.Dec -> M ()
convertDec (Syntax.FunDec _ s ss ps ty t) = do d <- lookupFunction [s]
                                               ds <- mapM (const gen) ss
                                               withTypeRenames ss (map Lambda.VariableType ds) $ do
                                                 ty <- convertType ty
                                                 ty <- convertCurriedPatterns ps ty
                                                 t <- convertCurried ps t
                                                 exportFunction d (Lambda.Function ds ty t)
convertDec (Syntax.ModDec _ s ds)       = do r <- lookupMod [s]
                                             withRename r $
                                               mapM_ convertDec ds
convertDec (Syntax.NewDec _ s1 q tys)   = do tys' <- mapM convertType tys
                                             r <- lookupMod [s1]
                                             d <- lookupUnit q
                                             x <- lookupUnitClosure d
                                             unitClosureApply x tys' r
convertDec (Syntax.SumDec _ s ss cs)    = convertSumDec s ss cs
convertDec (Syntax.UnitDec _ s1 s2s ds) = do d <- lookupUnit [s1]
                                             rs <- getRenameStack
                                             exportUnitClosure d $ unitClosure rs s2s ds

convertCurried :: [Syntax.Pat] -> Syntax.Term -> M Lambda.Term
convertCurried []     t = convertTerm t
convertCurried (p:ps) t = do
  d  <- gen
  t  <- convertPat d p (convertCurried ps t)
  ty <- patternType p
  return $ Lambda.LambdaTerm d ty t

convertPat :: Int -> Syntax.Pat -> M a -> M a
convertPat d p m =
  case p of
    Syntax.AscribePat _ p ty ->
      convertPat d p m
    Syntax.LowerPat _ s ->
      withValueRename s d m
    Syntax.UnitPat _ ->
      m
    p -> error $ "cp: " ++ show p

convertTerm :: Syntax.Term -> M Lambda.Term
convertTerm t =
  case t of
    Syntax.ApplyTerm _ t1 t2 -> do
      t1 <- convertTerm t1
      t2 <- convertTerm t2
      return $ Lambda.ApplyTerm t1 t2
    Syntax.BindTerm _ p t1 t2 -> do
      d <- gen
      t1 <- convertTerm t1
      t2 <- convertPat d p $ convertTerm t2
      return $ Lambda.BindTerm d t1 t2
    Syntax.SeqTerm t1 t2 -> do
      d  <- gen
      t1 <- convertTerm t1
      t2 <- convertTerm t2
      return $ Lambda.BindTerm d t1 t2
    Syntax.StringTerm _ x ->
      return $ Lambda.StringTerm x
    Syntax.UnitTerm _ ->
      return Lambda.UnitTerm
    Syntax.UpperTerm _ tys _ q -> do
      d   <- lookupFunction q
      tys <- mapM convertTypeType tys
      return $ Lambda.TypeApplyTerm d tys
    Syntax.VariableTerm _ s -> do
      d <- lookupValueRename s
      return $ Lambda.VariableTerm d
    _ -> error $ "ct: " ++ show t


-- This must export both the variant type and the constructor functions.

convertSumDec :: String -> [String] -> [(Syntax.Pos, String, [Syntax.Typ])] -> M ()
convertSumDec s ss cs = do
  d <- lookupVariant [s]
  dd <- mapM (const gen) ss
  withTypeRenames ss (map Lambda.VariableType dd) $ do
    let names = map (\ (_, name, _) -> name) cs
    tys <- mapM (\ (_, _, tys) -> mapM convertType tys) cs
    exportVariant d (Lambda.Variant dd names tys)
  let f n [] = return ()
      f n ((_, s2, tys):cs) = do
        d2 <- lookupFunction [s2]
        dd2 <- mapM (const gen) ss
        withTypeRenames ss (map Lambda.VariableType dd2) $ do
          ty <- convertCurriedTypes tys (Lambda.VariantType d (map Lambda.VariableType dd2))
          t <- let g [] d2s = return $ Lambda.ConstructorTerm d (map Lambda.VariableType dd2) n (reverse d2s)
                   g (ty1:ty1s) d2s = do
                     ty1 <- convertType ty1
                     d2 <- gen
                     t <- g ty1s (Lambda.VariableTerm d2 : d2s)
                     return $ Lambda.LambdaTerm d2 ty1 t
                in g tys []
          exportFunction d2 $ Lambda.Function dd2 ty t
        f (n + 1) cs
   in f 0 cs

convertCurriedTypes :: [Syntax.Typ] -> Lambda.Type -> M Lambda.Type
convertCurriedTypes []         ty2 = return ty2
convertCurriedTypes (ty1:ty1s) ty2 = do ty1 <- convertType ty1
                                        ty2 <- convertCurriedTypes ty1s ty2
                                        return $ Lambda.ArrowType ty1 ty2

convertCurriedPatterns :: [Syntax.Pat] -> Lambda.Type -> M Lambda.Type
convertCurriedPatterns []     ty2 = return ty2
convertCurriedPatterns (p:ps) ty2 = do ty1 <- patternType p
                                       ty2 <- convertCurriedPatterns ps ty2
                                       return $ Lambda.ArrowType ty1 ty2

--         | UpperPat Pos [Type.Type] Type.Type Qual [Pat]

patternType :: Syntax.Pat -> M Lambda.Type
patternType (Syntax.AscribePat _ _ ty)  = convertType ty
patternType (Syntax.LowerPat _ _)       = error "impossible"
patternType (Syntax.TuplePat _ _ ps)    = do tys <- mapM patternType ps
                                             return $ Lambda.TupleType tys
patternType Syntax.UnderbarPat          = error "impossible"
patternType (Syntax.UnitPat _)          = return Lambda.UnitType
patternType (Syntax.UpperPat {})        = error "patternType"

convertType :: Syntax.Typ -> M Lambda.Type
convertType (Syntax.ArrowTyp ty1 ty2) = do ty1 <- convertType ty1
                                           ty2 <- convertType ty2
                                           return $ Lambda.ArrowType ty1 ty2
convertType (Syntax.LowerTyp s)       = lookupType s
convertType (Syntax.TupleTyp tys)     = do tys <- mapM convertType tys
                                           return $ Lambda.TupleType tys
convertType (Syntax.UnitTyp _)        = return Lambda.UnitType
convertType (Syntax.UpperTyp _ q tys) = do d <- lookupVariant q
                                           tys <- mapM convertType tys
                                           return $ Lambda.VariantType d tys

convertTypeType :: Type.Type -> M Lambda.Type
convertTypeType (Type.Arrow ty1 ty2)  = do ty1 <- convertTypeType ty1
                                           ty2 <- convertTypeType ty2
                                           return $ Lambda.ArrowType ty1 ty2
convertTypeType (Type.Metavariable _) =    error "convertTypeType"
convertTypeType Type.String           =    return Lambda.StringType
convertTypeType (Type.Tuple tys)      = do tys <- mapM convertTypeType tys
                                           return $ Lambda.TupleType tys
convertTypeType Type.Unit             =    return Lambda.UnitType
convertTypeType (Type.Variable s)     =    lookupType s
convertTypeType (Type.Variant q tys)  = do d <- lookupVariant q
                                           tys <- mapM convertTypeType tys
                                           return $ Lambda.VariantType d tys

lookupConstructor :: [String] -> M Int
lookupConstructor q = do rs <- getRenameStack
                         return $ renameStackLookupConstructor rs q

renameStackLookupConstructor :: [Rename] -> [String] -> Int
renameStackLookupConstructor []     q = error $ "impossible: " ++ show q
renameStackLookupConstructor (r:rs) q = fromMaybe failure (renameLookupConstructor r q)
  where failure = renameStackLookupConstructor rs q

renameLookupConstructor :: Rename -> [String] -> Maybe Int
renameLookupConstructor r []    = error "impossible"
renameLookupConstructor r [s]   = lookup s (renameConstructors r)
renameLookupConstructor r (s:q) = do r <- lookup s (renameMods r)
                                     renameLookupConstructor r q

lookupFunction :: [String] -> M Int
lookupFunction q = do rs <- getRenameStack
                      return $ renameStackLookupFunction rs q

renameStackLookupFunction :: [Rename] -> [String] -> Int
renameStackLookupFunction []     q = error $ "impossible: " ++ show q
renameStackLookupFunction (r:rs) q = fromMaybe failure (renameLookupFunction r q)
  where failure = renameStackLookupFunction rs q

renameLookupFunction :: Rename -> [String] -> Maybe Int
renameLookupFunction r []    = error "impossible"
renameLookupFunction r [s]   = lookup s (renameFunctions r)
renameLookupFunction r (s:q) = do r <- lookup s (renameMods r)
                                  renameLookupFunction r q

lookupType :: String -> M Lambda.Type
lookupType s = do rs <- getRenameStack
                  return $ renameStackLookupType rs s

renameStackLookupType :: [Rename] -> String -> Lambda.Type
renameStackLookupType [] s = error "impossible"
renameStackLookupType (r:rs) s = fromMaybe failure (lookup s (renameTypes r))
  where failure = renameStackLookupType rs s

lookupUnit :: [String] -> M Int
lookupUnit q = do rs <- getRenameStack
                  return $ renameStackLookupUnit rs q

renameStackLookupUnit :: [Rename] -> [String] -> Int
renameStackLookupUnit (r:rs) q  = fromMaybe failure (renameLookupUnit r q)
                                 where failure = renameStackLookupUnit rs q
renameStackLookupUnit []     _  = error "impossible b"

renameLookupUnit :: Rename -> [String] -> Maybe Int
renameLookupUnit r []     = error "impossible c"
renameLookupUnit r (s:[]) = lookup s (renameUnits r)
renameLookupUnit r (s:q)  = do r' <- lookup s (renameMods r)
                               renameLookupUnit r' q


lookupVariant :: [String] -> M Lambda.VariantIdent
lookupVariant q = do rs <- getRenameStack
                     return $ renameStackLookupVariant rs q

renameStackLookupVariant :: [Rename] -> [String] -> Int
renameStackLookupVariant (r:rs) q =
  fromMaybe failure (renameLookupVariant r q)
  where failure = renameStackLookupVariant rs q
renameStackLookupVariant [] _ = error "impossible"

renameLookupVariant :: Rename -> [String] -> Maybe Lambda.VariantIdent
renameLookupVariant r []     = error "impossible"
renameLookupVariant r (s:[]) = lookup s (renameVariants r)
renameLookupVariant r (s:q)  = do r' <- lookup s (renameMods r)
                                  renameLookupVariant r' q

lookupMod :: [String] -> M Rename
lookupMod q = do rs <- getRenameStack
                 return $ renameStackLookupMod rs q

renameStackLookupMod :: [Rename] -> [String] -> Rename
renameStackLookupMod (r:rs) q  = fromMaybe failure (renameLookupMod r q)
                                 where failure = renameStackLookupMod rs q
renameStackLookupMod []     _  = error "impossible d"

renameLookupMod :: Rename -> [String] -> Maybe Rename
renameLookupMod = foldM f
  where f r s = lookup s (renameMods r)


--------------------------------------------------------------------------------
-- The monad.
--------------------------------------------------------------------------------

newtype M a = M { runM :: forall b. (a -> Env -> Int -> b) -> [Rename] -> Env -> Int -> b }

instance Monad M where
  return x = M (\ k _ -> k x)
  m >>= g = M (\ k rs -> runM m (\ x -> runM (g x) k rs) rs)

emptyK :: a -> Env -> Int -> a
emptyK x _ _ = x

gen :: M Int
gen = M (\ k _ v i -> k i v (i + 1))

getEnv :: M Env
getEnv = M (\ k _ v n -> k v v n)

exportUnitClosure :: Int -> UnitClosure -> M ()
exportUnitClosure d x = M (\ k rs v -> k () (envAddUnitClosure v d x))

exportTag :: Lambda.TagIdent -> Lambda.Tag -> M ()
exportTag d x = M (\ k rs v -> k () (envAddTag v d x))

exportVariant :: Lambda.VariantIdent -> Lambda.Variant -> M ()
exportVariant d x = M (\ k rs v -> k () (envAddVariant v d x))

exportFunction :: Lambda.FunctionIdent -> Lambda.Function -> M ()
exportFunction d x = M (\ k rs v -> k () (envAddFunction v d x))

getRenameStack :: M [Rename]
getRenameStack = M f
                 where f k = k

withTypeRenames :: [String] -> [Lambda.Type] -> M a -> M a
withTypeRenames ss tys m = M (\ k rs -> runM m k (Rename [] [] [] [] [] (zip ss tys) [] : rs))

lookupUnitClosure :: Int -> M UnitClosure
lookupUnitClosure d = M (\ k rs v -> k (fromMaybe failure (lookup d (envUnitClosures v))) v)
  where failure = error "Compiler.Elaborator.lookupUnitClosure"

withRenameStack :: [Rename] -> M a -> M a
withRenameStack rs m =  M (\ k _ -> runM m k rs)

withRename :: Rename -> M a -> M a
withRename r m = M (\ k rs -> runM m k (r:rs))

lookupValueRename :: String -> M Lambda.ValueIdent
lookupValueRename s = do
  rs <- getRenameStack
  case rs of
    [] -> error "lookupValueRename"
    (r:_) -> return $ fromMaybe (error "lookupValueRename") (lookup s (renameValues r))

withValueRename :: String -> Lambda.ValueIdent -> M a -> M a
withValueRename s d m = do
  rs <- getRenameStack
  case rs of
    [] -> error "withValueRename"
    (Rename x1s x2s x3s x4s x5s x6s x7s : rs) ->
      withRenameStack (Rename x1s x2s x3s x4s x5s x6s ((s, d) : x7s) : rs)
        m


{-
elaborate :: Syntax.Program -> Lambda.Program
elaborate p = run $ do
  n <- names p
  r <- renames n
  elaborateProgram r p

data Names = Names [(String, Names)] -- Units
                   [(String, Names)] -- Modules
                   [String]          -- Variants
                   [(String, Int)]   -- Constructor Indices
                   [String]          -- Functions
                   [String]          -- Types
                   [String]          -- Values
             deriving (Eq, Show)

names :: Syntax.Program -> M Names
names = return . programNames

programNames :: Syntax.Program -> Names
programNames (Syntax.Program ds) = decsNames [] ds

decsNames :: [Names] -> [Syntax.Dec] -> Names
decsNames ns ds = foldl (decNames ns) emptyNames ds

decNames :: [Names] -> Names -> Syntax.Dec -> Names
decNames ns n (Syntax.FunDec _ s _ _ _ _) = namesWithFun n s
decNames ns n (Syntax.NewDec _ s1 s2 _)   = namesWithNew n (s1, namesLookupUnit (n:ns) s2)
decNames ns n (Syntax.SumDec _ s _ cs)    = undefined
decNames ns n (Syntax.TagDec _ s _)       = namesWithTag n s
decNames ns n (Syntax.UnitDec _ s _ ds)   = namesWithUnit n (s, decsNames (n:ns) ds)

emptyNames :: Names
emptyNames = Names [] [] [] [] [] [] []

namesWithFun :: Names -> String -> Names
namesWithFun (Names x1 x2 x3 x4 x5 x6 x7) s = Names x1 x2 x3 x4 (s:x5) x6 x7

namesWithNew :: Names -> (String, Names) -> Names
namesWithNew (Names x1 x2 x3 x4 x5 x6 x7) x = Names x1 (x:x2) x3 x4 x5 x6 x7

namesWithTag :: Names -> String -> Names
namesWithTag (Names x1 x2 x3 x4 x5 x6 x7) s = Names x1 x2 x3 x4 (s:x5) x6 x7

namesWithUnit :: Names -> (String, Names) -> Names
namesWithUnit (Names x1 x2 x3 x4 x5 x6 x7) x = Names (x:x1) x2 x3 x4 x5 x6 x7

namesUnits :: Names -> [(String, Names)]
namesUnits (Names x1 x2 x3 x4 x5 x6 x7) = x1

namesLookupUnit :: [Names] -> String -> Names
namesLookupUnit []     s = error $ "unit not found: " ++ s
namesLookupUnit (n:ns) s = maybe (namesLookupUnit ns s) id (lookup s (namesUnits n))

type UnitIdent = Int

data Renames = Renames [(String, (UnitIdent, Renames))]
                       [(String, Renames)] -- Modules
                       [(String, Lambda.VariantIdent)]
                       [(String, Lambda.ConstructorIndex)]
                       [(String, Lambda.FunctionIdent)]
                       [(String, Lambda.TypeIdent)]
                       [(String, Lambda.ValueIdent)]

renamer :: String -> M (String, Int)
renamer = undefined

unitRenamer :: (String, Names) -> M (String, (UnitIdent, Renames))
unitRenamer (s, n) = do (_, d) <- renamer s
                        r <- renames n
                        return (s, (d, r))

moduleRenamer :: (String, Names) -> M (String, Renames)
moduleRenamer (s, n) = do
  n' <- renames n
  return (s, n')

renames :: Names -> M Renames
renames (Names x1 x2 x3 x4 x5 x6 x7) = do
  x1' <- mapM unitRenamer x1
  x2' <- mapM moduleRenamer x2
  x3' <- mapM renamer x3
  x4' <- return x4
  x5' <- mapM renamer x5
  x6' <- mapM renamer x6
  x7' <- mapM renamer x7
  return $ Renames x1' x2' x3' x4' x5' x6' x7'

elaborateProgram :: Renames -> Syntax.Program -> M Lambda.Program
elaborateProgram r (Syntax.Program ds) = do Env _ x1 x2 x3 <- foldM (elaborateDec r) emptyEnv ds
                                            d <- renamesLookupFun r "Main"
                                            return $ Lambda.Program x1 x2 x3 d

emptyEnv :: Env
emptyEnv = Env [] [] [] []

elaborateDec :: Renames -> Env -> Syntax.Dec -> M Env
elaborateDec r v (Syntax.FunDec _ s _ _ _ _)  = undefined (renamesLookupFun r s)
elaborateDec r v (Syntax.NewDec _ s1 s2 tys)  = do tys' <- mapM (elaborateType r) tys
                                                   unitClosureApply v (envLookupUnitClosure v (renamesLookupUnitClosure r s2)) tys'
elaborateDec r v (Syntax.SumDec _ _ _ _)      = undefined
elaborateDec r v (Syntax.TagDec _ _ _)        = undefined
elaborateDec r v (Syntax.UnitDec _ s1 s2s ds) = do (d, r2) <- renamesLookupUnit r s1
                                                   envWithUnitClosure v d (UnitClosure r2 s2s ds)

elaborateType :: Renames -> Syntax.Typ -> M Lambda.Type
elaborateType = undefined

unitClosureApply :: Env -> UnitClosure -> [Lambda.Type] -> M Env
unitClosureApply = undefined

envLookupUnitClosure :: Env -> Int -> UnitClosure
envLookupUnitClosure = undefined

renamesLookupUnitClosure :: Renames -> String -> Int
renamesLookupUnitClosure = undefined

envWithUnitClosure :: Env -> UnitIdent -> UnitClosure -> M Env
envWithUnitClosure (Env x1 x2 x3 x4) d x = return $ Env ((d,x):x1) x2 x3 x4

renamesLookupFun :: Renames -> String -> M Int
renamesLookupFun = undefined

renamesLookupUnit :: Renames -> String -> M (Int, Renames)
renamesLookupUnit = undefined

data UnitClosure = UnitClosure Renames [String] [Syntax.Dec]

data Env = Env [(UnitIdent, UnitClosure)]
               [(Lambda.TagIdent, Lambda.Tag)]
               [(Lambda.VariantIdent, Lambda.Variant)]
               [(Lambda.FunctionIdent, Lambda.Function)]

type M a = Maybe a

run :: M a -> a
run = undefined
-}

{-

data UnitClosure = UnitClosure [Renames] [Syntax.Dec]

type UnitIdent = Int

data Out = Out [(UnitIdent, UnitClosure)]
               [(Lambda.TagIdent, Lambda.Tag)]
               [(Lambda.VariantIdent, Lambda.Variant)]
               [(Lambda.FunctionIdent, Lambda.Function)]

-- Creates a Names value.

gatherDec :: Syntax.Dec -> Result ()
gatherDec (Syntax.FunDec _ s _ _ _ _) = exportFunction s
gatherDec (Syntax.NewDec _ s1 s2 _)   = do xs <- lookupUnit s2
                                           renameUnit s1 xs
gatherDec (Syntax.SumDec _ s _ cs)    = do exportVariant s
                                           mapM_ exportConstructor cs
gatherDec (Syntax.TagDec _ s _)       = exportTag s
gatherDec (Syntax.UnitDec _ s _ ds)   = do xs <- withNestedEnv $ do
                                                   mapM_ gatherDec ds
                                                   getNames
                                           exportUnit s xs

renameUnit :: String -> Names
renameUnit s1 (Names rs s2s s3s s4s s5s) = do
  mapM_ (\ (s6, ds) -> exportUnit (f s6) ds) rs
  mapM_ (exportTag . f) s2s
  mapM_ (exportVariant . f) s2s
  mapM_ (exportConstructor . f) s2s
  mapM_ (exportFunction . f) s2s
  where f s6 = s1 ++ s6






elaborateDec :: Syntax.Dec -> Result ()
elaborateDec = undefined

data Result a where
  Return                 :: a -> Result a
  Bind                   :: Result b -> (b -> Result a) -> Result a
  Gen                    :: Result Int
  LookupUpper            :: String -> Result Lambda.FunctionIdent
  LookupTypeVariable     :: String -> Result Lambda.TypeIdent
  LookupValueVariable    :: String -> Result Lambda.ValueIdent
  LookupConstructorIndex :: String -> Result Lambda.ConstructorIndex

instance Monad Result where
  return = Return
  Return x >>= f = f x
  Bind m g >>= f = Bind m (\ x -> g x >>= f)
  m        >>= f = Bind m f

impossible :: a
impossible = error "impossible"

run :: Result Lambda.Program -> Lambda.Program
run m = check genStart m
  where check :: Int -> Result Lambda.Program -> Lambda.Program
        check n (Return x)                          = x
        check n (Bind (Return _) _)                 = error "Compiler.Elaborater.run: unreachable"
        check n (Bind (Bind _ _) _)                 = error "Compiler.Elaborater.run: unreachable"
        check n (Bind Gen k)                        = check (n + 1) (k n)
        check n (Bind (LookupUpper s) k)            = impossible
        check n (Bind (LookupTypeVariable s) k)     = impossible
        check n (Bind (LookupValueVariable s) k)    = impossible
        check n (Bind (LookupConstructorIndex s) k) = impossible

withConstructors :: [(String, Int)] -> Result a -> Result a
withConstructors gs m = check m
  where check (Return x)                          = Return x
        check (Bind (LookupConstructorIndex s) k) = check $ k (maybe (error "withConstructors") id (lookup s gs))
        check (Bind m k)                          = Bind m (check . k)
        check m                                   = check (Bind m Return)

withUppers :: [(String, Int)] -> Result a -> Result a
withUppers gs m = check m
  where check (Return x)               = Return x
        check (Bind (LookupUpper s) k) = check $ k (maybe (error ("withUppers: " ++ s ++ ", " ++ show (map fst gs))) id (lookup s gs))
        check (Bind m k)               = Bind m (check . k)
        check m                        = check (Bind m Return)

withTypes :: [(String, Int)] -> Result a -> Result a
withTypes gs m = check m
  where check (Return x)                      = Return x
        check (Bind (LookupTypeVariable s) k) = check $ k (maybe (error "withTypes") id (lookup s gs))
        check (Bind m k)                      = Bind m (check . k)
        check m                               = check (Bind m Return)

withLower :: String -> Int -> Result a -> Result a
withLower d d' m = check m
  where check (Return x)                       = Return x
        check (Bind (LookupValueVariable s) k)
                                   | s == d    = check $ k d'
                                   | otherwise = Bind (LookupValueVariable s) (check . k)
        check (Bind m k)                       = Bind m (check . k)
        check m                                = check (Bind m Return)

elaborate :: Syntax.Program -> Lambda.Program
elaborate p = run (elaborateProgram p)

funs :: [(Lambda.FunctionIdent, Lambda.Function)]
funs = [ -- Exit
         (0, Lambda.Function [] (Lambda.VariantType 0 [])
               (Lambda.ConstructorTerm 0 [] 0 []))
         -- Unreachable
       , (9, Lambda.Function [10] (Lambda.VariableType 10)
               (Lambda.Unreachable (Lambda.VariableType 10)))
       ]

genStart :: Int
genStart = 11

constructorEnv :: [(String, Int)]
constructorEnv = [ ("Exit", 0)
                 ]

env :: [(String, Int)]
env = [ ("Exit", 0)
      , ("Unreachable", 9)
      ]

elaborateProgram :: Syntax.Program -> Result Lambda.Program
elaborateProgram (Syntax.Program ds) = do
  (gs1, gs2) <- decEnvs ([], []) ds
  withConstructors (constructorEnv ++ gs1) $ do
    withUppers (env ++ gs2) $ do
      xs1 <- liftM catMaybes $ mapM elaborateVariant ds
      xs2 <- liftM concat $ mapM elaborateFunction ds
      d <- LookupUpper "Main"
      return $ Lambda.Program [] xs1 (funs ++ xs2) d

decEnvs :: ([(String, Int)], [(String, Int)]) -> [Syntax.Dec] -> Result ([(String, Int)], [(String, Int)])
decEnvs (xs, ys) []                               = return (xs, ys)
decEnvs (xs, ys) (Syntax.FunDec _ s _ _ _ _ : ds) = do { d <- Gen; decEnvs (xs, (s, d) : ys) ds }
decEnvs (xs, ys) (Syntax.SumDec _ s _ rs : ds)    = do d <- Gen
                                                       ss <- return $ map (\ (_, s, _) -> s) rs
                                                       ns <- mapM (\ _ -> Gen) rs
                                                       decEnvs (zip ss [0..] ++ xs, zip ss ns ++ ys) ds
decEnvs (xs, ys) (Syntax.TagDec _ s ty : ds)      = do d <- Gen
                                                       decEnvs (xs, (s, d) : ys) ds
decEnvs (xs, ys) (Syntax.NewDec _ s1 "Escape" tys : ds) = do d1 <- Gen
                                                             d2 <- Gen
                                                             ys <- return $ (s1 ++ ".Throw", d1) : ys
                                                             ys <- return $ (s1 ++ ".Catch", d2) : ys
                                                             decEnvs (xs, ys) ds
decEnvs (xs, ys) (Syntax.NewDec _  _ _       _   : _ ) = error "decEnvs new"

elaborateFunction :: Syntax.Dec -> Result [(Lambda.FunctionIdent, Lambda.Function)]
elaborateFunction (Syntax.FunDec _ s ss ps t e) = do
  d  <- LookupUpper s
  ds <- mapM (\ _ -> Gen) ss
  withTypes (zip ss ds) $ do
    e' <- elaborateCurried ps e
    t  <- elaborateType (Syntax.funType ps t)
    return [(d, Lambda.Function ds t e')]
elaborateFunction (Syntax.SumDec _ s1 ss rs) = mapM f (zip [0..] rs)
  where f (i, (_, s2, tys)) = do
          d <- LookupUpper s2
          ds <- mapM (\ _ -> Gen) ss
          withTypes (zip ss ds) $ do
            ty <- elaborateType (Syntax.constructorType tys s1 ss)
            tys' <- mapM (elaborateType . Syntax.typType) tys
            t <- g tys' [] i
            return (d, Lambda.Function ds ty t)
        g []       ds i = return $ Lambda.ConstructorTerm undefined undefined i (map Lambda.VariableTerm ds)
        g (ty:tys) ds i = do d <- Gen
                             t <- g tys (d:ds) i
                             return $ Lambda.LambdaTerm d ty t
elaborateFunction (Syntax.TagDec _ s ty) = do
  d <- LookupUpper s
  ty' <- elaborateType (Syntax.typType ty)
  return $ [(d, Lambda.Function [] ty' (Lambda.TagTerm d))]
elaborateFunction (Syntax.NewDec _ s1 "Escape" [ty1, ty2]) = do d1 <- LookupUpper $ s1 ++ ".Catch"
                                                                d2 <- LookupUpper $ s1 ++ ".Throw"
                                                                d3 <- Gen
                                                                d4 <- Gen
                                                                d5 <- Gen
                                                                d6 <- Gen
                                                                d7 <- Gen
                                                                d8 <- Gen
                                                                d9 <- Gen
                                                                return [ (d1, Lambda.Function [d5] undefined
                                                                                (Lambda.LambdaTerm d6 undefined
                                                                                  (Lambda.LambdaTerm d7 undefined
                                                                                    (Lambda.CatchTerm (Lambda.TagTerm d3)
                                                                                      (Lambda.ApplyTerm (Lambda.VariableTerm d6) Lambda.UnitTerm)
                                                                                      d8 d9
                                                                                      (Lambda.ApplyTerm (Lambda.ApplyTerm (Lambda.VariableTerm d7)
                                                                                                                          (Lambda.VariableTerm d8))
                                                                                                        (Lambda.VariableTerm d9))))))
                                                                       , (d2, Lambda.Function [] undefined
                                                                                (Lambda.LambdaTerm d4 undefined
                                                                                  (Lambda.ThrowTerm (Lambda.TagTerm d3) (Lambda.VariableTerm d4))))
                                                                       ]
elaborateFunction (Syntax.NewDec _ _  _       _         ) = error "elaborateFunction new"

elaborateVariant :: Syntax.Dec -> Result (Maybe (Lambda.VariantIdent, Lambda.Variant))
elaborateVariant (Syntax.FunDec _ _ _ _ _ _) = return Nothing
elaborateVariant (Syntax.SumDec _ s ss rs) = do
  d <- return undefined
  ds <- mapM (\ _ -> Gen) ss
  withTypes (zip ss ds) $ do
    ns <- mapM (\ (_, n, _) -> return n) rs
    xs <- mapM (\ (_, _, tys) -> mapM (elaborateType . Syntax.typType) tys) rs
    return (Just (d, Lambda.Variant ds ns xs))
elaborateVariant (Syntax.TagDec _ _ _) = return Nothing
elaborateVariant (Syntax.NewDec _ _ _ _) = return Nothing

elaborateCurried :: [Syntax.Pat] -> Syntax.Term -> Result Lambda.Term
elaborateCurried [] e     = elaborateTerm e
elaborateCurried (p:ps) e = do
  d <- Gen
  e' <- elaboratePat d p (elaborateCurried ps e)
  t <- elaborateType $ Syntax.patType p
  return $ Lambda.LambdaTerm d t e'

elaboratePat :: Lambda.ValueIdent -> Syntax.Pat -> Result Lambda.Term -> Result Lambda.Term
elaboratePat d p m = elaboratePatAlt d p m (return $ Lambda.Unreachable undefined)

elaboratePats :: [Lambda.ValueIdent] -> [Syntax.Pat] -> Result Lambda.Term -> Result Lambda.Term
elaboratePats ds ps m = elaboratePatsAlt ds ps m (return $ Lambda.Unreachable undefined)

elaboratePatAlt :: Lambda.ValueIdent -> Syntax.Pat -> Result Lambda.Term -> Result Lambda.Term -> Result Lambda.Term
elaboratePatAlt d (Syntax.AscribePat p ty) m1 m2 = elaboratePatAlt d p m1 m2
elaboratePatAlt d (Syntax.LowerPat _ s)    m1 m2 = withLower s d m1
elaboratePatAlt d (Syntax.TuplePat _ ps)   m1 m2 = do ds <- mapM (\ _ -> Gen) ps
                                                      t <- elaboratePatsAlt ds ps m1 m2
                                                      return $ Lambda.UntupleTerm ds (Lambda.VariableTerm d) t
elaboratePatAlt d Syntax.UnderbarPat       m1 m2 = m1
elaboratePatAlt d (Syntax.UnitPat _)       m1 m2 = m1
elaboratePatAlt d (Syntax.UpperPat _ _ _ x ps) m1 m2
                                          = do i <- LookupConstructorIndex x
                                               ds <- mapM (\ _ -> Gen) ps
                                               m1' <- elaboratePatsAlt ds ps m1 m2
                                               m2' <- m2
                                               return $ Lambda.TestTerm (Lambda.VariableTerm d) i ds m1' m2'

elaboratePatsAlt :: [Lambda.ValueIdent] -> [Syntax.Pat] -> Result Lambda.Term -> Result Lambda.Term -> Result Lambda.Term
elaboratePatsAlt []     []     m1 m2 = m1
elaboratePatsAlt (d:ds) (p:ps) m1 m2 = elaboratePatAlt d p (elaboratePats ds ps m1) m2
elaboratePatsAlt _      _      m1 m2 = impossible

elaborateTerm :: Syntax.Term -> Result Lambda.Term
elaborateTerm (Syntax.ApplyTerm _ t1 t2)     = do { t1' <- elaborateTerm t1; t2' <- elaborateTerm t2; return $ Lambda.ApplyTerm t1' t2' }
elaborateTerm (Syntax.AscribeTerm _ t _)     = elaborateTerm t
elaborateTerm (Syntax.BindTerm _ p t1 t2)    = do d <- Gen
                                                  t1' <- elaborateTerm t1
                                                  t2' <- elaboratePat d p $ elaborateTerm t2
                                                  return $ Lambda.BindTerm d t1' t2'
elaborateTerm (Syntax.CaseTerm _ t rs)       = do d <- Gen
                                                  t' <- elaborateTerm t
                                                  t2' <- elaborateRules d rs
                                                  return $ Lambda.BindTerm d t' t2'
                                               where elaborateRules d [] = return $ Lambda.Unreachable undefined
                                                     elaborateRules d ((p, t1) : rs) = do
                                                       t2 <- elaborateRules d rs
                                                       d2 <- Gen
                                                       d3 <- Gen
                                                       t1 <- elaboratePatAlt d p (elaborateTerm t1) (return $ Lambda.ApplyTerm (Lambda.VariableTerm d2) Lambda.UnitTerm)
                                                       return $ Lambda.BindTerm d2 (Lambda.LambdaTerm d3 Lambda.UnitType t2) t1

elaborateTerm (Syntax.SeqTerm t1 t2)         = do { d <- Gen; t1' <- elaborateTerm t1; t2' <- elaborateTerm t2; return $ Lambda.BindTerm d t1' t2' }
elaborateTerm (Syntax.TupleTerm pos tys es)  = do { es' <- mapM elaborateTerm es; return $ Lambda.TupleTerm es' }
elaborateTerm (Syntax.UnitTerm pos)          = return Lambda.UnitTerm
elaborateTerm (Syntax.UpperTerm pos tys _ s) = do { d <- LookupUpper s; tys' <- mapM elaborateType tys; return $ Lambda.TypeApplyTerm d tys' }
elaborateTerm (Syntax.VariableTerm pos s)    = do { d <- LookupValueVariable s; return $ Lambda.VariableTerm d }

elaborateType :: Type.Type -> Result Lambda.Type
elaborateType (Type.Arrow t1 t2)    = do { t1' <- elaborateType t1; t2' <- elaborateType t2; return $ Lambda.ArrowType t1' t2' }
elaborateType (Type.Metavariable _) = error "Compiler.Elaborator: all metavariables should have been removed"
elaborateType (Type.Tuple ts)       = do { ts' <- mapM elaborateType ts; return $ Lambda.TupleType ts' }
elaborateType Type.Unit             = return Lambda.UnitType
elaborateType (Type.Variable s)     = liftM Lambda.VariableType (LookupTypeVariable s)
elaborateType (Type.Variant _ _)    = return $ Lambda.VariantType 0 [] -- fix
-}
