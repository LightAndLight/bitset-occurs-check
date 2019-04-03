{-# language DerivingVia #-}
{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language FlexibleContexts #-}
{-# language ScopedTypeVariables #-}
{-# language StandaloneDeriving #-}
{-# language TemplateHaskell #-}
module HM where

import Bound.Scope (Scope, fromScope, toScope, abstract, transverseScope)
import Bound.Name (Name(..), abstract1Name)
import Bound.TH (makeBound)
import Bound.Var (Var(..), unvar)
import Control.Applicative ((<|>), liftA2)
import Control.Monad (ap, replicateM)
import Control.Monad.Except (MonadError, ExceptT(..), runExceptT, throwError)
import Control.Monad.ST (ST, runST)
import Control.Monad.Trans (lift)
import Data.Bitset (Bitset, Union(..))
import Data.Deriving (deriveEq1, deriveShow1)
import Data.Functor.Classes (Eq1(..))
import Data.Equivalence.Monad (MonadEquiv)
import Data.Map (Map)
import Data.STRef (STRef, newSTRef, readSTRef, writeSTRef, modifySTRef)
import Data.Void (Void, absurd)
import Unsafe.Coerce (unsafeCoerce)

import qualified Bound.Scope as Scope
import qualified Data.Bitset as Bitset
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set

data Tm n a
  = Var a
  | App (Tm n a) (Tm n a)
  | Lam (Scope (Name n ()) (Tm n) a)
  deriving (Functor, Foldable, Traversable)
instance Eq1 (Tm n) where
  liftEq f (Var a) (Var a') = f a a'
  liftEq f (App a b) (App a' b') = liftEq f a a' && liftEq f b b'
  liftEq f (Lam s) (Lam s') = liftEq f s s'
  liftEq _ _ _ = False
deriveShow1 ''Tm
deriving instance Eq a => Eq (Tm n a)
deriving instance (Show n, Show a) => Show (Tm n a)
makeBound ''Tm

lam :: Eq a => a -> Tm a a -> Tm a a
lam a = Lam . abstract1Name a

data Ty v a
  = TyVar v a
  | TyApp v (Ty v a) (Ty v a)
  | TyArr
  deriving (Show, Functor, Foldable, Traversable)
deriveShow1 ''Ty
instance Monoid v => Applicative (Ty v) where pure = return; (<*>) = ap
instance Monoid v => Monad (Ty v) where
  return = TyVar mempty
  TyVar _ a >>= f = f a
  TyApp _ a b >>= f =
    let
      a' = a >>= f
      b' = b >>= f
    in
      TyApp (measure a' <> measure b') a' b'
  TyArr >>= _ = TyArr

instance Eq a => Eq (Ty v a) where
  TyVar _ a == TyVar _ a' = a == a'
  TyApp _ a b == TyApp _ a' b' = a == a' && b == b'
  TyArr == TyArr = True
  _ == _ = False

instance Ord a => Ord (Ty v a) where
  compare (TyVar _ a) (TyVar _ a') = compare a a'
  compare (TyVar _ a) TyApp{} = LT
  compare (TyVar _ a) TyArr = LT
  compare TyApp{} TyVar{} = GT
  compare (TyApp _ a b) (TyApp _ a' b') =
    case compare a a' of
      EQ -> compare b b'
      res -> res
  compare (TyApp _ a b) TyArr = LT
  compare TyArr TyVar{} = GT
  compare TyArr TyApp{} = GT
  compare TyArr TyArr = EQ

data Scheme f a = Forall !Int (Scope Int f a)
  deriving (Functor, Foldable, Traversable, Show)

forall_ :: (Foldable f, Monad f, Ord a) => [a] -> f a -> Scheme f a
forall_ vs t = Forall (length inOrder) $ abstract (`List.elemIndex` inOrder) t
  where
    vsSet = Set.fromList vs
    inOrder =
      List.nub $
      foldr (\a b -> if a `Set.member` vsSet then a : b else b) [] t

measure :: Monoid v => Ty v a -> v
measure ty =
  case ty of
    TyVar v _ -> v
    TyApp v _ _ -> v
    TyArr -> mempty

mapMeasure :: Monoid v' => (v -> v') -> Ty v a -> Ty v' a
mapMeasure f ty =
  case ty of
    TyVar v a -> TyVar (f v) a
    TyApp _ a b ->
      let
        a' = mapMeasure f a
        b' = mapMeasure f b
      in
        TyApp (measure a' <> measure b') a' b'
    TyArr -> TyArr

tyVar :: (a -> v) -> a -> Ty v a
tyVar f a = TyVar (f a) a

tyApp :: Monoid v => Ty v a -> Ty v a -> Ty v a
tyApp a b = TyApp (measure a <> measure b) a b

tyArr :: Monoid v => Ty v a -> Ty v a -> Ty v a
tyArr a b = TyApp (measure a <> measure b) (TyApp (measure a) TyArr a) b

newtype UData = UData { metas :: Bitset }
  deriving (Semigroup, Monoid) via Union
  deriving Show

tyMeta :: Int -> Ty UData (Either Int a)
tyMeta n = TyVar (UData $ Bitset.singleton n) (Left n)

occurs :: Int -> Ty UData a -> Bool
occurs v ty = Bitset.member v $ metas (measure ty)

data TypeError v n ty
  = TypeMismatch (Ty v (Either Int ty)) (Ty v (Either Int ty))
  | OccursError Int (Ty v (Either Int ty))
  | NotInScope n
  deriving (Eq, Show)

data Rank = Rank !Int | Inf
  deriving (Eq, Ord, Show)

data NodeType s a
  = NVar a
  | NMeta !Int (STRef s Rank)
  | NApp (STRef s (Node s a)) (STRef s (Node s a))
  | NArr

data Node s a
  = Node
  { nodeData :: UData
  , nodeType :: NodeType s a
  }

next :: STRef s Int -> ST s Int
next r = readSTRef r <* modifySTRef r (+1)

newNApp ::
  STRef s (Node s a) ->
  STRef s (Node s a) ->
  ST s (STRef s (Node s a))
newNApp aR bR = do
  a <- readSTRef aR
  b <- readSTRef bR
  newSTRef $ Node (nodeData a <> nodeData b) (NApp aR bR)

newNArr ::
  STRef s (Node s a) ->
  STRef s (Node s a) ->
  ST s (STRef s (Node s a))
newNArr aR bR = do
  arrow <- newSTRef $ Node mempty NArr
  arrowA <- newNApp arrow aR
  newNApp arrowA bR

newNMetaRanked ::
  STRef s Int ->
  STRef s Int ->
  ST s (STRef s (Node s a))
newNMetaRanked supplyRef rankRef = do
  r <- readSTRef rankRef
  n <- readSTRef supplyRef <* modifySTRef supplyRef (+1)
  rank <- newSTRef $ Rank r
  newSTRef $ Node (UData $ Bitset.singleton n) (NMeta n rank)

newNMetaInf ::
  STRef s Int ->
  ST s (STRef s (Node s a))
newNMetaInf supplyRef = do
  n <- readSTRef supplyRef <* modifySTRef supplyRef (+1)
  rank <- newSTRef Inf
  newSTRef $ Node (UData $ Bitset.singleton n) (NMeta n rank)

toNodes :: forall s v a. Ty v a -> ST s (Node s a)
toNodes ty =
  case ty of
    TyVar _ a -> pure $ Node mempty (NVar a)
    TyApp _ a b -> do
      a' <- toNodes a
      b' <- toNodes b
      aRef <- newSTRef a'
      bRef <- newSTRef b'
      pure $ Node (nodeData a' <> nodeData b') (NApp aRef bRef)
    TyArr -> pure $ Node mempty NArr

toNodesWith :: forall s v a b. (a -> ST s (Node s b)) -> Ty v a -> ST s (Node s b)
toNodesWith f ty =
  case ty of
    TyVar _ a -> f a
    TyApp _ a b -> do
      a' <- toNodesWith f a
      b' <- toNodesWith f b
      aRef <- newSTRef a'
      bRef <- newSTRef b'
      pure $ Node (nodeData a' <> nodeData b') (NApp aRef bRef)
    TyArr -> pure $ Node mempty NArr

fromNodes :: forall s a. Node s a -> ST s (Ty UData (Either Int a))
fromNodes (Node v nty) =
  case nty of
    NVar a -> pure . TyVar mempty $ Right a
    NMeta a _ -> pure . TyVar v $ Left a
    NApp aRef bRef -> do
      a <- readSTRef aRef
      b <- readSTRef bRef
      TyApp v <$> fromNodes a <*> fromNodes b
    NArr -> pure TyArr

newtype UScheme s a
  = UScheme
  { unUScheme ::
      Scheme (ExceptT (STRef s (Node s a)) (Ty UData)) a
  }

generalize ::
  forall s a.
  STRef s Int ->
  STRef s (Node s a) ->
  ST s (UScheme s a)
generalize rr nr = do
  mapRef <- newSTRef mempty
  res <- go mapRef rr nr
  sz <- Map.size <$> readSTRef mapRef
  pure . UScheme . Forall sz $ toScope res
  where
    go ::
      forall a.
      STRef s (Map Int Int) ->
      STRef s Int ->
      STRef s (Node s a) ->
      ST s (ExceptT (STRef s (Node s a)) (Ty UData) (Var Int a))
    go mapRef rankRef nR = do
      currentRank <- readSTRef rankRef
      n <- readSTRef nR
      case nodeType n of
        NVar a -> pure $ pure $ F a
        NMeta a r -> do
          rank <- readSTRef r
          if Rank currentRank < rank
            then do
              mp <- readSTRef mapRef
              b <- case Map.lookup a mp of
                Nothing -> do
                  let sz = Map.size mp
                  sz <$ modifySTRef mapRef (Map.insert a sz)
                Just b -> pure b
              pure $ pure $ B b
            else pure . ExceptT . TyVar (nodeData n) $ Left nR
        NApp aRef bRef -> do
          a' <- runExceptT <$> go mapRef rankRef aRef
          b' <- runExceptT <$> go mapRef rankRef bRef
          pure $ ExceptT $ TyApp (nodeData n) a' b'
        NArr -> pure $ lift TyArr

instantiate ::
  forall s v a.
  Monoid v =>
  STRef s Int ->
  Scheme (Ty v) a ->
  ST s (Node s a)
instantiate supplyRef (Forall n s) = do
  metas <- replicateM n $ do
    m <- readSTRef supplyRef <* modifySTRef supplyRef (1+)
    r <- newSTRef Inf
    pure $ Node (UData $ Bitset.singleton m) (NMeta m r)
  toNodesWith (pure . unvar (metas !!) (Node mempty . NVar)) (fromScope s)

zonkScheme ::
  UScheme s a ->
  Maybe (Scheme (Ty UData) a)
zonkScheme (UScheme (Forall n s)) =
  Forall n <$> transverseScope (traverse (either (const Nothing) Just) . runExceptT) s

zonkNodes :: forall s a. Node s a -> ST s (Maybe (Ty UData a))
zonkNodes (Node v nty) =
  case nty of
    NVar a -> pure $ Just (TyVar mempty a)
    NMeta{} -> pure Nothing
    NApp aRef bRef -> do
      a <- readSTRef aRef
      b <- readSTRef bRef
      liftA2 (TyApp v) <$> zonkNodes a <*> zonkNodes b
    NArr -> pure $ Just TyArr

unify ::
  Eq a =>
  STRef s (Node s a) ->
  STRef s (Node s a) ->
  ExceptT (TypeError UData n a) (ST s) ()
unify nRef1 nRef2 = do
  n1 <- lift $ readSTRef nRef1
  n2 <- lift $ readSTRef nRef2
  case (nodeType n1, nodeType n2) of
    (NVar a, NVar a') ->
      if a == a'
      then pure ()
      else do
        t1 <- lift $ fromNodes n1
        t2 <- lift $ fromNodes n2
        throwError $ TypeMismatch t1 t2
    (NMeta n rn, NMeta m rm) -> do
      lift $ do
        minRank <- min <$> readSTRef rn <*> readSTRef rm
        writeSTRef rn minRank *> writeSTRef rm minRank
      if n == m
        then pure ()
        else lift $ writeSTRef nRef2 n1
    (NMeta n _, _) ->
      if Bitset.member n $ metas (nodeData n2)
      then do
        t <- lift $ fromNodes n2
        throwError $ OccursError n t
      else lift $ writeSTRef nRef1 n2
    (_, NMeta n _) ->
      if Bitset.member n $ metas (nodeData n1)
      then do
        t <- lift $ fromNodes n1
        throwError $ OccursError n t
      else lift $ writeSTRef nRef2 n1
    (NApp a b, NApp a' b') -> do
      unify a a'
      unify b b'
      newA <- lift $ readSTRef a
      newB <- lift $ readSTRef b
      let v = nodeData newA <> nodeData newB
      lift $ do
        modifySTRef nRef1 $ \n -> n { nodeData = v }
        modifySTRef nRef2 $ \n -> n { nodeData = v }
    (NArr, NArr) -> pure ()
    _ -> do
      t1 <- lift $ fromNodes n1
      t2 <- lift $ fromNodes n2
      throwError $ TypeMismatch t1 t2

infer ::
  forall tm ty n v s.
  (Ord tm, Eq ty, Monoid v) =>
  (tm -> n) ->
  Map tm (Scheme (Ty v) Void) ->
  Map tm (STRef s (Node s ty)) ->
  Tm n tm ->
  ExceptT (TypeError UData n ty) (ST s) (STRef s (Node s ty))
infer n ds c t = do
  countRef <- lift $ newSTRef 0
  rankRef <- lift $ newSTRef 0
  go countRef rankRef n ds c t
  where
    go ::
      forall tm.
      Ord tm =>
      STRef s Int ->
      STRef s Int ->
      (tm -> n) ->
      Map tm (Scheme (Ty v) Void) ->
      Map tm (STRef s (Node s ty)) ->
      Tm n tm ->
      ExceptT (TypeError UData n ty) (ST s) (STRef s (Node s ty))
    go countRef rankRef names defs tmCtx tm =
      case tm of
        Var a ->
          case Map.lookup a tmCtx of
            Nothing ->
              case Map.lookup a defs of
                Nothing -> throwError . NotInScope $ names a
                Just sig -> lift $ newSTRef . unsafeCoerce =<< instantiate countRef sig
            Just a -> pure a
        App a b -> do
          aTy <- go countRef rankRef names defs tmCtx a
          bTy <- go countRef rankRef names defs tmCtx b
          retTy <- lift $ newNMetaInf countRef
          unify aTy =<< lift (newNArr bTy retTy)
          pure retTy
        Lam s -> do
          argTy <- lift $ do
            modifySTRef rankRef (+1)
            newNMetaRanked countRef rankRef
          resTy <-
            go
              countRef
              rankRef
              (unvar (\(Name n _) -> n) names)
              (Map.foldrWithKey (\k a -> Map.insert (F k) a) mempty defs)
              (Map.insert (B $ Name undefined ()) argTy $
               Map.foldrWithKey (\k a -> Map.insert (F k) a) mempty tmCtx)
              (fromScope s)
          lift $ do
            modifySTRef rankRef (subtract 1)
            newNArr argTy resTy


emptyDefs :: Map String (Scheme (Ty ()) Void)
emptyDefs = mempty

id_test :: Either (TypeError UData String String) (Ty UData (Either Int String))
id_test =
  runST $ do
    res <- runExceptT $ infer id emptyDefs mempty id_tm
    case res of
      Left a -> pure $ Left a
      Right a -> fmap Right . fromNodes =<< readSTRef a
  where
    id_tm :: Tm String String
    id_tm = lam "x" $ pure "x"

const_test :: Either (TypeError UData String String) (Ty UData (Either Int String))
const_test =
  runST $ do
    res <- runExceptT $ infer id emptyDefs mempty const_tm
    case res of
      Left a -> pure $ Left a
      Right a -> fmap Right . fromNodes =<< readSTRef a
  where
    const_tm :: Tm String String
    const_tm = lam "x" $ lam "y" $ pure "x"

omega_test :: Either (TypeError UData String String) (Ty UData (Either Int String))
omega_test =
  runST $ do
    res <- runExceptT $ infer id emptyDefs mempty omega_tm
    case res of
      Left a -> pure $ Left a
      Right a -> fmap Right . fromNodes =<< readSTRef a
  where
    omega_tm :: Tm String String
    omega_tm = lam "x" $ App (pure "x") (pure "x")

app_test :: Either (TypeError UData String String) (Ty UData (Either Int String))
app_test =
  runST $ do
    res <- runExceptT $ infer id emptyDefs mempty app_tm
    case res of
      Left a -> pure $ Left a
      Right a -> fmap Right . fromNodes =<< readSTRef a
  where
    app_tm :: Tm String String
    app_tm = lam "f" $ lam "x" $ App (pure "f") (pure "x")

app_scheme_test :: Either (TypeError UData String String) (Maybe (Scheme (Ty UData) String))
app_scheme_test =
  runST $ do
    res <- runExceptT $ infer id emptyDefs mempty app_tm
    case res of
      Left a -> pure $ Left a
      Right a -> do
        rank <- newSTRef 0
        Right . zonkScheme <$> generalize rank a
  where
    app_tm :: Tm String String
    app_tm = lam "f" $ lam "x" $ App (pure "f") (pure "x")

instantiate_const_test :: Ty UData (Either Int String)
instantiate_const_test =
  runST $ do
    countRef <- newSTRef 0
    fromNodes =<< instantiate countRef const_ty
  where
    const_ty :: Scheme (Ty UData) String
    const_ty =
      forall_ ["a", "b"] $
      tyArr (pure "a") $
      tyArr (pure "b" ) $
      pure "a"

-- | broken?
big_map :: [(String, Tm String String)]
big_map =
  [ ("pair", lam "x" $ lam "y" $ lam "z" $ App (App (pure "z") (pure "x")) (pure "y"))
  , ("x1", lam "y" $ App (App (pure "pair") (pure "y")) (pure "y"))
  , ("x2", lam "y" $ App (pure "x1") (App (pure "x1") (pure "y")))
  -- , ("x3", lam "y" $ App (pure "x2") (App (pure "x2") (pure "y")))
  -- , ("x4", lam "y" $ App (pure "x3") (App (pure "x3") (pure "y")))
  -- , ("x5", lam "y" $ App (pure "x4") (App (pure "x4") (pure "y")))
  -- , ("x6", lam "y" $ App (pure "x5") (App (pure "x5") (pure "y")))
  -- , ("bad", App (pure "x6") (lam "x" $ pure "x"))
  ]

big_scheme_test ::
  Either
    (TypeError UData String String)
    (Map String (Scheme (Ty UData) Void))
big_scheme_test = go mempty big_map
  where
    go ::
      Map String (Scheme (Ty UData) Void) ->
      [(String, Tm String String)] ->
      Either
        (TypeError UData String String)
        (Map String (Scheme (Ty UData) Void))
    go types [] = Right types
    go types ((defname, deftm) : rest) =
      let
        scheme =
          runST $ do
            countRef <- newSTRef 0
            res <- runExceptT $ infer id types mempty deftm
            res' <- traverse (fmap zonkScheme . generalize countRef) res
            case res' of
              Left e -> pure $ Left e
              Right a ->
                case a of
                  Nothing -> error "nothing"
                  Just a' -> pure $ Right a'
      in
        case scheme of
          Left e -> Left e
          Right (Forall n s) -> do
            s' <- traverse (unvar (Right . B) (error . show)) (fromScope s)
            go (Map.insert defname (Forall n $ toScope s') types) rest
