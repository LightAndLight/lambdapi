{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable, TemplateHaskell, FlexibleContexts, ApplicativeDo #-}
module AST where

import Bound
import Bound.Name
import Bound.Scope
import Control.Applicative
import Control.Monad
import Control.Monad.Trans.Class
import Data.Deriving
import Data.Functor.Classes
import Data.Functor.Identity
import Text.Trifecta

expr :: (Eq n, DeltaParsing m) => m n -> m (Expr n n)
expr ns =
  pi <|>
  lam <|>
  try app <|>
  try ann <|>
  var <|>
  between (symbol "(") (symbol ")") (token $ expr ns)
  where
    appRhs =
      between (symbol "(") (symbol ")") (token $ lam <|> try app <|> pi <|> ann) <|>
      token var
    appLhs =
      between (symbol "(") (symbol ")") (token $ lam <|> try ann <|> app) <|>
      token var
    app = do
      l <- appLhs
      rs <- some appRhs
      pure $ foldl App l rs

    annLhs =
      between (symbol "(") (symbol ")") (token $ lam <|> ann <|> try app) <|>
      token var
    annRhs =
      between (symbol "(") (symbol ")") ann <|>
      token (try app) <|>
      token lam <|>
      token var
    ann = Ann <$> (annLhs <* symbol ":") <*> annRhs

    var = Var <$> token ns
    pi = do
      _ <- symbol "pi"
      (n, f) <- between (symbol "(") (symbol ")") $ do
        n <- token ns
        _ <- symbol ":"
        pure (n, Pi n <$> token (expr ns))
      _ <- symbol "."
      f <*> (abstract1Name n <$> token (expr ns))
    lam = do
      _ <- symbol "lam"
      n <- token ns
      _ <- symbol "."
      Lam n . abstract1Name n <$> token (expr ns)

-- | Type : Type is unsound and needs to be reworked with universe polymorphism
data Expr n a
  = Ann (Expr n a) (Expr n a)
  | Type
  | Pi n (Expr n a) (Scope (Name n ()) (Expr n) a)
  | Var a
  | App (Expr n a) (Expr n a)
  | Lam n (Scope (Name n ()) (Expr n) a)
  deriving (Functor, Foldable, Traversable)

instance Eq1 (Expr n) where
  liftEq f (Ann a b) (Ann a' b') = liftEq f a a' && liftEq f b b'
  liftEq _ Type Type = True
  liftEq f (Pi _ a b) (Pi _ a' b') = liftEq f a a' && liftEq f b b'
  liftEq f (Var a) (Var a') = f a a'
  liftEq f (App a b) (App a' b') = liftEq f a a' && liftEq f b b'
  liftEq f (Lam _ a) (Lam _ a') = liftEq f a a'
  liftEq _ _ _ = False
  
deriveShow1 ''Expr

instance Applicative (Expr n) where
  pure = return
  (<*>) = ap

instance Monad (Expr n) where
  return = Var
  
  Ann a b >>= f = Ann (a >>= f) (b >>= f)
  Type >>= _ = Type
  Pi n a b >>= f = Pi n (a >>= f) (b >>>= f)
  Var a >>= f = f a
  App a b >>= f = App (a >>= f) (b >>= f)
  Lam n a >>= f = Lam n (a >>>= f)

instance Eq a => Eq (Expr n a) where
  (==) = eq1
  
instance (Show n, Show a) => Show (Expr n a) where
  showsPrec = showsPrec1

lam :: Eq n => n -> Expr n n -> Expr n n
lam n e = Lam n $ abstract1Name n e

piType :: Eq n => n -> Expr n n -> Expr n n -> Expr n n
piType n e e' = Pi n e $ abstract1Name n e'

eval :: Expr n a -> Expr n a
eval expr =
  case expr of
    Ann e _ -> eval e
    Type -> Type
    Pi n rho rho' ->
      let t = eval rho
      in Pi n t (runIdentity $ transverseScope (Identity . eval) rho')
    App f x ->
      case eval f of
        Lam _ e -> eval $ instantiate1Name (eval x) e
        _ -> error "eval: value applied to non-function value"
    Lam n e ->
      Lam n (runIdentity $ transverseScope (Identity . eval) e)
    _ -> expr

printExpr :: Expr String String -> String
printExpr e =
  case e of
    Ann a b -> "(" ++ printExpr a ++ ") : (" ++ printExpr b ++ ")"
    Type -> "Type"
    Pi n a b ->
      "pi (" ++ n ++ " : " ++ printExpr a ++ "). " ++
      printExpr (instantiate1Name (Var n) b)
    Var a -> a
    App a b -> "(" ++ printExpr a ++ ") (" ++ printExpr b ++ ")"
    Lam n a ->
      "lam " ++ n ++ ". " ++ printExpr (instantiate1Name (Var n) a)

data TypeError n a
  = TypeMismatch (Expr n a) (Expr n a)
  | NotAFunction (Expr n a)
  | NotAFunctionType (Expr n a)
  | CannotInfer (Expr n a)
  | UnknownVar n
  deriving (Eq, Show)

type Context n = [(n, Expr n n)]

-- | Check the first argument's type is the second argument. The second argument is
-- | assumed to be in normal form.
check :: Eq n => Context n -> Expr n n -> Expr n n -> Either (TypeError n n) ()
check ctxt expr ty
  | Lam x e <- expr =
      case ty of
        Pi n tau tau' ->
          check
            ((x, tau) : (n, tau) : ctxt)
            (instantiate1 (Var x) e)
            (instantiate1 (Var n) tau')
        _ -> Left $ NotAFunctionType ty
  | otherwise = do
      ty' <- infer ctxt expr
      unless (ty == ty') . Left $ TypeMismatch ty ty'
      
infer :: Eq n => Context n -> Expr n n -> Either (TypeError n n) (Expr n n)
infer ctxt expr =
  case expr of
    Ann e rho -> do
      check ctxt rho Type
      let tau = eval rho
      check ctxt e tau
      pure tau
    Type -> pure Type
    Pi n rho rho' -> do
      check ctxt rho Type
      let tau = eval rho
      check
        ((n, tau) : ctxt)
        (instantiate1 (Var n) rho')
        Type
      pure Type
    App f x -> do
      tf <- infer ctxt f
      case tf of
        Pi _ tau tau' -> do
          check ctxt x tau
          pure $ instantiate1 x tau'
        _ -> Left $ NotAFunction (Ann f tf)
    Var n ->
      case lookup n ctxt of
        Just tau -> pure tau
        Nothing -> Left $ UnknownVar n
    _ -> Left $ CannotInfer expr
