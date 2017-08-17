module Typecheck where

import Bound
import Control.Monad

import Eval
import Expr

data TypeError
  = TypeMismatch Expr Expr
  | NotAFunction Expr
  | NotAFunctionType Expr
  | CannotInfer Expr
  | UnknownVar String
  deriving (Eq, Show)

type Context = [(String, Expr)]

-- | Check the first argument's type is the second argument. The second argument is
-- | assumed to be in normal form.
check :: Context -> Expr -> Expr -> Either TypeError ()
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

infer :: Context -> Expr -> Either TypeError Expr
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
    String _ -> pure $ Var "String"
    Var "String" -> pure Type
    Quote _ -> pure $ Var "Expr"
    Var "Expr" -> pure Type
    Var n ->
      case lookup n ctxt of
        Just tau -> pure tau
        Nothing -> Left $ UnknownVar n
    _ -> Left $ CannotInfer expr
