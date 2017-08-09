module AST where

import Control.Monad

-- | Type : Type is unsound and needs to be reworked with universe polymorphism
data Expr
  = Ann Expr Expr
  | Type
  | Pi Expr Expr
  | Var Int
  | App Expr Expr
  | Lam Expr
  deriving (Eq, Show)

type Context = [(Int, Expr)]

data TypeError
  = TypeMismatch Expr Expr
  | UnboundVar Int
  | NotAFunction Expr Expr
  | CannotInfer Expr
  deriving (Eq, Show)

eval :: Context -> Expr -> Expr
eval ctxt expr =
  case expr of
    Ann e _ -> eval ctxt e
    Type -> Type
    Pi rho rho' -> Pi (eval ctxt rho) (eval ctxt rho')
    Var n -> Var n
    App f x -> reduce $ App (eval ctxt f) (eval ctxt x)
    Lam e -> Lam (eval ctxt e)
  where
    reduce (App (Lam e) e') = subst 1 e e'
    reduce a = a

check :: Int -> Context -> Expr -> Expr -> Either TypeError ()
check binder ctxt (Lam e) (Pi tau tau') =
  check (binder+1) ((binder, tau) : ctxt) e tau'
check binder ctxt e tau = do
  tau' <- infer binder ctxt e
  unless (tau == tau') . Left $ TypeMismatch tau tau'

-- | Substitute first into second
subst :: Int -> Expr -> Expr -> Expr
subst binder new orig
  | binder < 1 = error "subst: called with binder less than 1"
  | otherwise =
      case orig of
        Ann e t -> Ann (subst binder new e) t
        Type -> Type
        Pi t e -> Pi (subst binder new t) (subst (binder+1) new e)
        Var n -> if binder == n then new else orig
        App f x -> App (subst binder new f) (subst binder new x)
        Lam e -> Lam (subst (binder+1) new e)

infer :: Int -> Context -> Expr -> Either TypeError Expr
infer binder ctxt expr =
  case expr of
    Ann e rho -> do
      check binder ctxt rho Type
      let tau = eval ctxt rho
      check binder ctxt e tau
      pure tau
    Type -> pure Type
    Pi rho rho' -> do
      check binder ctxt rho Type
      let tau = eval ctxt rho
      check (binder+1) ((binder, tau) : ctxt) rho' Type
      pure Type
    Var n ->
      case lookup n ctxt of
        Just t -> pure t
        Nothing -> Left $ UnboundVar n
    App f x -> do
      tf <- infer binder ctxt f
      case tf of
        Pi tau tau' -> do
          check binder ctxt x tau
          pure (subst 1 x tau')
        _ -> Left $ NotAFunction f tf
    _ -> Left $ CannotInfer expr
