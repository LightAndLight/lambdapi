module AST where

import Control.Applicative
import Control.Monad

-- | Type : Type is unsound and needs to be reworked with universe polymorphism
data Expr
  = Ann Expr Expr
  | Type
  | Pi Expr Expr
  | Bound Int
  | Free Name
  | App Expr Expr
  | Lam Expr
  deriving (Eq, Show)

data Name
  = Local Int
  | Global String
  | Quote Int
  deriving (Eq, Show)

printExpr :: Expr -> String
printExpr = go [] (liftA2 (++) (pure <$> ['a'..'z']) (show <$> [1::Int ..]))
  where
    go mapping supply e =
      case e of
        Ann a b -> "(" ++ go mapping supply a ++ ") : (" ++ go mapping supply b ++ ")"
        Type -> "Type"
        Pi a b ->
          case supply of
            name : supply' ->
              "pi (" ++ name ++ " : " ++ go mapping supply a ++ "). " ++
              go (name : mapping) supply' b
            _ -> error "printExpr: name supply exhausted"
        Bound n -> mapping !! n
        Free (Global name) -> name
        Free a -> error "printExpr: unexpected " ++ show a ++ " in Free"
        App f x -> "(" ++ go mapping supply f ++ ") (" ++ go mapping supply x ++ ")"
        Lam a -> 
          case supply of
            name : supply' ->
              "lam " ++ name ++ ". " ++
              go (name : mapping) supply' a
            _ -> error "printExpr: name supply exhausted"

data TypeError
  = TypeMismatch Expr Expr
  | NotAFunction Expr Expr
  | UnknownName Name
  | NotAFunctionType Expr
  | CannotInfer Expr
  deriving (Eq, Show)

data Neutral
  = NVar Name
  | NApp Neutral Value

data Value
  = VLam (Value -> Value)
  | VPi Value (Value -> Value)
  | VType
  | VNeutral Neutral

quote :: Int -> Value -> Expr
quote binders v =
  case v of
    VLam f -> Lam . quote (binders+1) . f . VNeutral $ NVar $ Quote binders
    VPi t f -> Pi (quote binders t) (quote (binders+1) . f . VNeutral $ NVar $ Quote binders)
    VType -> Type
    VNeutral n -> fromNeutral binders n
  where
    fromNeutral binders (NVar (Quote n)) = Bound $ binders - n - 1
    fromNeutral binders (NVar n) = Free n
    fromNeutral binders (NApp n v) = App (fromNeutral binders n) (quote binders v)
  
type Environment = [Value]

eval :: Environment -> Expr -> Value
eval ctxt expr =
  case expr of
    Ann e _ -> eval ctxt e
    Type -> VType
    Pi rho rho' -> VPi (eval ctxt rho) (\v -> eval (v : ctxt) rho')
    Bound n -> ctxt !! n
    Free name -> VNeutral $ NVar name
    App f x ->
      case eval ctxt f of
        VLam f' -> f' (eval ctxt x)
        VNeutral f' -> VNeutral $ NApp f' (eval ctxt x)
        _ -> error "eval: value applied to non-function value"
    Lam e -> VLam (\v -> eval (v : ctxt) e)
    
type Context = [(Name, Value)]

check :: Int -> Context -> Expr -> Value -> Either TypeError ()
check binders ctxt expr ty
  | Lam e <- expr =
      case ty of
        VPi tau tau' ->
          check
            (binders+1)
            ((Local binders, tau) : ctxt)
            (subst 0 (Free $ Local binders) e)
            (tau' . VNeutral $ NVar $ Local binders)
        _ -> Left $ NotAFunctionType $ quote 0 ty
  | otherwise = do
      ty' <- infer binders ctxt expr
      let
        v = quote 0 ty
        v' = quote 0 ty'
      unless (v == v') . Left $ TypeMismatch v v'

-- | Substitute first into second
subst :: Int -> Expr -> Expr -> Expr
subst binder new orig
  | binder < 0 = error "subst: called with binder less than 0"
  | otherwise =
      case orig of
        Ann e t -> Ann (subst binder new e) t
        Type -> Type
        Pi t e -> Pi (subst binder new t) (subst (binder+1) new e)
        Bound n -> if binder == n then new else orig
        App f x -> App (subst binder new f) (subst binder new x)
        Lam e -> Lam (subst (binder+1) new e)
        Free a -> Free a

infer :: Int -> Context -> Expr -> Either TypeError Value
infer binders ctxt expr =
  case expr of
    Ann e rho -> do
      check binders ctxt rho VType
      let tau = eval [] rho
      check binders ctxt e tau
      pure tau
    Type -> pure VType
    Pi rho rho' -> do
      check binders ctxt rho VType
      let tau = eval [] rho
      check
        (binders+1)
        ((Local binders, tau) : ctxt)
        (subst 0 (Free $ Local binders) rho')
        VType
      pure VType
    Free name ->
      case lookup name ctxt of
        Just v -> pure v
        Nothing -> Left $ UnknownName name
    Bound a -> error $ "infer: unexpected " ++ show a
    App f x -> do
      tf <- infer binders ctxt f
      case tf of
        VPi tau tau' -> do
          check binders ctxt x tau
          pure $ tau' (eval [] x)
        _ -> Left $ NotAFunction f $ quote 0 tf
    _ -> Left $ CannotInfer expr
