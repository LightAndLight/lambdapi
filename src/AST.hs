{-# language PatternSynonyms #-}
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
  | Int Int
  | String String
  | Char Char
  deriving (Eq, Show)

pattern Ctor :: String -> Expr
pattern Ctor s = Free (Global s)

pattern TInt :: Expr
pattern TInt = Free (Global "Int")

pattern TChar :: Expr
pattern TChar = Free (Global "Char")

pattern TString :: Expr
pattern TString = Free (Global "String")

data Name
  = Local Int
  | Global String
  | Quote Int
  deriving (Eq, Show)

printExpr :: Expr -> String
printExpr = go [] (("t"++) . show <$> [1::Int ..]) (("var"++) . show <$> [1::Int ..])
  where
    go mapping t_supply var_supply e =
      case e of
        Int n -> show n
        String s -> show s
        Char c -> show c
        Ann a b -> "(" ++ go mapping t_supply var_supply a ++ ") : (" ++ go mapping t_supply var_supply b ++ ")"
        Type -> "Type"
        Pi a b ->
          case t_supply of
            name : t_supply' ->
              "pi (" ++ name ++ " : " ++ go mapping t_supply' var_supply a ++ "). " ++
              go (name : mapping) t_supply' var_supply b
            _ -> error "printExpr: name supply exhausted"
        Bound n -> mapping !! n
        Free (Global name) -> name
        Free a -> error "printExpr: unexpected " ++ show a ++ " in Free"
        App f x -> "(" ++ go mapping t_supply var_supply f ++ ") (" ++ go mapping t_supply var_supply x ++ ")"
        Lam a -> 
          case var_supply of
            name : var_supply' ->
              "lam " ++ name ++ ". " ++
              go (name : mapping) t_supply var_supply' a
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
  | VInt Int
  | VChar Char
  | VString String
  | VNeutral Neutral

quote :: Int -> Value -> Expr
quote i v =
  case v of
    VLam f -> Lam . quote (i+1) . f . VNeutral $ NVar $ Quote i
    VPi t f -> Pi (quote i t) (quote (i+1) . f . VNeutral $ NVar $ Quote i)
    VType -> Type
    VNeutral n -> fromNeutral i n
    VInt n -> Int n
    VChar c -> Char c
    VString s -> String s
  where
    fromNeutral i (NVar (Quote n)) = Bound $ i - n - 1
    fromNeutral i (NVar n) = Free n
    fromNeutral i (NApp n v) = App (fromNeutral i n) (quote i v)
  
type Environment = [Value]

eval :: Environment -> Expr -> Value
eval ctxt expr =
  case expr of
    Int n -> VInt n
    String s -> VString s
    Char c -> VChar c
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
check i ctxt expr ty
  | Lam e <- expr =
      case ty of
        VPi tau tau' ->
          check
            (i+1)
            ((Local i, tau) : ctxt)
            (subst 0 (Free $ Local i) e)
            (tau' . VNeutral $ NVar $ Local i)
        _ -> Left $ NotAFunctionType $ quote 0 ty
  | otherwise = do
      ty' <- infer i ctxt expr
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
        Pi t e -> Pi (subst binder new t) (subst (binder+1) new e)
        Bound n -> if binder == n then new else orig
        App f x -> App (subst binder new f) (subst binder new x)
        Lam e -> Lam (subst (binder+1) new e)
        _ -> orig

infer :: Int -> Context -> Expr -> Either TypeError Value
infer i ctxt expr =
  case expr of
    Int _ -> pure . VNeutral . NVar $ Global "Int"
    Char _ -> pure . VNeutral . NVar $ Global "Char"
    String _ -> pure . VNeutral . NVar $ Global "String"
    TInt -> pure VType
    TChar -> pure VType
    TString -> pure VType
    Ann e rho -> do
      check i ctxt rho VType
      let tau = eval [] rho
      check i ctxt e tau
      pure tau
    Type -> pure VType
    Pi rho rho' -> do
      check i ctxt rho VType
      let tau = eval [] rho
      check
        (i+1)
        ((Local i, tau) : ctxt)
        (subst 0 (Free $ Local i) rho')
        VType
      pure VType
    Free name ->
      case lookup name ctxt of
        Just v -> pure v
        Nothing -> Left $ UnknownName name
    Bound a -> error $ "infer: unexpected " ++ show a
    App f x -> do
      tf <- infer i ctxt f
      case tf of
        VPi tau tau' -> do
          check i ctxt x tau
          pure $ tau' (eval [] x)
        _ -> Left $ NotAFunction f $ quote 0 tf
    _ -> Left $ CannotInfer expr
