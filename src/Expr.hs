{-# language DeriveFunctor #-}
{-# language DeriveFoldable #-}
{-# language DeriveTraversable #-}
{-# language FlexibleInstances #-}
{-# language LambdaCase #-}
{-# language RankNTypes #-}
{-# language TemplateHaskell #-}
module Expr where

import Bound
import Bound.Name
import Control.Monad
import Control.Lens
import Data.Deriving
import Data.Functor
import Data.Functor.Classes

-- | Type : Type is unsound and needs to be reworked with universe polymorphism
data ExprF n a
  = Ann (ExprF n a) (ExprF n a)
  | Pi n (ExprF n a) (Scope (Name n ()) (ExprF n) a)
  | App (ExprF n a) (ExprF n a)
  | Lam n (Scope (Name n ()) (ExprF n) a)
  | Var a
  | Type
  | String String
  | Char Char
  | Ctor String
  | Quote (ExprF n a)
  deriving (Functor, Foldable, Traversable)

instance Eq a => Plated (ExprF a a) where
  plate f =
    outside _Ann .~ (\(a, b) -> Ann <$> f a <*> f b) $
    outside _Pi
      .~ (\(n, a, b) -> fmap (review _Pi) $ (,,) n <$> f a <*> f b) $
    outside _App .~ (\(a, b) -> Ann <$> f a <*> f b) $
    outside _Lam
      .~ (\(n, a) -> fmap (review _Lam) $ (,) n <$> f a) $
    outside _Quote .~ (fmap Quote . f) $
    pure

instance (Eq a, Eq n) => Eq (ExprF n a) where (==) = eq1
instance (Show a, Show n) => Show (ExprF n a) where showsPrec = showsPrec1

instance Applicative (ExprF n) where
  pure = return
  (<*>) = ap

instance Monad (ExprF n) where
  return = Var

  Ann a b >>= f = Ann (a >>= f) (b >>= f)
  Type >>= _ = Type
  Pi n a b >>= f = Pi n (a >>= f) (b >>>= f)
  Var a >>= f = f a
  App a b >>= f = App (a >>= f) (b >>= f)
  Lam n a >>= f = Lam n (a >>>= f)
  String s >>= _ = String s
  Char c >>= _ = Char c
  Ctor a >>= _ = Ctor a
  Quote a >>= f = Quote (a >>= f)

type Expr = ExprF String String

_Lam :: Eq a => Prism' (ExprF a a) (a, ExprF a a)
_Lam =
  prism'
    (\(n, e) -> Lam n $ abstract1Name n e)
    (\case
        Lam n e -> Just (n, instantiate1 (Var n) e)
        _ -> Nothing)
    
_Lam' :: Prism' (ExprF a a) (a, Scope (Name a ()) (ExprF a) a)
_Lam' =
  prism'
    (uncurry Lam)
    (\case
        Lam n e -> Just (n, e)
        _ -> Nothing)

_Pi :: Eq a => Prism' (ExprF a a) (a, ExprF a a, ExprF a a)
_Pi =
  prism'
    (\(n, t, t') -> Pi n t $ abstract1Name n t')
    (\case
        Pi n t t' -> Just (n, t, instantiate1 (Var n) t')
        _ -> Nothing)

_Ann :: Prism' (ExprF a a) (ExprF a a, ExprF a a)
_Ann =
  prism'
    (uncurry Ann)
    (\case
        Ann a b -> Just (a, b)
        _ -> Nothing)

_Type ::  Prism' (ExprF a a) ()
_Type =
  prism'
    (const Type)
    (\case
        Type -> Just ()
        _ -> Nothing)

_Var ::  Prism' (ExprF a a) a
_Var =
  prism'
    Var
    (\case
        Var a -> Just a
        _ -> Nothing)

_App ::  Prism' (ExprF a a) (ExprF a a, ExprF a a)
_App =
  prism'
    (uncurry App)
    (\case
        App a b -> Just (a, b)
        _ -> Nothing)

_String ::  Prism' (ExprF a a) String
_String =
  prism'
    String
    (\case
        String a -> Just a
        _ -> Nothing)

_Char ::  Prism' (ExprF a a) Char
_Char =
  prism'
    Char
    (\case
        Char a -> Just a
        _ -> Nothing)

_Ctor ::  Prism' (ExprF a a) String
_Ctor =
  prism'
    Ctor
    (\case
        Ctor a -> Just a
        _ -> Nothing)

_AppCtor :: Prism' (ExprF a a) (String, [ExprF a a])
_AppCtor =
  prism'
    (\(n, es) -> foldl App (Ctor n) es)
    (\case
        Ctor n -> Just (n, [])
        App a b -> do
          (n, args) <- a ^? _AppCtor
          pure (n, args ++ [b])
        _ -> Nothing)

_Quote ::  Prism' (ExprF a a) (ExprF a a)
_Quote =
  prism'
    Quote
    (\case
        Quote a -> Just a
        _ -> Nothing)
    
_Con0 :: String -> Prism' (ExprF n a) ()
_Con0 s =
  prism'
    (const $ Ctor s)
    (\case
        Ctor s'
          | s' == s -> Just ()
        _ -> Nothing)

_Con1 :: String -> Prism' (ExprF n a) (ExprF n a)
_Con1 s =
  prism'
    (App $ _Con0 s # ())
    (\case
        App c e -> (c ^? _Con0 s) $> e
        _ -> Nothing)

_Con2 :: String -> Prism' (ExprF n a) (ExprF n a, ExprF n a)
_Con2 s =
  prism'
    (\(e1, e2) -> App (_Con1 s # e1) e2)
    (\case
        App e1 e2 -> (,) <$> e1 ^? _Con1 s <*> pure e2
        _ -> Nothing)

_Con3 :: String -> Prism' (ExprF n a) (ExprF n a, ExprF n a, ExprF n a)
_Con3 s =
  prism'
    (\(e1, e2, e3) -> App (_Con2 s # (e1, e2)) e3)
    (\case
        App e12 e3 -> uncurry (,,) <$> e12 ^? _Con2 s <*> pure e3
        _ -> Nothing)
_Mk2
  :: Prism' a a'
  -> Prism' b b'
  -> Prism' (a, b) (a', b')
_Mk2 pa pb =
  prism'
    (\(a', b') -> (pa # a', pb # b'))
    (\(a, b) -> (,) <$> a ^? pa <*> b ^? pb)
    
_Mk3
  :: Prism' a a'
  -> Prism' b b'
  -> Prism' c c'
  -> Prism' (a, b, c) (a', b', c')
_Mk3 pa pb pc =
  prism'
    (\(a', b', c') -> (pa # a', pb # b', pc # c'))
    (\(a, b, c) -> (,,) <$> a ^? pa <*> b ^? pb <*> c ^? pc)

_Quoted :: Prism' Expr Expr
_Quoted = prism' quote unquote
  where
    unquote :: Expr -> Maybe Expr
    unquote =
      outside (_Con2 "Ann")
        .~ (\(a, b) -> Ann <$> unquote a <*> unquote b) $

      outside (_Con0 "Type")
        .~ const (Just Type) $

      outside (_Con3 "Pi"._Mk3 _String id id)
        .~ (\(s, t, t') -> preview (_Just.re _Pi) $ (,,) s <$> unquote t <*> unquote t') $

      outside (_Con1 "Var"._String)
        .~ Just . Var $

      outside (_Con2 "App")
        .~ (\(a, b) -> App <$> unquote a <*> unquote b) $

      outside (_Con2 "Lam"._Mk2 _String id)
        .~ (\(s, e) -> preview (_Just.re _Lam) $ (,) s <$> unquote e) $

      outside (_Con1 "String"._String)
        .~ Just . String $

      outside (_Con1 "Char"._Char)
        .~ Just . Char $

      outside (_Con1 "Ctor"._String)
        .~ Just . Ctor $

      const Nothing

    quote :: Expr -> Expr
    quote e =
      case e of
        Ann a b -> _Con2 "Ann" # (quote a, quote b)
        Type -> _Con0 "Type" # ()
        Pi s t t' -> _Con3 "Pi"._Mk3 _String id id # (s, quote t, quote $ instantiate1 (Var s) t')
        Var a -> _Con1 "Var"._String # a
        App f x -> _Con2 "App" # (quote f, quote x)
        Lam s e -> _Con2 "Lam"._Mk2 _String id # (s, quote $ instantiate1 (Var s) e)
        String a -> _Con1 "String"._String # a
        Char a -> _Con1 "Char"._Char # a
        Ctor s -> _Con1 "Ctor"._String # s
        Quote q -> _Con1 "Quote" # quote q
        
printExpr :: Expr -> String
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
    String s -> show s
    Char c -> show c
    Ctor s -> s
    Quote e -> "'(" ++ printExpr e ++ ")"

deriveEq1 ''ExprF
deriveShow1 ''ExprF
