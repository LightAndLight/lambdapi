module Eval where

import Bound
import Control.Lens
import GHC.Stack

import Expr

eval :: HasCallStack => Expr -> Expr
eval =
  outside _Pi
    .~ (\(n, t, t') -> _Pi # (n, eval t, eval t')) $

  outside (_App._Mk2 _Lam' id)
    .~ (\((_, e), b) -> instantiate1 (eval b) e) $

  outside _Lam
    .~ (\(n, e) -> _Lam # (n, eval e)) $

  outside _AppCtor
    .~ (\(n, es) -> _AppCtor # (n, fmap eval es)) $

  outside _Ann .~ (eval . fst) $
  outside _Type .~ const Type $
  outside _Var .~ Var $
  outside _String .~ String $
  outside _Char .~ Char $
  outside _Ctor .~ Ctor $
  outside _Quote .~ id $
  error . ("invlid argument: " ++) . show
