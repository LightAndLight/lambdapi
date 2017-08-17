module Decl where

import Expr

data Decl
  = DeclBinding
  { bindingName :: String
  , bindingValue :: Expr
  , bindingType :: Expr
  }
  | DeclSyntax
  { syntaxValue :: Expr
  } deriving (Eq, Show)
