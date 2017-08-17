module Module where

import Decl

data Module
  = Module
  { decls :: [Decl]
  } deriving (Eq, Show)
