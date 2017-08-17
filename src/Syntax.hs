{-# language FlexibleContexts #-}
{-# language FlexibleInstances #-}
{-# language GADTs #-}
{-# language GeneralizedNewtypeDeriving #-}
module Syntax where
import Debug.Trace

import Bound
import Bound.Name
import Control.Applicative
import Control.Arrow
import Control.Lens hiding (Empty)
import Control.Monad.State
import Data.Foldable
import Data.Graph
import Data.Map (Map)
import Data.Maybe
import GHC.Stack
import Text.Trifecta

import qualified Data.Map as M

import Eval
import Expr
import Decl
import Module

sccRFromMap :: Ord k => Map k (n, [k]) -> [SCC (n, k, [k])]
sccRFromMap = stronglyConnCompR . fmap (\(k, (n, ks)) -> (n, k, ks)) . M.toList

-- | Given an immutable context, perform mutually recursive substitution on a group
-- of bindings.
--
-- Examples
--
-- Given @substitute :: Map String String@ such that:
--
-- >>> substitute (M.fromList [("A", "B"), ("C", "D")]) [("E", "(A)"), ("F", "1234(C)")]
-- M.fromList [("E", "B"), ("F", "1234D")]
--
-- Then:
--
-- >>> substituteMutually substitute (M.fromList [("A", "1234"), ("B", "5678")]) [("C", "(A)(D)"), ("D", "(B)"]
-- M.fromList [("C", "12345678"), ("D", "5678")]
--
-- >>> substituteMutually substitute [] [("A", "a(A)")]
-- M.fromList ["A", "aaaaaaaaaaaaaaaaaaaaaaaaaa^CInterrupted
--
-- >>> take 10 . fromJust . M.lookup "A" $ substituteMutually substitute [] [("A", "a(B)"), ("B", "b(B)")]
-- "ababababab"
substituteMutually
  :: Ord a
  => (Map a c -> b -> c)
  -> Map a c
  -> [(a, b)]
  -> Map a c
substituteMutually f = go M.empty
  where
    go result _ [] = result
    go result ctxt ((n, ex):rest) =
      let
        ex' = f (result' `M.union` ctxt') ex
        ctxt' = M.insert n ex' ctxt
        result' = go result ctxt' rest
      in M.insert n ex' result'

-- | Given a list of strongly connected compoents (of type Syntax Expr) in topological order,
-- | reify them in order.
buildGrammar :: Alternative m => [SCC (Syntax Expr, String, [String])] -> m (Syntax Expr)
buildGrammar [] = empty
buildGrammar [e] =
  case e of
    (AcyclicSCC (ex, _, _)) -> pure ex
    (CyclicSCC []) -> error "no elements in cyclic scc"
    (CyclicSCC ((ex, _, _) : _)) -> pure ex
buildGrammar (a:rest) =
  liftA2 (<|>) (buildGrammar rest) (buildGrammar [a])
  
addRule :: (Alternative m, MonadState SyntaxRules m) => SCC (Expr, String, [String]) -> m ()
addRule e =
  case e of
    (AcyclicSCC (ex, n, deps)) -> do
      ctxt <- gets (fmap fst . exprRules)
      let ex' = reifyExprSyntax ctxt ex
      modify $ \s -> s { exprRules = M.insert n (ex', deps) $ exprRules s }
    (CyclicSCC vs) -> do
      ctxt <- gets (fmap fst . exprRules)
      let vs' = substituteMutually reifyExprSyntax ctxt $ (\(a, b, _) -> (b, a)) <$> vs
      let deps = M.elems . M.fromList $ (\(_, b, c) -> (b, c)) <$> vs
      modify $ \s -> s { exprRules = M.fromList (zipWith (\(a, b) c -> (a, (b, c))) (M.toList vs') deps) `M.union` exprRules s }

        {-
buildGrammar sccs =
  case sccs of
    (AcyclicSCC (ex, n, deps):rest) -> do
      ctxt <- gets (fmap fst . exprRules)
      let ex' = reifyExprSyntax ctxt ex
      modify $ \s -> s { exprRules = M.insert n (ex', deps) $ exprRules s }
      fmap (<|> ex') (buildGrammar rest)
    (CyclicSCC vs:rest) -> do
      ctxt <- gets (fmap fst . exprRules)
      let vs' = substituteMutually reifyExprSyntax ctxt $ (\(a, b, _) -> (b, a)) <$> vs
      let deps = M.elems . M.fromList $ (\(_, b, c) -> (b, c)) <$> vs
      modify $ \s -> s { exprRules = M.fromList (zipWith (\(a, b) c -> (a, (b, c))) (M.toList vs') deps) `M.union` exprRules s }
      case vs of
        [] -> buildGrammar rest
        ((_, n, _):_) -> fmap (<|> fromJust (M.lookup n vs')) (buildGrammar rest) -}

data SyntaxRules
  = SyntaxRules
  { exprGrammar :: Syntax Expr
  , exprRules :: Map String (Syntax Expr, [String])
  , declRules :: Map String (Syntax Decl, [String])
  , moduleRules :: Map String (Syntax Module, [String])
  }

newtype Syntax a
  = Syntax
  { unSyntax :: StateT SyntaxRules Parser a
  } deriving
  ( Functor, Applicative, Monad, MonadState SyntaxRules
  , Alternative, MonadPlus
  , Parsing, CharParsing
  )

instance TokenParsing Syntax where
  someSpace = skipSome $ satisfy (`elem` " \t")

liftParser :: Parser a -> Syntax a
liftParser = Syntax . lift

-- | Assumes that the AST is well-formed and has type `Syntax Expr`
reifyExprSyntax :: HasCallStack => Map String (Syntax Expr) -> Expr -> Syntax Expr
reifyExprSyntax ctxt e = go1 $ eval e
  where
    go1 :: HasCallStack => Expr -> Syntax Expr
    go1 =
      outside _Var
        .~ (\n -> fromMaybe (error "name not found") $ M.lookup n ctxt) $
      outside (_Con1 "Pure")
        .~ (pure . eval) $

      outside (_Con2 "Bind")
        .~ (\(sa, f) -> go2 sa >>= go2 . eval . App f) $

      outside (_Con2 "Map")
        .~ (\(f, sa) -> eval . App f <$> go2 sa) $

      outside (_Con2 "Discard")
        .~ (\(sa, sb) -> go2 sa >> go2 sb) $

      error . ("invalid argument: "++) . show

    go2 :: HasCallStack => Expr -> Syntax Expr
    go2 =
      outside (_Con1 "Symbol"._String) .~ (fmap String . symbol) $
      outside (_Con1 "Satisfy"._Lam') .~ (\(_, body) ->
        fmap Char . satisfy $
          \a -> case eval $ instantiate1 (Char a) body of
            Ctor "True" -> True
            Ctor "False" -> False
            res -> error $ "invalid result: " ++ show res) $
      go1

reifyDeclSyntax :: HasCallStack => Expr -> Syntax Decl
reifyDeclSyntax = undefined

reifyModuleSyntax :: HasCallStack => Expr -> Syntax Module
reifyModuleSyntax = undefined

expr :: Syntax Expr
expr = join $ gets exprGrammar

syntax :: Syntax ()
syntax = syntaxExpr <|> syntaxDecl <|> syntaxModule
  where
    syntaxExpr = do
      _ <- symbol "%%syntax expr"
      es <- braces $
        sepEndBy1
          (liftA2 (,) identifier $ symbol "=" *> token expr)
          newline
      let
        deps = es ^..
          folded .
          alongside id (to $ id &&& (^.. cosmos._Var))
      traverse_ addRule (sccRFromMap $ M.fromList deps)
      rules <- gets exprRules
      grammar <- buildGrammar (sccRFromMap rules) 
      modify $ \s -> s { exprGrammar = grammar }

    syntaxDecl = do
      _ <- symbol "%%syntax decl"
      es <- braces $
        sepEndBy1
          (liftA2 (,) identifier $ symbol "=" *> token expr)
          newline
      let
        deps = es ^..
          folded .
          alongside id (to $ reifyDeclSyntax &&& (^.. cosmos._Var))

      modify $
        \s -> s { declRules = M.fromList deps `M.union` declRules s }

    syntaxModule = do
      _ <- symbol "%%syntax module"
      es <- braces $
        sepEndBy1
          (liftA2 (,) identifier $ symbol "=" *> token expr)
          newline
      let
        deps = es ^..
          folded .
          alongside id (to $ reifyModuleSyntax &&& (^.. cosmos._Var))

      modify $
        \s -> s { moduleRules = M.fromList deps `M.union` moduleRules s }

decl :: Syntax Decl
decl =
  (token syntax *> some newline *> decl) <|> (do
    rules <- gets (choice . toListOf (folded._1) . declRules)
    (rules <* many newline))

module' :: Syntax Module
module' = do
  rules <- gets (choice . toListOf (folded._1) . moduleRules)
  (syntax *> many newline *> module') <|> rules

identifier :: Syntax String
identifier = token (liftA2 (:) lower $ many letter)

buildDefaultGrammar :: Syntax ()
buildDefaultGrammar = do
  grammar <-
    go (sccRFromMap defaultExprRules)
  modify $ \s -> s { exprGrammar = grammar }
  where
    go
      :: MonadState SyntaxRules m
      => [SCC (Syntax Expr, String, [String])] -> m (Syntax Expr)
    go [] = pure empty
    go (AcyclicSCC (e, name, deps) : rest) = do
      modify $ \s -> s { exprRules = M.insert name (e, deps) $ exprRules s }
      fmap (<|> e) $ go rest
    go (CyclicSCC [] : rest) = go rest
    go (CyclicSCC vs : rest) = do
      modify $ \s -> s { exprRules =
        M.union (M.fromList $ (\(a, b, c) -> (b, (a, c))) <$> vs) $ exprRules s }
      case vs of
        [] -> go rest
        ((e, _, _) : _) -> fmap (<|> e) $ go rest

defaultExprRules :: Map String (Syntax Expr, [String])
defaultExprRules =
  M.fromList
    [ ( "__exprStart_internal"
      , ( exprStart
        , [ "__pi_internal"
          , "__lam_internal"
          , "__quote_internal"
          , "__ann_internal"
          , "__app_internal"
          , "__lit_internal"
          , "__var_internal"
          , "__ctor_internal"
          ]
        )
      )
    , ("__pi_internal", (pi, ["__annRhs_internal"]))
    , ( "__annRhs_internal"
      , ( annRhs
        , [ "__lam_internal"
          , "__ann_internal"
          , "__app_internal"
          , "__quote_internal"
          , "__var_internal"
          , "__lit_internal"
          , "__ctor_internal"
          ]
        )
      )
    , ("__lam_internal", (lam, []))
    , ("__app_internal", (try app, ["__appLhs_internal", "__appRhs_internal"]))
    , ( "__appLhs_internal"
      , ( appLhs
        , [ "__quote_internal"
          , "__var_internal"
          , "__lit_internal"
          , "__ctor_internal"
          ]
        )
      )
    , ( "__appRhs_internal"
      , ( appRhs
        , [ "__quote_internal"
          , "__var_internal"
          , "__lit_internal"
          , "__ctor_internal"
          ]
        )
      )
    , ( "__ann_internal"
      , ( try ann
        , [ "__annLhs_internal"
          , "__annRhs_internal"
          ]
        )
      )
    , ( "__annLhs_internal"
      , ( annLhs
        , [ "__lam_internal"
          , "__ann_internal"
          , "__app_internal"
          , "__quote_internal"
          , "__var_internal"
          , "__lit_internal"
          , "__ctor_internal"
          ]
        )
      )
    , ( "__annRhs_internal"
      , ( annRhs
        , [ "__ann_internal"
          , "__app_internal"
          , "__quote_internal"
          , "__lam_internal"
          , "__lit_internal"
          , "__var_internal"
          , "__ctor_internal"
          ]
        )
      )
    , ( "__quote_internal"
      , ( quote
        , [ "__quote_internal"
          , "__var_internal"
          , "__ctor_internal"
          , "__lit_internal"
          , "__pi_internal"
          , "__lam_internal"
          , "__app_internal"
          , "__ann_internal"
          ]
        )
      )
    , ("__var_internal", (var, []))
    , ("__ctor_internal", (ctor, []))
    , ("__lit_internal", (lit, []))
    , ("__bracketed_internal", (between (symbol "(") (symbol ")") (token expr), []))
    ]
  where
    exprStart =
      pi <|>
      lam <|>
      quote <|>
      parens expr <|>
      try ann <|>
      try app <|>
      lit <|>
      var <|>
      ctor
      
    var = Var <$> identifier
    quote = do
      _ <- try $ char '\''
      fmap Quote $
        quote <|>
        var <|>
        ctor <|>
        lit <|>
        between (char '(') (char ')')
          (pi <|>
          lam <|>
          try app <|>
          try ann)

    appRhs =
      between (symbol "(") (symbol ")") (token expr) <|> -- (token $ lam <|> try app <|> pi <|> ann) <|>
      quote <|>
      var <|>
      lit <|>
      ctor

    appLhs =
      between (symbol "(") (symbol ")") (token expr) <|> -- (token $ lam <|> try ann <|> app) <|>
      quote <|>
      var <|>
      lit <|>
      ctor

    app = do
      l <- token appLhs
      rs <- some $ token appRhs
      pure $ foldl App l rs

    annLhs =
      between (symbol "(") (symbol ")") (token $ lam <|> ann <|> try app) <|>
      quote <|>
      var <|>
      lit <|>
      ctor

    annRhs =
      between (symbol "(") (symbol ")") (token ann) <|>
      try app <|>
      quote <|>
      lam <|>
      var <|>
      lit <|>
      ctor

    ann = Ann <$> (token annLhs <* symbol ":") <*> token annRhs

    ctor = Ctor <$> token (liftA2 (:) upper $ many letter)

    lit =
      (Char <$> try charLiteral) <|>
      (String <$> stringLiteral)

    pi = do
      _ <- symbol "pi"
      (n, f) <- token . between (symbol "(") (symbol ")") $ do
        n <- token $ some letter
        _ <- symbol ":"
        (,) n . Pi n <$> token annRhs
      _ <- symbol "."
      f . abstract1Name n <$> token expr

    lam = do
      _ <- symbol "lam"
      n <- token $ some letter
      _ <- symbol "."
      Lam n . abstract1Name n <$> token expr

defaultDeclRules :: Map String (Syntax Decl, [String])
defaultDeclRules =
  M.fromList 
  [ ("__decl_internal", (decl, [])) ]
  where
    decl = do
      n <- token $ liftA2 (:) lower (many letter)
      _ <- symbol ":"
      ty <- token expr
      _ <- newline
      _ <- symbol n
      _ <- symbol "="
      val <- token expr
      pure $ DeclBinding n val ty

defaultModuleRules :: Map String (Syntax Module, [String])
defaultModuleRules =
  M.fromList
  [ ("__module_internal", (Module <$> sepEndBy1 decl (some newline), [])) ]
