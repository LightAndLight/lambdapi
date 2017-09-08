{-# language DeriveFunctor #-}
{-# language FlexibleContexts #-}
{-# language FlexibleInstances #-}
{-# language GADTs #-}
{-# language GeneralizedNewtypeDeriving #-}
module Syntax where

import Bound
import Bound.Name
import Control.Applicative
import Control.Lens hiding (Empty)
import Control.Monad.State
import Data.Foldable
import Data.Functor
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

parseModule :: String -> Result Module
parseModule =
  let parser =
        flip evalStateT defaultSyntaxRules .
        unSyntax $
        buildParser =<< module'
  in parseString parser mempty

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

data SyntaxRules
  = SyntaxRules
  { exprRules :: [ParseProgram Expr -> ParseProgram Expr]
  , declRules :: [ParseProgram Decl -> ParseProgram Expr -> ParseProgram Decl]
  , moduleRules :: [ParseProgram Module -> ParseProgram Decl -> ParseProgram Module]
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

reifyFunction :: HasCallStack => Expr -> (Expr -> Expr)
reifyFunction =
  outside _Lam'
    .~ (\(_, e) ex -> eval $ instantiate1 ex e) $
  outside _Pi'
    .~ (\(_, _, e) ex -> eval $ instantiate1 ex e) $

  (error . ("Non-function passed to reifyFunction: " ++) . show)

isUnit :: HasCallStack => Expr -> Expr
isUnit =
  outside (_Con0 "Unit") .~ const (Ctor "Unit") $
  (error . ("Unit was not passed to reifyUnit: " ++) . show)

-- | Assumes that the AST is well-formed and has type `Syntax Expr`
reifyExprSyntax
  :: HasCallStack
  => Map String (ParseProgram Expr)
  -> Expr
  -> ParseProgram Expr
reifyExprSyntax ctxt e = go1 $ eval e
  where

    go1 :: HasCallStack => Expr -> ParseProgram Expr
    go1 =
      outside _Var
        .~ (\n -> fromMaybe (error "name not found") $ M.lookup n ctxt) $

      outside (_Con1 "Pure")
        .~ Pure . eval $

      outside (_Con2 "Bind")
        .~ (\(ma, f) ->
              Bind (go2 ma) (\a -> go2 . eval . App f $ _Quoted # a)) $

      outside (_Con2 "Map")
        .~ (\(f, ma) -> Map (\a -> eval . App f $ _Quoted # a) $ go2 ma) $

      outside (_Con2 "Choice")
        .~ (\(ma, ma') -> Choice (go2 ma) $ go2 ma') $

      outside (_Con0 "Empty")
        .~ const Empty $

      outside (_Con2 "Apply")
        .~ (\(mf, ma) -> Apply (reifyFunction <$> go2 mf) $ go2 ma) $

      outside (_Con1 "Try")
        .~ (Try . go2) $

      outside (_Con2 "Named" . _Mk2 id _String)
        .~ (\(ma, s) -> Named (go2 ma) s) $

      outside (_Con1 "Unexpected" . _String)
        .~ Unexpected $

      error . ("invalid argument: "++) . show

    go2 :: HasCallStack => Expr -> ParseProgram Expr
    go2 =
      outside (_Con1 "NotFollowedBy")
        .~ (\ma -> isUnit <$> go2 ma) $

      outside (_Con0 "SomeSpace")
        .~ (\_ -> SomeSpace $> Ctor "Unit") $

      outside (_Con1 "Symbol" . _String)
        .~ (\s -> Symbol s $> String s) $

      outside (_Con0 "Eof")
        .~ const (Eof $> Ctor "Unit")$

      outside (_Con1 "Satisfy"._Lam') .~ (\(_, body) ->
        fmap Char . satisfy $
          \a -> case eval $ instantiate1 (Char a) body of
            Ctor "True" -> True
            Ctor "False" -> False
            res -> error $ "invalid result: " ++ show res) $

      go1

reifyDeclSyntax :: HasCallStack => Expr -> ParseProgram Decl
reifyDeclSyntax = undefined

reifyModuleSyntax :: HasCallStack => Expr -> ParseProgram Module
reifyModuleSyntax = undefined

buildParser :: (Monad m, TokenParsing m) => ParseProgram a -> m a
buildParser p =
  case p of
    Choice a1 a2 -> buildParser a1 <|> buildParser a2
    Empty -> empty
    Pure a -> pure a
    Map f a -> f <$> buildParser a
    Apply a1 a2 -> buildParser a1 <*> buildParser a2
    Bind a1 a2 -> buildParser a1 >>= buildParser . a2
    Try a -> try $ buildParser a
    Named a1 a2 -> buildParser a1 <?> a2
    NotFollowedBy a -> notFollowedBy $ buildParser a
    Unexpected a -> unexpected a
    Eof -> eof
    Satisfy a -> satisfy a
    Symbol s -> symbol s
    SomeSpace -> someSpace

syntax :: Syntax ()
syntax = syntaxExpr <|> syntaxDecl <|> syntaxModule
  where
    syntaxExpr = do
      _ <- symbol "%%syntax expr"
      es <- braces $
        sepEndBy1
          (liftA2
             (,)
             (token identifier)
             (symbol "=" *> token (expr >>= buildParser)))
          newline
      let
        substituted =
          substituteMutually
            (\m b -> fromMaybe b $ (b ^? _Var) >>= flip M.lookup m)
            M.empty
            es
        reified = reifyExprSyntax M.empty <$> toList substituted
      modify $ \s -> s { exprRules = exprRules s ++ fmap const reified }

    syntaxDecl = do
      _ <- symbol "%%syntax decl"
      es <- braces $
        sepEndBy1
          (liftA2
            (,)
            identifier
            (symbol "=" *> token (expr >>= buildParser)))
          newline
      let
        substituted =
          substituteMutually
            (\m b -> fromMaybe b $ (b ^? _Var) >>= flip M.lookup m)
            M.empty
            es
        reified = reifyDeclSyntax <$> toList substituted
      modify $
        \s -> s { declRules = fmap (const . const) reified ++ declRules s }

    syntaxModule = do
      _ <- symbol "%%syntax module"
      es <- braces $
        sepEndBy1
          (liftA2
            (,)
            identifier
            (symbol "=" *> token (expr >>= buildParser)))
          newline
      let
        substituted =
          substituteMutually
            (\m b -> fromMaybe b $ (b ^? _Var) >>= flip M.lookup m)
            M.empty
            es
        reified = reifyModuleSyntax <$> toList substituted
      modify $
        \s -> s { moduleRules = fmap (const . const) reified ++ moduleRules s }

expr :: Syntax (ParseProgram Expr)
expr = do
  rules <- gets exprRules
  let e = asum $ fmap ($ e) rules
  pure e

decl :: Syntax (ParseProgram Decl)
decl = someSyntax <|> aDecl
  where
    someSyntax = token syntax *> some newline *> decl
    aDecl = do
      ds <- gets declRules
      e <- expr

      let d = asum $ fmap (($ e) . ($ d)) ds
      pure d

module' :: Syntax (ParseProgram Module)
module' = someSyntax <|> aModule
  where
    someSyntax = token syntax *> some newline *> module'
    aModule = do
      ms <- gets moduleRules
      d <- decl

      let m = asum $ fmap (($ d) . ($ m)) ms
      pure m

identifier :: TokenParsing m => m String
identifier = token (liftA2 (:) lower $ many letter)

defaultSyntaxRules :: SyntaxRules
defaultSyntaxRules =
  SyntaxRules
  { exprRules = defaultExprRules
  , declRules = defaultDeclRules
  , moduleRules = defaultModuleRules
  }

data ParseProgram a where
  Choice :: ParseProgram a -> ParseProgram a -> ParseProgram a
  Empty :: ParseProgram a
  Pure :: a -> ParseProgram a
  Map :: (a -> b) -> ParseProgram a -> ParseProgram b
  Apply :: ParseProgram (a -> b) -> ParseProgram a -> ParseProgram b
  Bind :: ParseProgram a -> (a -> ParseProgram b) -> ParseProgram b
  Try :: ParseProgram a -> ParseProgram a
  Named :: ParseProgram a -> String -> ParseProgram a
  NotFollowedBy :: Show a => ParseProgram a -> ParseProgram ()
  Unexpected :: String -> ParseProgram a
  Eof :: ParseProgram ()
  Satisfy :: (Char -> Bool) -> ParseProgram Char
  Symbol :: String -> ParseProgram String
  SomeSpace :: ParseProgram ()

instance Functor ParseProgram where
  fmap = Map

instance Applicative ParseProgram where
  pure = Pure
  (<*>) = Apply

instance Alternative ParseProgram where
  empty = Empty
  (<|>) = Choice

instance Monad ParseProgram where
  (>>=) = Bind

instance Parsing ParseProgram where
  try = Try
  (<?>) = Named
  notFollowedBy = NotFollowedBy
  unexpected = Unexpected
  eof = Eof

instance CharParsing ParseProgram where
  satisfy = Satisfy

instance TokenParsing ParseProgram where
  someSpace = SomeSpace

defaultExprRules :: [ParseProgram Expr -> ParseProgram Expr]
defaultExprRules = [ exprStart ]
  where
    exprStart :: ParseProgram Expr -> ParseProgram Expr
    exprStart es =
      pi es <|>
      lam es <|>
      try (ann es) <|>
      try (app es) <|>
      atom es

    var :: ParseProgram Expr
    var = Var <$> identifier

    quote :: ParseProgram Expr -> ParseProgram Expr
    quote es = do
      _ <- try $ char '\''
      Quote <$> atom es

    atom :: ParseProgram Expr -> ParseProgram Expr
    atom es =
      between (symbol "(") (symbol ")") (token es) <|>
      quote es <|>
      var <|>
      lit <|>
      ctor

    app :: ParseProgram Expr -> ParseProgram Expr
    app es = chainl1 (token $ atom es) (pure App)

    ann :: ParseProgram Expr -> ParseProgram Expr
    ann es =
      Ann <$>
      (token (atom es) <* symbol ":") <*>
      token (try (app es) <|> atom es)

    ctor :: ParseProgram Expr
    ctor = Ctor <$> token (liftA2 (:) upper $ many letter)

    lit :: ParseProgram Expr
    lit =
      (Char <$> try charLiteral) <|>
      (String <$> stringLiteral)

    pi :: ParseProgram Expr -> ParseProgram Expr
    pi es = do
      _ <- symbol "pi"
      (n, f) <- token . between (symbol "(") (symbol ")") $ do
        n <- token $ some letter
        _ <- symbol ":"
        (,) n . Pi n <$> token (atom es)
      _ <- symbol "."
      f . abstract1Name n <$> token es

    lam :: ParseProgram Expr -> ParseProgram Expr
    lam es = do
      _ <- symbol "lam"
      n <- token $ some letter
      _ <- symbol "."
      Lam n . abstract1Name n <$> token es

defaultDeclRules
  :: [ParseProgram Decl -> ParseProgram Expr -> ParseProgram Decl]
defaultDeclRules = [ declStart ]
  where
    declStart _ es = do
      n <- token $ liftA2 (:) lower (many letter)
      _ <- symbol ":"
      ty <- token es
      _ <- newline
      _ <- symbol n
      _ <- symbol "="
      val <- token es
      pure $ DeclBinding n val ty

defaultModuleRules
  :: [ParseProgram Module -> ParseProgram Decl -> ParseProgram Module]
defaultModuleRules =
  [ \ms ds -> Module <$> sepEndBy1 ds (some newline) ]
