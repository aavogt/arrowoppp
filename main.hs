module Main (main) where

import Control.Lens hiding (re)
import Control.Monad
import Data.Char
import Data.Data
import Data.IntMap (IntMap)
import Data.List
import Data.Maybe
import Data.Monoid
import Debug.Trace
import GHC.TypeLits
import System.Environment
import System.Exit
import Test.Hspec
import Text.Regex.Applicative

main = do
  args@(~(originalName : input : output : (listToMaybe -> mPrefix))) <- getArgs
  unless (length args `elem` [3, 4]) $ do
    putStrLn
      "Usage: arrowoppp originalName input output [alternateStarPrefix] \n\n\
      \ If *x should be !(readIORef x) or writeIORef x:\n\
      \ {-# OPTIONS_GHC -F -pgmF arrowoppp -fplugin=MonadicBang #-}\n\n\
      \ For better compatibility with haskell-language-server, use a letter prefix such as v: \n\
      \ {-# OPTIONS_GHC -F -pgmF arrowoppp -optF v -fplugin=MonadicBang #-}"
    exitFailure
  input <- readFile input
  let linePragma = "{-# LINE 1 " ++ show originalName ++ " #-}\n"

  writeFile output $ linePragma ++ let ?star = fromMaybe "*" mPrefix in p input s0

item input output = it input $ p input s0 `shouldBe` output

itemId input = item input input

test =
  let ?star = "*"
   in hspec $ do
        let itemId input = item input input
        describe "lowercase variables" $ do
          item "x * y" "x * y"
          item "x *y" "x !(readIORef y)"
          item " *x->y" " !(readIORef !(readIORef x).y)"
          item " *x" " !(readIORef x)"
          item " *x->y" " !(readIORef !(readIORef x).y)"
          item " x->y" " !(readIORef x).y"
          item " x->y->z" " !(readIORef !(readIORef x).y).z"
          item "let w = 2 * pi * *sr.freq / 48000" "let w = 2 * pi * !(readIORef sr.freq) / 48000"
          item "let w = *x\n-- x\nlet imax = round (48000 * (*sr.on + *sr.off) * fromIntegral n) `div` n" "let w = !(readIORef x)\n-- x\nlet imax = round (48000 * (!(readIORef sr.on) + !(readIORef sr.off)) * fromIntegral n) `div` n"

        describe "ignores sigs" $ do
          itemId "a :: x -> y"
          itemId "a :: x->y"
          itemId "a :: x -> y -> z"
          itemId "do x :: a -> b <- y"
        describe "ignores <*>" $ do
          itemId "f <$> x <*> y"
        describe "linear package operator" $ do
          itemId "f *^ y"
        describe "qual" $ do
          item " X.e->Y.e" " !(readIORef X.e).Y.e"
          item " X.e->e" " !(readIORef X.e).e"
          item " e->Y.e" " !(readIORef e).Y.e"
        describe "ident" $ do
          it "stops" $ ident "X.y.e" `shouldBe` Just ("X.y", ".e")
          it "goes" $ ident "X.y" `shouldBe` Just ("X.y", "")
          it "caps" $ ident "X.Y" `shouldBe` Just ("X.Y", "")
          it "stops2" $ ident "x.y" `shouldBe` Just ("x", ".y")

        describe "assignment" $ do
          item "do *x <- y" "do writeIORef x =<<  y"
          item "do *x = y" "do writeIORef x $  y"
          item "do let *x = y" "do x <- newIORef $  y"
          item "do when (*x == 3)" "do when (!(readIORef x) == 3)"
          item "do *x=y" "do writeIORef x $ y"
          item "do *x==y" "do !(readIORef x)==y"
          item "do (x, *y) = rhs" "do (x, _) <- _2 (writeIORef y) $ rhs"
          item "do (x, *y) <- guiSpinner *y" "do (x, _) <- _2 (writeIORef y) =<< rhs"

-- TODO: * -> .

s0 = S 0 0 []

-- parser state
data S = S
  { paren, blockComment :: !Int,
    -- | value of `paren` when starting a ::
    -- does it play nicely with kind signatures?
    -- x::y::z doesn't happen, it's always e :: (t :: k)
    --
    -- but there is a problem with PatternSignatures
    --
    -- p::t <- expression
    --
    -- so <- can end a type signature
    -- can <- be in a type signature?
    sig :: [Int]
  }

incSig, tryDecSig, incParen, decParen, incBC, decBC :: S -> S
incSig s = s {sig = paren s : sig s}
tryDecSig s = fromMaybe s (decSig s)
incParen s = s {paren = paren s + 1}
decParen s = s {paren = paren s - 1}
incBC s = s {blockComment = blockComment s + 1}
decBC s = s {blockComment = blockComment s - 1}

decSig :: S -> Maybe S
decSig s@S {sig = x : xs, paren = (x <=) -> True} =
  Just s {sig = xs}
decSig _ = Nothing

p (stripPrefix "-}" -> Just x) s = "-}" ++ p x (decBC s)
p (stripPrefix "{-" -> Just x) s = "{-" ++ p x (incBC s)
p (x : xs) s | blockComment s > 0 = x : p xs s
p (stringLit -> Just (a, b)) s = a ++ p b s
p (dashComment -> Just (a, b)) s = a ++ p b s
p (c : (pointerPat -> Just (Just r, z))) s@S {sig = []} | c `elem` "( " = c : r <> p z s
p (c : (pointerExp -> Just (r, z))) s@S {sig = []} | c `elem` "( " = c : r <> p z s
p (stripPrefix "::" -> Just x) s = "::" ++ p x (incSig s)
p (stripPrefix "<-" -> Just x) s = "<-" ++ p x (tryDecSig s) -- end of Pat
p ('=' : xs) s = '=' : p xs s {sig = []} -- end of Pat
p ('\n' : xs) (decSig -> Just s) = '\n' : p xs s
p ('(' : xs) s = '(' : p xs (incParen s)
p (')' : xs) s = ')' : p xs (tryDecSig (decParen s))
p (x : xs) s = x : p xs s
p [] _ = []

-- assume typedecls go up to "\n\n", which isn't quite true
typedecl = findLongestPrefix $ do
  keyword <- string "data" <|> string "newtype"
  body <- many $ do
    a <- psym (/= '\n')
    b <- optional (sym '\n')
    pure (maybe [a] (\b -> [a, b]) b)
  pure (keyword ++ concat body)

dashComment = findLongestPrefix ((<>) <$> string "--" <*> many (psym (/= '\n')))

-- | matches a pointer expression, e.g. "*?a.b->c"
pointerRE = do
  star <- length <$> many (string ?star) -- ' '
  implicit <- optional $ sym '?'
  var1 <- qualIdent
  oprs <- many $ do
    op <- string "." <|> string "->"
    r <- qualIdent
    pure (op, r)
  pure (star, maybe id (:) implicit var1, oprs)

-- | the incomplete core of arrowoppp for patterns
pointerPat :: (_) => String -> Maybe (Maybe String, [Char])
pointerPat =
  pushBack . findLongestPrefix do
    letStr <- optional $ (<>) (string "let") (many (psym isSpace))
    ~((n, a, ope), naope) <- withMatched pointerRE -- ApplicativeDo needs irrefutable patterns
    s <- many (psym isSpace)
    assignOp <- string "<-" <|> string "="
    s2 <- psym (not . isSymbol)
    pure
      ( case assignOp of
          "<-" | n == 1 -> Just ("writeIORef " <> a <> " =<< ")
          "=" | Just l <- letStr, n == 1 -> Just (a <> " <- newIORef $ ")
          "=" | n == 1 -> Just ("writeIORef " <> a <> " $ ")
          _ -> Nothing,
        s2
      )
  where
    -- there should be a better way to get a lookahead
    pushBack (Just ((Just x, c), xs)) = Just (Just x, c : xs)
    pushBack x = x & _Just . _1 %~ fst

-- | the core of arrowoppp for expressions:
--
-- > pointerExp "****a.b->c" = Just ("!(readIORef !(readIORef !(readIORef !(readIORef !(readIORef a.b).c))))", "")
-- via intermediate parse (4, "a", [(".", "b"), ("->", "c")])
pointerExp = findLongestPrefix (interpretPointerExp <$> pointerRE)
  where
    interpretPointerExp ::
      (Int, String, [(String, String)]) -> -- (stars, first var, [(op, var)])
      String
    interpretPointerExp (n, a, ope) = foldl addOpe a ope & addStars n

    -- the current expression x grows a bit with each op, y
    addOpe x (op, y) = case op of
      "->" -> "!(readIORef " <> x <> ")" <> "." <> y
      "." -> x <> "." <> y
      _ -> error $ "pointerExp impossible op:" <> op

    addStars n x = foldr (++) (x ++ replicate n ')') $ replicate n "!(readIORef "

ident x = findLongestPrefix qualIdent x

-- from HListPP
-- "ModuleName."
modNameDot = do
  m <- psym isUpper
  odName <- many (psym isAlpha <|> psym isDigit)
  dot <- sym '.'
  pure $ m : odName ++ [dot]

-- "M.Od.Ule.Name.something"
qualIdent = do
  modNames <- many modNameDot
  end <- identAlpha
  pure $ concat (modNames ++ [end])

identAlpha = do
  c <- psym isAlpha
  cs <- many (psym isAlphaNum <|> sym '\'')
  pure $ c : cs

stringLit = findLongestPrefix $ do
  a <- sym '"'
  b <-
    many $
      many (psym (`notElem` "\"\\"))
        <|> do
          e <- sym '\\'
          f <- anySym
          pure [e, f]
  c <- sym '"'
  pure $ a : concat b ++ [c]
