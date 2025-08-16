import Data.Char (isAlphaNum, isDigit, isSpace)
import Data.Fixed (mod')
import Data.List (findIndex, intercalate, partition)

import Data.Map qualified as Map
import Data.Set qualified as Set

import Control.Monad (void)
import System.Environment (getArgs)

--------------------------------------------------------------------------------
-- DATA
--------------------------------------------------------------------------------

data SalVal
  = SalNil
  | SalBool Bool
  | SalKeyword SalKwI
  | SalNumber Double
  | SalString String
  | SalList [SalVal]
  | SalMap (Map.Map SalVal SalVal)
  | SalMacro SalMcI
  | SalFunction SalFnI

instance Show SalVal where
  show :: SalVal -> String
  show SalNil = "nil"
  show (SalBool a) = show a
  show (SalKeyword a) = ':' : a
  show (SalNumber a) = show a
  show (SalString a) = a
  show (SalList a) = "[" ++ intercalate ", " (map show a) ++ "]"
  show (SalMap a) = "{" ++ intercalate ", " (map (\(k, v) -> show k ++ " " ++ show v) $ Map.assocs a) ++ "}"
  show (SalMacro _) = "<macro>"
  show (SalFunction _) = "<function>"

instance Eq SalVal where
  (==) :: SalVal -> SalVal -> Bool
  SalNil == SalNil = True
  SalBool a == SalBool b = a == b
  SalNumber a == SalNumber b = a == b
  SalString a == SalString b = a == b
  SalList a == SalList b = a == b
  SalMap a == SalMap b = a == b
  SalKeyword a == SalKeyword b = a == b
  _ == _ = False

instance Ord SalVal where
  compare :: SalVal -> SalVal -> Ordering
  SalBool a `compare` SalBool b = a `compare` b
  SalNumber a `compare` SalNumber b = a `compare` b
  SalString a `compare` SalString b = a `compare` b
  SalList a `compare` SalList b = a `compare` b
  SalMap a `compare` SalMap b = a `compare` b
  SalKeyword a `compare` SalKeyword b = a `compare` b
  _ `compare` _ = EQ

data SalAst
  = SalLit SalVal
  | SalLitList [SalAst]
  | SalLitMap [SalAst]
  | SalExp (SalKwI, [SalAst])
  | SalRef SalKwI

type SalKwI = String
type SalMcI = SalEnv -> [SalAst] -> IO (SalEnv, [SalAst])
type SalFnI = [SalVal] -> IO SalVal

type SalEnv = Map.Map SalKwI SalVal

--------------------------------------------------------------------------------
-- TOKENIZER
--------------------------------------------------------------------------------

tokenize :: String -> [String]
tokenize = tokenize' [] ""

tokenize' :: [String] -> String -> String -> [String]
tokenize' acc buf "" = reverse $ tokenize'flush acc buf
tokenize' acc buf code@('"' : _) =
  let (str, code') = tokenize'string code in tokenize' (str : tokenize'flush acc buf) "" code'
tokenize' acc buf (';' : code) =
  tokenize' (tokenize'flush acc buf) "" $ dropWhile (/= '\n') code
tokenize' acc buf (c : code)
  | Set.member c tokenize'brackets = tokenize' ([c] : tokenize'flush acc buf) "" code
  | isSpace c || c == ',' = tokenize' (tokenize'flush acc buf) "" code
  | otherwise = tokenize' acc (c : buf) code

tokenize'flush :: [String] -> String -> [String]
tokenize'flush acc "" = acc
tokenize'flush acc buf = reverse buf : acc

tokenize'string :: String -> (String, String)
tokenize'string code = case findIndex quote $ unpack code of
  Just index -> splitAt (index + 2) code
  Nothing -> error "String not closed"
 where
  quote (a, b) = a /= '\\' && b == '"'
  unpack str = zip str $ drop 1 str

tokenize'brackets :: Set.Set Char
tokenize'brackets = Set.fromList "()[]{}"

--------------------------------------------------------------------------------
-- PARSER
--------------------------------------------------------------------------------

parse :: [String] -> [SalAst]
parse = fst . parse' [] ""

parse' :: [SalAst] -> String -> [String] -> ([SalAst], [String])
parse' acc "" [] = (reverse acc, [])
parse' acc bp [] = error "Unexpected end of input"
parse' acc bp ("nil" : tok) = parse' (SalLit SalNil : acc) bp tok
parse' acc bp ("true" : tok) = parse' (SalLit (SalBool True) : acc) bp tok
parse' acc bp ("false" : tok) = parse' (SalLit (SalBool False) : acc) bp tok
parse' acc bp ((':' : kw) : tok) = parse' (SalLit (SalKeyword kw) : acc) bp tok
parse' acc bp (('"' : str) : tok) = parse' (SalLit (SalString (init str)) : acc) bp tok
parse' acc bp ("[" : tok) = let (ast, tok') = parse' [] "]" tok in parse' (SalLitList ast : acc) bp tok'
parse' acc bp ("{" : tok) = let (ast, tok') = parse' [] "}" tok in parse' (SalLitMap (parse'map ast) : acc) bp tok'
parse' acc bp ("(" : kw : tok) = let (ast, tok') = parse' [] ")" tok in parse' (SalExp (kw, ast) : acc) bp tok'
parse' acc bp (t : tok)
  | t == bp = (reverse acc, tok)
  | parse'isNumber t = parse' (SalLit (SalNumber (read t)) : acc) bp tok
  | parse'isRef t = parse' (SalRef t : acc) bp tok
  | otherwise = error "Syntax error"

parse'map :: [SalAst] -> [SalAst]
parse'map ast = if even (length ast) then ast else error "Map literal must contain an even number of forms"

parse'isNumber :: String -> Bool
parse'isNumber (h : t) = isDigitNeg h && all isDigitDot t && dotCount t <= 1
 where
  isDigitNeg n = isDigit n || n == '-'
  isDigitDot n = isDigit n || n == '.'
  dotCount = length . filter (== '.')

parse'isRef :: String -> Bool
parse'isRef token@(h : _) = not (isDigit h) && all isAlphaNumSym token
 where
  isAlphaNumSym n = isAlphaNum n || Set.member n keywordSymbols
  keywordSymbols = Set.fromList "_+-*/<>='"

--------------------------------------------------------------------------------
-- RUNNER
--------------------------------------------------------------------------------

run :: SalEnv -> [SalAst] -> IO (SalEnv, [SalVal])
run = run' []

run' :: [SalVal] -> SalEnv -> [SalAst] -> IO (SalEnv, [SalVal])
run' acc env [] = return (env, reverse acc)
run' acc env (SalLit val : ast) = run' (val : acc) env ast
run' acc env (SalLitList ast' : ast) = run env ast' >>= \(env', vals) -> run' (SalList vals : acc) env' ast
run' acc env (SalLitMap ast' : ast) = run env ast' >>= \(env', vals) -> run' (SalMap (run'map vals) : acc) env' ast
run' acc env (SalExp (kw, ast') : ast) = run'exp env kw ast' >>= \(env', vals) -> run' (vals ++ acc) env' ast
run' acc env (SalRef kw : ast) = run' (run'ref env kw : acc) env ast

run'map :: [SalVal] -> Map.Map SalVal SalVal
run'map vals =
  let (keys, values) = partition (even . fst) $ zip [0 ..] vals
   in Map.fromList $ zip (map snd keys) (map snd values)

run'exp :: SalEnv -> SalKwI -> [SalAst] -> IO (SalEnv, [SalVal])
run'exp env kw ast = case Map.lookup kw env of
  Just (SalMacro mc) -> mc env ast >>= uncurry run
  Just (SalFunction fn) -> run env ast >>= fn . snd >>= \val -> return (env, [val])
  _ -> error ("`" ++ kw ++ "` is not a function")

run'ref :: SalEnv -> SalKwI -> SalVal
run'ref env kw = case Map.lookup kw env of
  Just val -> val
  Nothing -> error ("Undefined variable `" ++ kw ++ "`")

--------------------------------------------------------------------------------
-- PRELUDE
--------------------------------------------------------------------------------

-- Helpers

sal'castBool :: SalVal -> Bool
sal'castBool (SalBool bool) = bool
sal'castBool SalNil = False
sal'castBool _ = True

sal'castNumber :: SalVal -> Double
sal'castNumber (SalNumber number) = number
sal'castNumber val = error ("`" ++ show val ++ "` is not a number")

sal'bool :: Bool -> IO SalVal
sal'bool = pure . SalBool

sal'number :: Double -> IO SalVal
sal'number = pure . SalNumber

sal'string :: String -> IO SalVal
sal'string = pure . SalString

sal'keyword :: SalKwI -> IO SalVal
sal'keyword = pure . SalKeyword

-- Macros

sal'if :: SalMcI
sal'if env [cond, true] = sal'if env [cond, true, SalLit SalNil]
sal'if env [cond, true, false] =
  run env [cond] >>= \(env', [val]) -> pure (env', if sal'castBool val then [true] else [false])

sal'fn :: SalMcI
sal'fn env ast@(SalLitList _ : (_ : _)) = sal'fn env (SalRef "" : ast)
sal'fn env (SalRef kw : SalLitList args'keys : ast@(_ : _)) = pure (env, [SalLit fn'])
 where
  fn' = SalFunction fn'cls
  fn'cls args'values = last . snd <$> run (fn'env args'values) ast
  fn'env args'values = foldl env'ref env' $ zip args'keys args'values
  env' = Map.insert "recur" fn' $ if kw == "" then env else Map.insert kw fn' env
  env'ref e (SalRef k, v) = Map.insert k v e

sal'def :: SalMcI
sal'def env [SalRef kw, ast] =
  run env [ast] >>= \(env', [val]) -> pure (Map.insert kw val env', [SalLit (SalKeyword kw)])

sal'defn :: SalMcI
sal'defn env ast@(ref@(SalRef _) : (args@(SalLitList _) : (_ : _))) =
  sal'fn env ast >>= \(env', ast') -> sal'def env' (ref : ast')

-- Functions

sal'println :: SalFnI
sal'println values = do
  putStrLn (unwords $ map show values)
  return SalNil

sal'type :: SalFnI
sal'type [val] = sal'keyword $ typeOf val
 where
  typeOf SalNil = "nil"
  typeOf (SalBool _) = "bool"
  typeOf (SalNumber _) = "number"
  typeOf (SalString _) = "string"
  typeOf (SalList _) = "list"
  typeOf (SalKeyword _) = "keyword"
  typeOf (SalMacro _) = "macro"
  typeOf (SalFunction _) = "function"

sal'nil :: SalFnI
sal'nil [value] = sal'bool $ value == SalNil

sal'sum :: SalFnI
sal'sum = sal'number . sum . map sal'castNumber
sal'sub :: SalFnI
sal'sub = sal'number . foldl1 (-) . map sal'castNumber
sal'mul :: SalFnI
sal'mul = sal'number . product . map sal'castNumber
sal'div :: SalFnI
sal'div = sal'number . foldl1 (/) . map sal'castNumber

sal'mod :: SalFnI
sal'mod [SalNumber a, SalNumber b] = sal'number $ mod' a b
sal'abs :: SalFnI
sal'abs [SalNumber a] = sal'number $ abs a

sal'inc :: SalFnI
sal'inc [SalNumber a] = sal'number $ succ a
sal'dec :: SalFnI
sal'dec [SalNumber a] = sal'number $ pred a

sal'max :: SalFnI
sal'max = sal'number . maximum . map sal'castNumber
sal'min :: SalFnI
sal'min = sal'number . minimum . map sal'castNumber

sal'gt :: SalFnI
sal'gt [SalNumber a, SalNumber b] = sal'bool $ a > b
sal'gte :: SalFnI
sal'gte [SalNumber a, SalNumber b] = sal'bool $ a >= b

sal'lt :: SalFnI
sal'lt [SalNumber a, SalNumber b] = sal'bool $ a < b
sal'lte :: SalFnI
sal'lte [SalNumber a, SalNumber b] = sal'bool $ a <= b

sal'eq :: SalFnI
sal'eq [a, b] = sal'bool $ a == b
sal'or :: SalFnI
sal'or = sal'bool . any sal'castBool
sal'and :: SalFnI
sal'and = sal'bool . all sal'castBool

sal'not :: SalFnI
sal'not [value] = sal'bool . not $ sal'castBool value
sal'noteq :: SalFnI
sal'noteq [a, b] = sal'eq [a, b] >>= \c -> sal'not [c]

sal'str :: SalFnI
sal'str = sal'string . concatMap show

-- Export

prelude :: SalEnv
prelude =
  Map.fromList
    [ ("if", SalMacro sal'if)
    , ("fn", SalMacro sal'fn)
    , ("def", SalMacro sal'def)
    , ("defn", SalMacro sal'defn)
    , ("println", SalFunction sal'println)
    , ("type", SalFunction sal'type)
    , ("nil?", SalFunction sal'nil)
    , ("+", SalFunction sal'sum)
    , ("-", SalFunction sal'sub)
    , ("*", SalFunction sal'mul)
    , ("/", SalFunction sal'div)
    , ("mod", SalFunction sal'mod)
    , ("abs", SalFunction sal'abs)
    , ("inc", SalFunction sal'inc)
    , ("dec", SalFunction sal'dec)
    , ("max", SalFunction sal'max)
    , ("min", SalFunction sal'min)
    , (">", SalFunction sal'gt)
    , (">=", SalFunction sal'gte)
    , ("<", SalFunction sal'lt)
    , ("<=", SalFunction sal'lte)
    , ("=", SalFunction sal'eq)
    , ("or", SalFunction sal'or)
    , ("and", SalFunction sal'and)
    , ("not", SalFunction sal'not)
    , ("not=", SalFunction sal'noteq)
    ]

--------------------------------------------------------------------------------
-- MAIN
--------------------------------------------------------------------------------

eval :: String -> IO [SalVal]
eval code = snd <$> eval' prelude code

eval' :: SalEnv -> String -> IO (SalEnv, [SalVal])
eval' env = run env . parse . tokenize

repl :: IO ()
repl = loop prelude 1
 where
  loop env line = do
    putStr $ "sal:" ++ show line ++ "> "
    (env', vals) <- getLine >>= eval' env
    mapM_ print vals
    loop env' $ succ line

main :: IO ()
main = do
  args <- getArgs
  case args of
    [file] -> do
      code <- readFile file
      void $ eval code
    [] -> do
      putStrLn "Sal's Another Lisp"
      repl
