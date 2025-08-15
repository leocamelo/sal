import Data.Char (isAlphaNum, isDigit, isSpace)
import Data.Fixed (mod')
import Data.List (findIndex)

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
  | SalNumber Double
  | SalString String
  | SalList [SalVal]
  | SalKeyword SalKwI
  | SalMacro SalMcI
  | SalFunction SalFnI

instance Show SalVal where
  show :: SalVal -> String
  show SalNil = "nil"
  show (SalBool bool) = show bool
  show (SalNumber number) = show number
  show (SalString string) = string
  show (SalList list) = "[" ++ unwords (map show list) ++ "]"
  show (SalKeyword keyword) = ':' : keyword
  show (SalMacro _macro) = "<macro>"
  show (SalFunction _function) = "<function>"

instance Eq SalVal where
  (==) :: SalVal -> SalVal -> Bool
  SalNil == SalNil = True
  SalBool a == SalBool b = a == b
  SalNumber a == SalNumber b = a == b
  SalString a == SalString b = a == b
  SalList a == SalList b = a == b
  SalKeyword a == SalKeyword b = a == b
  _ == _ = False

data SalAst
  = SalLit SalVal
  | SalLitList [SalAst]
  | SalExp (SalKwI, [SalAst])
  | SalRef SalKwI

type SalKwI = String
type SalFnI = [SalVal] -> IO SalVal
type SalMcI = SalEnv -> [SalAst] -> IO (SalEnv, [SalAst])

type SalEnv = Map.Map SalKwI SalVal

--------------------------------------------------------------------------------
-- TOKENIZER
--------------------------------------------------------------------------------

tokenize :: String -> [String]
tokenize = tokenize' [] ""

tokenize' :: [String] -> String -> String -> [String]
tokenize' acc buf "" = reverse $ tokenize'flush acc buf
tokenize' acc buf (c : code)
  | c == '"' = let (str, code') = tokenize'string code in tokenize' ((c : str) : tokenize'flush acc buf) "" code'
  | Set.member c tokenize'brackets = tokenize' ([c] : tokenize'flush acc buf) "" code
  | isSpace c = tokenize' (tokenize'flush acc buf) "" code
  | otherwise = tokenize' acc (c : buf) code

tokenize'flush :: [String] -> String -> [String]
tokenize'flush acc "" = acc
tokenize'flush acc buf = reverse buf : acc

tokenize'string :: String -> (String, String)
tokenize'string ('"' : code) = (['"'], code)
tokenize'string code = case findIndex quote $ unpack code of
  Just index -> splitAt (index + 2) code
  Nothing -> error "ParseError: String not closed"
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
parse' acc stp ("nil" : tok) = parse' (SalLit SalNil : acc) stp tok
parse' acc stp ("true" : tok) = parse' (SalLit (SalBool True) : acc) stp tok
parse' acc stp ("false" : tok) = parse' (SalLit (SalBool False) : acc) stp tok
parse' acc stp (('"' : str) : tok) = parse' (SalLit (SalString (init str)) : acc) stp tok
parse' acc stp ("(" : kw : tok) = let (ast, tok') = parse' [] ")" tok in parse' (SalExp (kw, ast) : acc) stp tok'
parse' acc stp ("[" : tok) = let (ast, tok') = parse' [] "]" tok in parse' (SalLitList ast : acc) stp tok'
parse' acc stp (t : tok)
  | t == stp = (reverse acc, tok)
  | parse'isNumber t = parse' (SalLit (SalNumber (read t)) : acc) stp tok
  | parse'isKeyword t = parse' (SalRef t : acc) stp tok
  | otherwise = error "ParseError: Syntax error"

parse'isNumber :: String -> Bool
parse'isNumber (h : t) = isDigitNeg h && all isDigitDot t && dotCount t <= 1
 where
  isDigitNeg n = isDigit n || n == '-'
  isDigitDot n = isDigit n || n == '.'
  dotCount = length . filter (== '.')

parse'isKeyword :: String -> Bool
parse'isKeyword token@(h : _) = not (isDigit h) && all isAlphaNumSym token
 where
  isAlphaNumSym n = isAlphaNum n || Set.member n keywordSymbols
  keywordSymbols = Set.fromList "_+-*/<>='"

--------------------------------------------------------------------------------
-- RUNNER
--------------------------------------------------------------------------------

run :: SalEnv -> [SalAst] -> IO (SalEnv, [SalVal])
run = run' []

run' :: [SalVal] -> SalEnv -> [SalAst] -> IO (SalEnv, [SalVal])
run' acc env [] = pure (env, reverse acc)
run' acc env (SalLit val : ast) = run' (val : acc) env ast
run' acc env (SalLitList ast' : ast) = run env ast' >>= \(env', list) -> run' (SalList list : acc) env' ast
run' acc env (SalExp (kw, ast') : ast) = run'exp env kw ast' >>= \(env', val') -> run' (val' ++ acc) env' ast
run' acc env (SalRef kw : ast) = run' (run'ref env kw : acc) env ast

run'exp :: SalEnv -> SalKwI -> [SalAst] -> IO (SalEnv, [SalVal])
run'exp env kw ast = case Map.lookup kw env of
  Just (SalMacro mc) -> mc env ast >>= uncurry run
  Just (SalFunction fn) -> run env ast >>= fn . snd >>= \val -> pure (env, [val])
  _ -> error "RuntimeError: Is not a function or macro"

run'ref :: SalEnv -> SalKwI -> SalVal
run'ref env kw = case Map.lookup kw env of
  Just val -> val
  Nothing -> error "RuntimeError: Undefined variable"

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
sal'castNumber _ = error "RuntimeError: Not a number"

sal'bool :: Bool -> IO SalVal
sal'bool = pure . SalBool

sal'number :: Double -> IO SalVal
sal'number = pure . SalNumber

sal'keyword :: SalKwI -> IO SalVal
sal'keyword = pure . SalKeyword

-- Macros

sal'if :: SalMcI
sal'if env [cond, true] = sal'if env [cond, true, SalLit SalNil]
sal'if env [cond, true, false] = run env [cond] >>= \(_, [val]) -> pure (env, if sal'castBool val then [true] else [false])

sal'fn :: SalMcI
sal'fn env ast@(SalLitList _ : (_ : _)) = sal'fn env (SalRef "" : ast)
sal'fn env (SalRef kw : SalLitList args'keys : ast@(_ : _)) = pure (env, [SalLit fn])
 where
  fn = SalFunction fn'
  fn' args'values = last . snd <$> run (fn'env args'values) ast
  fn'env args'values = foldl env'ref env' $ zip args'keys args'values
  env' = Map.insert "recur" fn $ if kw == "" then env else Map.insert kw fn env
  env'ref e (SalRef k, v) = Map.insert k v e

sal'def :: SalMcI
sal'def env [SalRef kw, ast] = run env [ast] >>= \(_, [val]) -> pure (Map.insert kw val env, [SalLit (SalKeyword kw)])

sal'defn :: SalMcI
sal'defn env ast@(ref@(SalRef _) : (args@(SalLitList _) : (_ : _))) = sal'fn env ast >>= \(env', ast') -> sal'def env' (ref : ast')

-- Functions

sal'println :: SalFnI
sal'println values = putStrLn (unwords $ map show values) >> pure SalNil

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

sal'inc :: SalFnI
sal'inc [SalNumber a] = sal'number $ succ a
sal'dec :: SalFnI
sal'dec [SalNumber a] = sal'number $ pred a

sal'max :: SalFnI
sal'max = sal'number . maximum . map sal'castNumber
sal'min :: SalFnI
sal'min = sal'number . minimum . map sal'castNumber

sal'eq :: SalFnI
sal'eq [a, b] = sal'bool $ a == b

sal'gt :: SalFnI
sal'gt [SalNumber a, SalNumber b] = sal'bool $ a > b
sal'gte :: SalFnI
sal'gte [SalNumber a, SalNumber b] = sal'bool $ a >= b

sal'lt :: SalFnI
sal'lt [SalNumber a, SalNumber b] = sal'bool $ a < b
sal'lte :: SalFnI
sal'lte [SalNumber a, SalNumber b] = sal'bool $ a <= b

sal'or :: SalFnI
sal'or = sal'bool . any sal'castBool
sal'and :: SalFnI
sal'and = sal'bool . all sal'castBool

sal'not :: SalFnI
sal'not [value] = sal'bool . not $ sal'castBool value
sal'noteq :: SalFnI
sal'noteq [a, b] = sal'eq [a, b] >>= \c -> sal'not [c]

sal'nil :: SalFnI
sal'nil [val] = sal'bool $ val == SalNil

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
    , ("+", SalFunction sal'sum)
    , ("-", SalFunction sal'sub)
    , ("*", SalFunction sal'mul)
    , ("/", SalFunction sal'div)
    , ("mod", SalFunction sal'mod)
    , ("inc", SalFunction sal'inc)
    , ("dec", SalFunction sal'dec)
    , ("max", SalFunction sal'max)
    , ("min", SalFunction sal'min)
    , ("=", SalFunction sal'eq)
    , (">", SalFunction sal'gt)
    , (">=", SalFunction sal'gte)
    , ("<", SalFunction sal'lt)
    , ("<=", SalFunction sal'lte)
    , ("or", SalFunction sal'or)
    , ("and", SalFunction sal'and)
    , ("not", SalFunction sal'not)
    , ("not=", SalFunction sal'noteq)
    , ("nil?", SalFunction sal'nil)
    ]

--------------------------------------------------------------------------------
-- MAIN
--------------------------------------------------------------------------------

eval :: String -> IO [SalVal]
eval code = snd <$> eval' prelude code

eval' :: SalEnv -> String -> IO (SalEnv, [SalVal])
eval' env = run env . parse . tokenize

main :: IO ()
main = do
  args <- getArgs
  case args of
    [file] -> readFile file >>= void . eval
    [] -> putStrLn "REPL AQUI"
