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
  | SalKeyword String
  | SalFunction SalFnI
  | SalMacro SalMcI

instance Show SalVal where
  show :: SalVal -> String
  show SalNil = "nil"
  show (SalBool bool) = show bool
  show (SalNumber number) = show number
  show (SalString string) = string
  show (SalList list) = "[" ++ unwords (map show list) ++ "]"
  show (SalKeyword keyword) = ':' : keyword
  show (SalFunction _function) = "<function>"
  show (SalMacro _macro) = "<macro>"

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
  | SalExp (String, [SalAst])
  | SalRef String

type SalEnv = Map.Map String SalVal

type SalFnI = [SalVal] -> IO SalVal
type SalMcI = SalEnv -> [SalAst] -> IO (SalEnv, [SalAst])

--------------------------------------------------------------------------------
-- TOKENIZER
--------------------------------------------------------------------------------

tokenize :: String -> [String]
tokenize = tokenize' [] ""

tokenize' :: [String] -> String -> String -> [String]
tokenize' acc buf "" = reverse $ tokenize'flush acc buf
tokenize' acc buf (c : code)
  | c == '"' = let (str, code') = tokenize'string code in tokenize' ((c : str) : tokenize'flush acc buf) "" code'
  | Set.member c brackets = tokenize' ([c] : tokenize'flush acc buf) "" code
  | isSpace c = tokenize' (tokenize'flush acc buf) "" code
  | otherwise = tokenize' acc (c : buf) code
 where
  brackets = Set.fromList "()[]{}"

tokenize'flush :: [String] -> String -> [String]
tokenize'flush acc "" = acc
tokenize'flush acc buf = reverse buf : acc

tokenize'string :: String -> (String, String)
tokenize'string ('"' : code) = (['"'], code)
tokenize'string code = case findIndex quote $ unpack code of
  Just index -> splitAt (index + 2) code
  Nothing -> error "String not closed"
 where
  quote (a, b) = a /= '\\' && b == '"'
  unpack str = zip str $ drop 1 str

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
parse' acc stp ("(" : kw : tok) = parse' (SalExp (kw, ast) : acc) stp tok' where (ast, tok') = parse' [] ")" tok
parse' acc stp ("[" : tok) = parse' (SalLitList ast : acc) stp tok' where (ast, tok') = parse' [] "]" tok
parse' acc stp (t : tok)
  | t == stp = (reverse acc, tok)
  | isNumber t = parse' (SalLit (SalNumber (read t)) : acc) stp tok
  | isKeyword t = parse' (SalRef t : acc) stp tok
  | otherwise = error "Syntax error"
 where
  isNumber (h : t) = (isDigit h || h == '-') && all (\d -> isDigit d || '.' == d) t && (length . filter (== '.')) t <= 1
  isKeyword token@(h : _) = not (isDigit h) && all (\c -> isAlphaNum c || Set.member c keywordSymbols) token
  keywordSymbols = Set.fromList "_+-*/<>='"

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
sal'castNumber _ = error "Not a number"

sal'bool :: Bool -> IO SalVal
sal'bool = pure . SalBool

sal'number :: Double -> IO SalVal
sal'number = pure . SalNumber

-- Macros

sal'if :: SalMcI
sal'if env [cond, true] = sal'if env [cond, true, SalLit SalNil]
sal'if env [cond, true, false] = run env [cond] >>= \[val] -> pure (env, if sal'castBool val then [true] else [false])

sal'fn :: SalMcI
sal'fn env (SalLitList args : ast@(_ : _)) =
  pure (env, [SalLit (SalFunction function)])
 where
  function args' = last <$> run (env' args') ast
  env' args' = foldl map' env $ zip args args'
  map' e (SalRef k, v) = Map.insert k v e

sal'def :: SalMcI
sal'def env [SalRef kw, ast] = run env [ast] >>= \[val] -> pure (Map.insert kw val env, [SalLit (SalKeyword kw)])

sal'defn :: SalMcI
sal'defn env (ref : ast) = sal'fn env ast >>= \(env', ast') -> sal'def env' (ref : ast')

-- Functions

sal'println :: SalFnI
sal'println values = putStrLn (unwords $ map show values) >> return SalNil

sal'type :: SalFnI
sal'type [val] = pure . SalKeyword $ typeOf val
 where
  typeOf SalNil = "nil"
  typeOf (SalBool _) = "bool"
  typeOf (SalNumber _) = "number"
  typeOf (SalString _) = "string"
  typeOf (SalList _) = "list"
  typeOf (SalKeyword _) = "keyword"
  typeOf (SalFunction _) = "function"
  typeOf (SalMacro _) = "macro"

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

sal'eq :: SalFnI
sal'eq [a, b] = sal'bool $ a == b
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
    , (">", SalFunction sal'gt)
    , (">=", SalFunction sal'gte)
    , ("<", SalFunction sal'lt)
    , ("<=", SalFunction sal'lte)
    , ("=", SalFunction sal'eq)
    , ("or", SalFunction sal'or)
    , ("and", SalFunction sal'and)
    , ("not", SalFunction sal'not)
    , ("not=", SalFunction sal'noteq)
    , ("nil?", SalFunction sal'nil)
    ]

--------------------------------------------------------------------------------
-- RUNNER
--------------------------------------------------------------------------------

run :: SalEnv -> [SalAst] -> IO [SalVal]
run = run' []

run' :: [SalVal] -> SalEnv -> [SalAst] -> IO [SalVal]
run' acc env [] = pure $ reverse acc
run' acc env (SalLit val : ast) = run' (val : acc) env ast
run' acc env (SalLitList ast' : ast) = run env ast' >>= \list -> run' (SalList list : acc) env ast
run' acc env (SalExp (kw, ast') : ast) = run'exp env kw ast' >>= \(env', val') -> run' (val' ++ acc) env' ast
run' acc env (SalRef kw : ast) = run' (run'ref env kw : acc) env ast

run'ref :: SalEnv -> String -> SalVal
run'ref env kw = case Map.lookup kw env of
  Just val -> val
  Nothing -> error "Undefined variable"

run'exp :: SalEnv -> String -> [SalAst] -> IO (SalEnv, [SalVal])
run'exp env kw ast = case Map.lookup kw env of
  Just (SalFunction fn) -> run env ast >>= fn >>= \val -> pure (env, [val])
  Just (SalMacro mc) -> mc env ast >>= \(env', ast') -> run env' ast' >>= \vals -> pure (env', vals)
  _ -> error "Is not a function or macro"

--------------------------------------------------------------------------------
-- MAIN
--------------------------------------------------------------------------------

eval :: String -> IO [SalVal]
eval = run prelude . parse . tokenize

main :: IO ()
main = do
  args <- getArgs
  case args of
    [file] -> readFile file >>= void . eval
    [] -> putStrLn "REPL AQUI"
