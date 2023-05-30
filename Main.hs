{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}

import Lambdaa
import Text.Parsec
import Text.Parsec.Expr
import Text.Parsec.Language
import qualified Text.Parsec.Token as T


lingDef = emptyDef
          {
            T.identStart = letter
            , T.identLetter = alphaNum
            , T.reservedNames = ["let", "case", "in", "of", "if", "then", "else", "True", "False"]
            , T.reservedOpNames = ["=", "->", "\\", ".", "(", ")"]
          }

lexico      = T.makeTokenParser lingDef

reserved    = T.reserved lexico
reservedOp  = T.reservedOp lexico
identifier  = T.identifier lexico
float       = T.float lexico 
natural     = T.natural lexico
charLiteral = T.charLiteral lexico
stringLiteral = T.stringLiteral lexico

partida = do {e <- parseNonApp; eof; return e}

parseExpr = runParser partida [] "lambda-calculus"

boolParser = do {reserved "True"; return (Lit (LitBool True))}
             <|> do {reserved "False"; return (Lit (LitBool False))}

boolParserPattern = do {reserved "True"; return (PLit (LitBool True))}
                    <|> do {reserved "False"; return (PLit (LitBool False))}

var = do {i <- identifier; return (Var i)}

pvar = do {i <- identifier; return (PVar i)}

pcon = do {i <- identifier; e <- parsePatterns; return (PCon i e)}

litExpr = try (do {boolParser})
          <|> do {n <- float; return (Lit (LitFloat n))}
          <|> do {n <- natural; return (Lit (LitInt n))}
          <|> do {n <- charLiteral; return (Lit (LitChar n))}
          <|> do {n <- stringLiteral; return (Lit (LitStr n))}

litPattern = try (do {boolParserPattern})
                 <|> do {n <- float; return (PLit (LitFloat n))}
                 <|> do {n <- natural; return (PLit (LitInt n))}
                 <|> do {n <- charLiteral; return (PLit (LitChar n))}
                 <|> do {n <- stringLiteral; return (PLit (LitStr n))}

lamAbs term = do reservedOp "\\"
                 i <- identifier
                 reservedOp "."
                 e <- term
                 return (Lam i e)

letExpr = do reserved "let"
             i <- identifier
             reservedOp "="
             e <- parseNonApp
             reserved "in"
             e' <- parseNonApp
             return (Let i e e')

ifExpr = do reserved "if"
            c <- parseNonApp
            reserved "then"
            e <- parseNonApp
            reserved "else"
            e' <- parseNonApp
            return(If c e e')

parsePatterns = try ( do {pat <- parsePattern; pats <- parsePatterns; return (pat : pats)})
                <|> do {return []}

parsePattern = do {reservedOp "("; e <- parsePattern; reservedOp ")"; return e} -- (E)
              <|> pcon                                      -- constructor
              <|> litPattern                                -- literal
              <|> pvar                                      -- var

patCases = try ( do {pat <- patCase; pats <- patCases; return (pat : pats)})
                <|> do {return []}

patCase = do pat <- parsePattern
             reservedOp "->"
             e <- parseNonApp
             char '\n'
             return (pat, e)

caseExpr = do reserved "case"
              e <- parseNonApp
              reserved "of"
              ps <- patCases
              return (Case e ps)

expr :: Parsec String u Expr
expr = chainl1 (between spaces spaces parseNonApp) $ return $ App

parseNonApp =  do {reservedOp "("; e <- expr; reservedOp ")"; return e} -- (E)
              <|> lamAbs expr                                                      -- \x.E
              <|> ifExpr                                                       -- if (C) then (E) else (E')
              <|> letExpr                                                      -- Let x = (E) in E'
              <|> caseExpr                                                     -- Case E of Pat -> E'
              <|> litExpr                                                      -- literal
              <|> var                                                          -- x

-------- Main -----------

parseLambda s = case parseExpr s of
                     Left er -> print er
                     Right e -> (print e >> print (infer e))

main = do putStr "Arquivo: "
          e <- getLine
          file' <- readFile e
          parseLambda file' 