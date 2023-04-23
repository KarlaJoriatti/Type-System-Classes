{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Move brackets to avoid $" #-}
{-# HLINT ignore "Use concatMap" #-}
{-# HLINT ignore "Redundant bracket" #-}
{-# HLINT ignore "Use <$>" #-}
{-# HLINT ignore "Redundant $" #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
import Text.Parsec
import Typee
import Distribution.PackageDescription (TestSuite(TestSuite))

data Literal = LitInt   Integer
             | LitChar  Char
             | LitStr   String
             | LitFloat Double
             | LitBool  Bool
             deriving (Eq, Show)

data Pat = PVar Id
         | PLit Literal
         | PCon String [Pat]
         deriving (Eq, Show)

data Expr =   Var Id
            | App Expr Expr
            | Lam Id Expr
            | Let Id Expr Expr
            | Lit Literal
            | Constr String
            | If Expr Expr Expr
            | Case Expr [(Pat, Expr)]
            deriving (Eq, Show)

tiContext :: [Assump] -> Id -> TI SimpleType
tiContext g i = if l /= [] then unquantify t else error ("Undefined: " ++ i ++ "\n")
   where
      l = dropWhile (\(i' :>: _) -> i /= i' ) g
      (_ :>: t) = head l
      unqt = unquantify t       

setArr [x] = x   
setArr (x:xs) = TArr (x) (setArr xs)

unifyEP g t [] = return (t, g, [])
unifyEP g t (x:xs) = do 
                       (t', g', s1) <- tiExpr' g x
                       (t'', g'', s2) <- unifyEP g' t xs 
                       let s = unify t t'
                       return (t, g'', s1 @@ s2)

patterns :: [Assump] -> [Pat] -> TI[(SimpleType, [Assump], [(Id, SimpleType)])]
patterns g [] = return []
patterns g (x:xs) = do
                      t <- tiExpr' g x
                      let t' = fst' t
                      ts <- fmap (t:) (patterns g xs)
                      return (ts)

fechamento :: [Assump] -> SimpleType -> SimpleType
fechamento g t = apply s t
   where g' = [gs | gs <- tv t, gs `notElem` (concat $ map tv g)]
         s  = zip g' (map TGen [0..])
         
takeLit (LitInt   a) = TCon "Int"
takeLit (LitChar  a) = TCon "Char"
takeLit (LitStr   a) = TCon "String"
takeLit (LitFloat a) = TCon "Double"
takeLit (LitBool  a) = TCon "Bool"

tiExpr' :: [Assump] -> Pat -> TI (SimpleType, [Assump], [(Id, SimpleType)])
tiExpr' g (PVar i) = do 
                       b <- freshVar
                       return (b, g/+/[i:>:b], [])
tiExpr' g (PLit i) = return (takeLit i, g, [])
tiExpr' g (PCon i p) = do
                         t  <- tiContext g i
                         t' <- unquantify t
                         ts <- patterns g p 
                         let ts'  = map fst' ts
                             ts'' = setArr ts'
                             g'   = concat (map snd' ts)
                             s    = unify t' ts''
                         return (apply s t', g', s)
                         
assumps [] [] s = []
assumps (y:ys) (x:xs) s = (y:>:apply s x) : (assumps ys xs s)

tiExpr g (Lit i) = return (takeLit i, [])
tiExpr g (Var i) = do
                     t <- tiContext g i
                     return (t, [])
tiExpr g (Constr i) = do
                        t <- tiContext g i
                        return (t, [])
tiExpr g (App e e') = do (t, s1) <- tiExpr g e
                         (t', s2) <- tiExpr (apply s1 g) e'
                         b <- freshVar
                         let s3 = unify (apply s2 t) (t' --> b)
                         return (apply s3 b, s3 @@ s2 @@ s1)
tiExpr g (Lam i e) = do b <- freshVar
                        (t, s)  <- tiExpr (g/+/[i:>:b]) e
                        return (apply s (b --> t), s)
tiExpr g (Let i e e') = do (t, s1) <- tiExpr g e
                           (t', s2) <- tiExpr (apply s1 (g/+/[i:>:fechamento (apply s1 g) t])) e'
                           return (t', s1 @@ s2)
tiExpr g (If c e e')  = do (t1, s1) <- tiExpr g c
                           (t2, s2) <- tiExpr (apply s1 g) e
                           (t3, s3) <- tiExpr (apply (s1 @@ s2) g) e'
                           let s4 = unify t1 (TCon "Bool")
                               s5 = unify t2 t3
                           return (apply s5 t3, s1 @@ s2 @@ s3 @@ s4 @@ s5)
tiExpr g (Case e ps) = do
                                   (t, s) <- tiExpr g e
                                   (t', g', s') <- unifyEP g t (map fst ps)
                                   return (t, s @@ s')


--- Exemplos ---
ex1 = Lam "f" (Lam "x" (App (Var "f") (Var "x")))
ex2 = Lam "x" (App (Var "x") (Var "x"))
ex3 = Lam "g" (Lam "f" (Lam "x" (App (Var "g") (App (Var "f") (Var "x")))))
ex4 = Lam "x" (Lam "x" (Var "x"))
ex5 = Lam "w" (Lam "y" (Lam "x" (App (Var "y") (App (App (Var "w") (Var "y")) (Var "x")))))
ex6 = Lam "x" (Lam "y" (Lam "w" (Lam "u" (App (App (Var "x") (Var "w")) (App (App (Var "y") (Var "w")) (Var "u"))))))
-- Let --
ex7 = Lam "y" (Let "x" (Var "y") (Var "x"))
ex8 = Lam "y" (Lam "x" (Let "a" (App (Var "x") (Var "y")) (Var "a")))
ex9 = Lam "w" (Lam "y" (Lam "x" (Let "b" (App (App (Var "w") (Var "x")) (Var "y")) (Var "b"))))
ex10 = Lam "f" (Let "x" (Lam "y" (Var "y")) (App (Var "x") (App (Var "x") (Var "f"))))
ex11 = Lam "f" (Lam "w" (Let "x" (Lam "y" (Var "y")) (App (App (Var "x") (Var "w")) (App (Var "x") (Var "f")))))
-- Tipos Literais -- 
ex12 = Lam "x" (App (App (Var "sum") (Var "x")) (Lit (LitInt 1)))
ex13 = Lam "x" (Let "y" (App (Var "concat") (Lit (LitStr "amor"))) (App (Var "y") (Var "x")))
ex14 = Let "y" (Var "div") (Var "y")
-- Construtores de Lista e Dupla --
ex15 = Lam "x" (Let "y" (App (App (Constr "Cons") (Lit (LitInt 1))) (Constr "Nil")) (App (App (Constr "Pair") (Var "x")) (Var "y")))
ex16 = Lam "x" (Let "y" (Constr "Cons") (App (App (Constr "Pair") (App (App (Var "y") (Lit (LitInt 1)) ) (Constr "Nil"))) ((App (App (Var "y") (Var "x") ) (Constr "Nil")))))
ex17 = Let "a" (Constr "Pair") (Var "a")
ex18 = Let "b" (Constr "Cons") (Var "b")
-- error unify --
ex19 = Let "x" (Var "div") (App (Var "x") (Lit (LitInt 2)))
-- If --
ex20 = If (Lit (LitBool True)) (Let "a" (Constr "Pair") (Var "a")) (Let "b" (Constr "Pair") (Var "b"))
ex21 = If (Let "a" (Lit (LitBool False)) (Var "a")) (Let "y" (Var "div") (Var "y")) (Let "y" (Var "div") (Var "y"))
ex22 = Lam "x" (If (Var "x") (Lit (LitChar 'a')) (Lit (LitChar 'h')))
ex23 = Lam "z" (Lam "y" (Lam "x" (If (Var "x") (Var "z") (Var "y"))))
-- erro if --
ex24 = If (Lit (LitInt 2)) (Let "a" (Constr "Pair") (Var "a")) (Let "b" (Constr "Pair") (Var "b"))
ex25 = If (Lit (LitBool True)) (Let "a" (Constr "Cons") (Var "a")) (Let "b" (Constr "Pair") (Var "b"))
-- case --
ex26 = Let "x" (Lit (LitInt 3)) (Case (Var "x") [(PLit (LitInt 2), Var "False"), (PLit (LitInt 3), Var "True")])
-- erro case --
ex27 = Let "x" (Lit (LitInt 3)) (Case (Var "x") [(PLit (LitChar 'c'), Var "False"), (PLit (LitInt 3), Var "True")])
ex28 = Case (Var "x") [(PLit (LitInt 2), Var "False")]



infer e = runTI (tiExpr g e)

-------- Parser ---------------
parseExpr = runParser expr [] "lambda-calculus"

expr :: Parsec String u Expr
expr = chainl1 (between spaces spaces parseNonApp) $ return $ App

var = do {i <- varId; return (Var i)}

lamAbs term = do char '\\'
                 i <- varId
                 char '.'
                 e <- term
                 return (Lam i e)

parseNonApp =  do {char '('; e <- expr; char ')'; return e} -- (E)
              <|> lamAbs expr                               -- \x.E
              <|> var                                       -- x

varId = many1 letter 

----------------------------------------
parseLambda s = case parseExpr s of
                     Left er -> print er
                     Right e -> (print e >> print (infer e))

main = do putStr "Lambda:"
          e <- getLine
          parseLambda e
