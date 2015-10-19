module Main where

import Data.Char



-- A recursive datatype
{-
data Expr = Const Int
    | Add Expr Expr
    | Mul Expr Expr
-}

-- Same definition rewritten with Type Fixpoint 

newtype Fix f = Fx (f (Fix f ) )

data ExprF a = Const Int | Add a a | Mul a a 

type Expr = Fix ExprF

-- a test
testExpr = Fx $ (Fx $ (Fx $ Const 2 ) `Add` (Fx $ Const 3))
 `Mul` (Fx $ Const 4)

-- an algebra is built on top of a functor. 
-- ExprF is a functor:

instance Functor ExprF where
    fmap eval (Const i) = Const i
    fmap eval (Add x y) = Add (eval x) (eval y)
    fmap eval (Mul x y) = Mul (eval x) (eval y)

-- Having a functor we can try different 'algebras'
-- Note we are talking about ExprF now. 
-- We expect to be able to 'evaluate' children of Expr
alg':: ExprF Int -> Int
alg' (Const i) = i
alg' (Add x y) = x + y
alg' (Mul x y) = x * y


alg:: ExprF String -> String 
alg (Const i) = [ chr (ord 'a' + i)]
alg (Add x y) = x ++ y
alg (Mul x y) = concat [[a,b] | a <- x, b <- y] 

-- Algebra = (C, F, A, m)
-- + Category C = Hask, points are types of Haskell
-- + Endofunctor F (maps Hask points into other Hask points) 
-- + Point A of category C. It's called carrier.
-- + Function m:: (F A) -> A 
-- Hence our definition:

type Algebra f a = f a -> a

-- C is implied (Hask), F and A are type-level, the rest is m, the function
-- There are infinitely many algebras based on same functor
-- One is particular -- Initial algebra, 
-- Practice: does not 'forget' anything, preserves all information about input
-- Theory: there exists a homomorphism from initial algebra to any other algebra

type ExprInitAlgebra = Algebra ExprF (Fix ExprF)
ex_init_alg :: ExprF (Fix ExprF) -> Fix ExprF
ex_init_alg = Fx  

-- Now let's show we can build anything from it. Functor 'f' is fixed. 
-- Let 'a' be a carrier object for a new algebra.
--                   Carrier   Evaluator
-- Initial algebra:   Fix f        Fx
-- Constructed one:     a        `alg`
--
-- Fx :: f (Fix f) -> Fix f
-- alg:: f a -> a
--
-- we want to get:
-- g:: Fix f -> a
-- Thanks to the fact that f is a functor, fmap is at our disposal:
-- fmap g :: f (Fix f) ->  f a

{-  Before:
 
   f( Fix f ) ---- fmap g ---> f a
       |                        |
       |                        |
       Fx                      alg 
       |                        |
       |                        |
       V                        V
      Fix f  -------g-------->  a 
-}

-- VERY CRUCIAL:: Fx is lossess SO it can be inverted:
{-  Before:
 
   f( Fix f ) ---- fmap g ---> f a
       ^                        |
       |                        |
     Unfix                      alg 
       |                        |
       |                        |
       |                        V
      Fix f  -------g-------->  a 
-}

unFix:: Fix f -> f (Fix f)
unFix (Fx x) = x

-- Finally: let s build g:
g = alg. (fmap g) . unFix

--g alg = alg. (fmap (g alg)) . unFix

-- And even better:
cata :: Functor f => (f a -> a) -> (Fix f -> a)
cata alg = alg . fmap (cata alg) . unFix

-- *Main> :t cata alg
-- cata alg :: Fix ExprF -> String

-- Now lists

data ListF a b = Nil | Cons a b
type List a = Fix (ListF a)

instance Functor (ListF a)  where
    fmap f Nil = Nil
    fmap f (Cons e x) = Cons e (f x)

algSum :: ListF Int Int -> Int
algSum Nil = 0
algSum (Cons e acc) = e + acc

lst :: List Int
lst = Fx $ Cons 2 (Fx $ Cons 3 (Fx $ Cons 4 (Fx Nil)))


{- Fx and unFix together -}
{- Fx is In (into F), unfix is out (out of F) -}

newtype Mu f = In {out :: f (Mu f)} 
type CoAlgebra f a = a -> f a

catam :: Functor f => Algebra f a -> (Mu f -> a)
catam alg = alg . fmap (catam alg) . out

anam :: Functor f => CoAlgebra f a -> (a -> Mu f)
anam coalg = In. fmap (anam coalg) . coalg 


data ListF' a b = Nil' | Cons' a b deriving Show
type List' a = Mu (ListF' a)

instance Functor (ListF' a)  where
    fmap f Nil' = Nil'
    fmap f (Cons' e x) = Cons' e (f x)

coalg :: CoAlgebra (ListF' Int) Int --   Int --Int -> List' Int 
coalg 0 = Nil'
coalg x = Cons' x (x-1)

showF :: (Show a) => List' a -> String
showF (In Nil') = "NIL"
showF (In (Cons' x xs)) = (show x) ++ ";" ++ (showF xs)

main = do
    print $ (cata algSum) lst
    print $ foldr (\e acc -> e + acc) 0 [2, 3, 4]
    print $ showF $ anam coalg 10
--
-- Actually, even in Haskell recursion is not completely first class because the compiler does a terrible job of optimizing recursive code. This is why F-algebras and F-coalgebras are pervasive in high-performance Haskell libraries like vector, because they transform recursive code to non-recursive code, and the compiler does an amazing job of optimizing non-recursive code.
