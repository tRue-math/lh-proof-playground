{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module FibProofs (fibTwo, fibTen) where

import ProofCombinators

{-@ fib :: Nat -> Nat @-}
{-@ reflect fib @-}
fib :: Int -> Int
fib 0 = 0
fib 1 = 1
fib n = fib (n - 1) + fib (n - 2)

{-@ fibTwo :: { fib 2 == 1 } @-}
fibTwo :: Proof
fibTwo = fib 2
    ==. fib (1 + 1)
    ==. fib 1 + fib 0
    ==. 1 + 0
    ==. 1
    *** qed

{-@ fibTen :: { fib 10 == 55 } @-}
fibTen :: Proof
fibTen = ()