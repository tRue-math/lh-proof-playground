{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module FibProofs (fibTwo, fibTen, fibIncrease, fibIncreaseShort) where

import ProofCombinators

{-@ fib :: Nat -> Nat @-}
{-@ reflect fib @-}
fib :: Int -> Int
fib 0 = 0
fib 1 = 1
fib n = fib (n - 1) + fib (n - 2)

-- we cannot use the following type because lh does not support type synonyms with parameters yet
-- {-@ type Up f = n:Nat -> { f n <= f (n + 1) } @-}
-- {-@ type FibUp = Up fib @-}
{-@ type FibUp = n:Nat -> { fib n <= fib (n + 1) } @-}
{-@ type FibIncrease = n:Nat -> m:{Nat | n <= m} -> { fib n <= fib m } @-}

{-@ fibUp :: FibUp @-}
fibUp :: Int -> Proof
fibUp 0 = ()
fibUp 1 = ()
fibUp n =
        fib n
    <=. fib (n - 1) + fib n
    <=. fib (n + 1)
    *** qed

{-@ fibIncrease :: FibIncrease / [m] @-}
fibIncrease :: Int -> Int -> Proof
fibIncrease n m
  | n == m = ()
  | n < m  = fibIncrease n (m - 1) ? fibUp (m - 1) *** qed
  | otherwise = error "unreachable: n <= m is guaranteed by LH"

{-@ fibIncreaseShort :: FibIncrease / [m] @-}
fibIncreaseShort :: Int -> Int -> Proof
fibIncreaseShort n m
    | n == m = ()
    | n < m  =
        {-@ fibUpShort :: FibUp @-}
        let fibUpShort :: Int -> Proof
            fibUpShort 0 = ()
            fibUpShort 1 = ()
            fibUpShort n' = 0 <= fib (n' - 1) *** qed
        in
        [fibIncreaseShort n (m - 1), fibUpShort (m - 1)] *** qed
    | otherwise = error "unreachable: n <= m is guaranteed by LH"


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

-- it does not terminate in a reasonable time, so we comment it out for now
-- {-@ fibHundred :: { fib 100 == 354224848179261915075 } @-}
-- fibHundred :: Proof
-- fibHundred = ()