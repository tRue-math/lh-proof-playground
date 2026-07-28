{-@ LIQUID "--reflection" @-}

module ProofCombinators 
  ( Proof
  , (==.)
  , (***)
  , (?)
  , qed
  ) where

type Proof = ()

infixl 3 ==.
{-@ (==.) :: x:a -> y:{a | x == y} -> {v:a | v == x} @-}
(==.) :: a -> a -> a
x ==. _ = x

infixl 3 ?
{-@ (?) :: x:a -> y:b -> {v:a | v == x} @-}
(?) :: a -> b -> a
x ? _ = x

infixr 2 ***
{-@ (***) :: a -> b -> b @-}
(***) :: a -> b -> b
_ *** y = y

qed :: Proof
qed = ()