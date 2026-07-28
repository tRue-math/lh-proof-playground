{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module ListProofs (app, assoc) where

import ProofCombinators

{-@ reflect app @-}
app :: [a] -> [a] -> [a]
app []     ys = ys
app (x:xs) ys = x : app xs ys

{-@ assoc :: xs:[a] -> ys:[a] -> zs:[a] -> { app (app xs ys) zs == app xs (app ys zs) } @-}
assoc :: [a] -> [a] -> [a] -> Proof
assoc [] ys zs =
      app (app [] ys) zs
  ==. app ys zs
  ==. app [] (app ys zs)
  *** qed

-- assoc (_:xs) ys zs = assoc xs ys zs
assoc (x:xs) ys zs =
      app (app (x:xs) ys) zs
  ==. app (x : app xs ys) zs
  ==. x : app (app xs ys) zs ? assoc xs ys zs
  ==. x : app xs (app ys zs)
  ==. app (x:xs) (app ys zs)
  *** qed