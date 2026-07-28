{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module ListProofs (app, assoc, len, lenPlus, rev, revRev) where

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

{-@ len :: xs:[a] -> Nat @-}
{-@ reflect len @-}
len :: [a] -> Int
len []     = 0
len (_:xs) = 1 + len xs

{-@ lenPlus :: xs:[a] -> ys:[a] -> { len (app xs ys) == len xs + len ys } @-}
lenPlus :: [a] -> [a] -> Proof
lenPlus [] _ = ()
lenPlus (_:xs) ys = lenPlus xs ys

{-@ rev :: xs:[a] -> [a] @-}
{-@ reflect rev @-}
rev :: [a] -> [a]
rev []     = []
rev (x:xs) = app (rev xs) [x]

{-@ appNil :: xs:[a] -> { app xs [] == xs } @-}
appNil :: [a] -> Proof
appNil []     = ()
appNil (_:xs) = appNil xs

{-@ revApp :: xs:[a] -> ys:[a] -> { rev (app xs ys) == app (rev ys) (rev xs) } @-}
revApp :: [a] -> [a] -> Proof
-- revApp [] ys = appNil (rev ys)
revApp [] ys = 
      rev (app [] ys)
  ==. rev ys            ? appNil (rev ys)
  ==. app (rev ys) []
  ==. app (rev ys) (rev [])
  *** qed
-- revApp (x:xs) ys = [revApp xs ys, assoc (rev ys) (rev xs) (rev [x])] *** qed
revApp (x:xs) ys =
      rev (app (x:xs) ys)
  ==. rev (x : app xs ys)
  ==. app (rev (app xs ys)) [x] ? revApp xs ys
  ==. app (app (rev ys) (rev xs)) [x]
  ==. app (app (rev ys) (rev xs)) (rev [x]) ? assoc (rev ys) (rev xs) (rev [x])
  ==. app (rev ys) (app (rev xs) (rev [x]))
  *** qed

{-@ revRev :: xs:[a] -> { rev (rev xs) == xs } @-}
revRev :: [a] -> Proof
revRev []     = ()
-- revRev (x:xs) = [revRev xs, revApp (rev xs) [x]] *** qed
revRev (x:xs) = 
        rev (rev (x:xs))
    ==. rev (app (rev xs) [x]) ? revApp (rev xs) [x]
    ==. app (rev [x]) (rev (rev xs)) ? revRev xs
    ==. app [x] xs
    ==. x : xs
    *** qed