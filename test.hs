
data Test a = Test (TestS -> (a,TestS))

instance Monad Test where
    return a      = Test (\s -> (a,s))
    Test f >>= gm = Test (\s0 -> let (x,s1) = f s0
                                     (Test g) = gm x
                                   in g s1)

insertList l = Test (\s0 -> ((),l))
getElement n = Test (\(l) -> (l!!n,l))

runTest :: TestS -> Test a -> a
runTest s0 (Test c) = fst $ c s0

testcode = do h <- getElement 5
              p <- getElement 4
              t <- getElement 2
              return p

test = runTest [0..] testcode

{- guards

g x y = case 0 of
        _ | x == 1 && y>2     -> 1
          | x > 2             -> 3
          | otherwise         -> 2

Given a function with guards with otherwise
f <patterns> | p1        = e1
             | p2        = e2
             | ...      ...
             | pn        = en
             | otherwise = eo

can be converted like this
f <patterns> = if p1 then e1
                     else if p2 then e2
                                else eo

in case there is no otherwise i'll generate a pattern matching error
at the end with a function that always fails and returns the same type
f <patterns> = if p1 then e1
                     else if p2 then e2
                                else ((\a -> case a of 0 -> ex) 1)
ex is an expression choosen from {e1,..,en}
-}

