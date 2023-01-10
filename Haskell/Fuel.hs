
import Test.QuickCheck
import Test.QuickCheck.Poly

-- original Banker's queue from Okasaki

data Q a = Q Int [a] Int [a]
 deriving ( Eq, Ord, Show )

empty :: Q a
empty = Q 0 [] 0 []

enq :: Q a -> a -> Q a
enq (Q n xs m ys) y = mkQ n xs (m+1) (y:ys)

first :: Q a -> Maybe a
first (Q _ (x:_) _ _) = Just x
first _               = Nothing

deq :: Q a -> Q a
deq (Q n (_:xs) m ys) = mkQ (n-1) xs m ys
deq q                 = q

mkQ :: Int -> [a] -> Int -> [a] -> Q a
mkQ n xs m ys
  | m <= n    = Q n xs m ys
  | otherwise = Q (n+m) (xs ++ reverse ys) 0 []

-- modelling laziness using a "tree of fuel" that decides what to compute

type Lazy a = Fuel -> a

data Fuel = F [Fuel]
 deriving ( Eq, Ord, Show )

fuel1 :: Int -> Fuel
fuel1 0 = F []
fuel1 k = F [fuel1 (k-1)]

cost :: Fuel -> Int
cost (F rs) = 1 + sum (map cost rs)

-- transforming functions to be explicitly lazy like this
-- the fuel tree is distributed over all applications on the RHS

enqL :: Q a -> a -> Lazy (Q a)
enqL (Q n xs m ys) y r = mkQL n xs (m+1) (y:ys) r

deqL :: Q a -> Lazy (Q a)
deqL (Q n (_:xs) m ys) r = mkQL (n-1) xs m ys r
deqL q                 _ = q

mkQL :: Int -> [a] -> Int -> [a] -> Lazy (Q a)
mkQL n xs m ys (F _)       | m <= n = Q n xs m ys
mkQL n xs m ys (F (p:q:_))          = Q (n+m) (appL xs (revL ys [] q) p) 0 []

appL :: [a] -> [a] -> Lazy [a]
appL []     ys (F _)     = ys
appL (x:xs) ys (F (r:_)) = x : appL xs ys r

revL :: [a] -> [a] -> Lazy [a]
revL []     ys (F _)     = ys
revL (x:xs) ys (F (r:_)) = revL xs (x:ys) r

-- to model presistent usage of a datastructure, just following the API

data Usage a
  = First
  | Enq a [Usage a]
  | Deq [Usage a]
 deriving ( Eq, Ord, Show )

run :: Usage a -> Q a -> Lazy ()
run First      q (F _)      = first q `seq` ()
run (Enq x us) q (F (r:rs)) = let q' = enqL q x r in runAll us q' rs
run (Deq us)   q (F (r:rs)) = let q' = deqL q   r in runAll us q' rs

runAll :: [Usage a] -> Q a -> [Fuel] -> ()
runAll []     _ []     = ()
runAll (u:us) q (r:rs) = run u q r `seq` runAll us q rs

--

fuel :: Usage a -> Q a -> Fuel
fuel First      q = F []
fuel (Enq x us) q = F (enqFuel q (need us) : [ fuel u (enq q x) | u <- us ])
fuel (Deq   us) q = F (deqFuel q (need us) : [ fuel u (deq q) | u <- us ])

need :: [Usage a] -> Int
need []              = 0
need (First    : us) = 1             `max` need us
need (Enq _ vs : us) = need vs       `max` need us
need (Deq vs   : us) = (need vs + 1) `max` need us

enqFuel :: Q a -> Int -> Fuel
enqFuel (Q a _ b _) n = mkQFuel a (b+1) n

deqFuel :: Q a -> Int -> Fuel
deqFuel (Q a _ b _) n = mkQFuel (a-1) b n

mkQFuel :: Int -> Int -> Int -> Fuel
mkQFuel a b n
  | a < 0     = F [] -- when the queue was empty and we deq-ed anyway
  | b <= a    = F []
  | otherwise = F [fuel1 n, fuel1 n] -- over-approximation!
  -- | otherwise = F [fuel1 ap, fuel1 rv] -- more precise; both work
 where
  ap = (a `min` n)
  rv = if n > a then b else 0

-- QuickChecking

instance Arbitrary a => Arbitrary (Usage a) where
  arbitrary = sized (arb 0)
   where
    -- this generator avoids generating deq's on empty queues
    arb s n = frequency $
              [ (if s > 0 then 1 else 0,
                  do return First) ] ++
              [ (n `max` if s <= 0 then 1 else 0,
                  do x <- arbitrary
                     us <- arbs (s+1) (n-1)
                     return (Enq x us)) ] ++
              [ (if s <= 0 then 0 else 0 `max` n,
                  do us <- arbs (s-1) (n-1)
                     return (Deq us)) ]

    arbs s n =
      do k <- choose (0,5 `min` n)
         sequence [ arb s (n `div` (2 `min` k)) | i <- [1..k] ]

  shrink (Enq x us) =
    [ u | u <- us ] ++
    [ Enq x us' | us' <- shrink us ]
  shrink (Deq us) =
    [ u | u <- us ] ++
    [ Deq us' | us' <- shrink us ]
  shrink _ = []

-- the given fuel is enough to compute everything
prop_EnoughFuel :: Usage A -> Property
prop_EnoughFuel u =
  whenFail (print (fuel u empty) >> print (need [u])) $
    run u empty (fuel u empty) == () 

-- the given fuel cost is linear (time is a linear function)
prop_FuelLinear :: Usage A -> Property
prop_FuelLinear u =
  whenFail (print (fuel u empty) >> print (cost (fuel u empty)) >> print (time u)) $
    cost (fuel u empty) <= time u

-- tried to make this as tight as possible
time :: Usage a -> Int
time First      = 2
time (Enq _ us) = 5 + sum [ time u | u <- us ]
time (Deq   us) = 5 + sum [ time u | u <- us ]

main =
  do --quickCheckWith args prop_EnoughFuel
     quickCheckWith args prop_FuelLinear
 where
  args = stdArgs{ maxSuccess = 10000, maxSize = 1000 }
  

