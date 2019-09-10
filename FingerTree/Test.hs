{-# LANGUAGE 
        
        FlexibleInstances,
        ViewPatterns,
        TemplateHaskell
        
#-}
module Main where

import Prelude hiding (seq )
import GHC.Exts(IsList(..))
import Test.QuickCheck
import Tree
import Data.Maybe (isNothing)
import Control.Monad
import Data.Function
import Control.Applicative(liftA3)


       

prop_PopLID :: NonEmptySeq Int -> Bool
prop_PopLID (NEFT s) = left <| rest == s 
        where 
               (left, rest) =popL s


prop_PopRID :: NonEmptySeq Int -> Bool
prop_PopRID (NEFT s) = rest |> right == s 
        where 
                (right, rest) =popR s
               

prop_MapS :: NonEmptySeq Int -> Bool
prop_MapS (NEFT s) = let s' = mapS (fmap (+1)) s in
        s' /= s && 
        mapS (fmap (\i -> i-1)) s' == s


prop_TraverseS :: NonEmptySeq Int -> Bool
prop_TraverseS (NEFT s) = traverseS Just s == Just s && 
        isNothing (traverseS (const Nothing) s :: Maybe (Seq Int))


prop_PopMax :: NonEmptyFingerTree (Minimax Int) (Value Int) -> Bool
prop_PopMax (NEFT h) = 
                max == max' && 
                h2 /= h
        where              
                (max', h2) = popMax h
                l = toList h
                max = maximum l 


prop_PopMin :: NonEmptyFingerTree (Minimax Int) (Value Int) -> Bool
prop_PopMin (NEFT h) = 
                min == min' && 
                h1 /= h 
        where 
                (min', h1) = popMin h
                l = toList h
                min = minimum l

                
prop_Concat :: NonEmptySeq Int -> NonEmptySeq Int -> Bool
prop_Concat (NEFT a) (NEFT b) = l1 <> l2 == l3
        where
                l1 = toList a 
                l2 = toList b 
                c = a Tree.>< b
                l3 = toList $ l1 ++ l2 
                
        
prop_Indexing :: Positive Int -> Bool
prop_Indexing (getPositive -> i) 
        | i > 1 = seq i ! i == Value i
        | otherwise = True


prop_listId :: [Int] -> Bool
prop_listId l = values == toList t
        where 
                values = map Value l
                t = fromList values :: SimpleFingerTree Int 


prop_adjust :: Positive Int -> (Int -> Int) -> Seq Int -> Property
prop_adjust (getPositive -> i) f s = i < size  ==> f a == a'
        where 
                (Size size) = measure s 
                (Value a, s') = adjust (Value . f . (\(Value a)-> a)) i s
                (Value a') = toList s' !! (i-1)


prop_replaceAt :: Positive Int -> Int -> NonEmptySeq Int -> Property
prop_replaceAt (getPositive -> i) a (NEFT s) = i < size ==>  a == a'
        where 
                (Size size) = measure s 
                (_, s') = replaceAt (Value a) i s
                (Value a') = toList s' !! (i-1)


instance (Arbitrary a, Measured a m) => Arbitrary (Vec m a) where
        arbitrary = (\e -> Vec (foldMap measure e) (length e) e) <$> (take maxLen  <$> infiniteList)

newtype NonEmptyFingerTree m a = NEFT (FingerTree m a) deriving (Show, Eq)

type NonEmptySeq a = NonEmptyFingerTree Size (Value a)

instance (Arbitrary a, Measured a m) => Arbitrary (NonEmptyFingerTree m a) where
        arbitrary = NEFT <$> frequency [
                (1, Single <$> arbitrary), 
                (2, liftA3 deep arbitrary arbitrary arbitrary)]


instance (Measured a m, Arbitrary a) => Arbitrary (FingerTree m a) where
        arbitrary = frequency [
                (1, pure Empty),
                (1, Single <$> arbitrary), 
                (2, liftA3 deep arbitrary arbitrary arbitrary)]


instance Arbitrary (Value Int) where 
        arbitrary = Value <$> arbitrary
                

instance {-# Overlapping #-} Arbitrary (Int -> Int) where
        arbitrary = oneof [(+) <$> arbitrary, (-) <$> arbitrary ,pure (*2)]

instance Show (Int -> Int) where
        show f = "f :: Int -> Int"

instance Arbitrary Interval where
        arbitrary = do
                a <- arbitrary ::Gen Int
                b <- arbitrary ::Gen Int
                if a < b 
                        then return $ Interval a b 
                        else return $ Interval b a



queue :: Int -> PriorityQueue Int
queue = fromList . mappedList (join Prioritized)

heap :: Int -> Heap Int
heap = fromList . mappedList Value 

seq :: Int -> Seq Int
seq = fromList . mappedList Value

mappedList f n = map f [1..n]


return []
runTests = $quickCheckAll

main :: IO ()
main =  runTests >>= print 