{-# LANGUAGE 
        OverloadedLists, 
        TypeFamilies, 
        ScopedTypeVariables, 
        MultiParamTypeClasses, 
        FlexibleInstances, 
        DeriveFunctor,
        FlexibleContexts,
        GeneralisedNewtypeDeriving
#-}
----------------------------------------------------------------------------------------
{-| 
== General information
Library implementing FingerTree, an efficient persistent general purpose data-structure, which can be easily specialized to implement other data structures.

* O(1) access to elements at beginning and end

* O(log n) access to other elements

* O(log n) concatenation

If this was to be released as library into real world, 
every application of FingerTree (eg. seq, heap) should probably be newtyped 
to achieve more modularity and user-friendlier API.
Though here I resorted to type aliasing instead, 
as it allows expressing the core functionality with much less boilerplate and copying code around.


== Other

Author: Tomas Zasadil

Created as project for classes Programming II and NonProcedural Programming.

in 1st class-year at Charles University, Faculty of Mathematics and Physics, General computer science

-}
module Tree (
    -- * FingerTree
      FingerTree(..)
    , Vec (..)
    , maxLen
    -- ** Operations
    , Structure (..)
    , bind
    , (><)
    , concatTrees
    , update
    , replace
    , deep
    
    -- ** Applications
    -- *** Order based FingerTrees
    , Heap, PriorityQueue, IntervalTree
    , popMax
    , popMin
    , overlapInclusive
    , overlapExclusive
    -- *** Indexed FingerTrees
    , Seq, SegmentTree
    , Indexed (..)
    -- ** Other
    , SimpleFingerTree
    , Measured (..)
    , Size (..)
    , Value (..)
    , Interval (..)
    , Segment (..)
    , Max (..)
    , Min (..)
    , Minimax (..)
    , Prioritized (..)





) where


import GHC.Exts(IsList(..))
import Data.Monoid
import Data.Maybe (fromMaybe)
import Data.Functor
import Data.Foldable (foldl')




class (Monoid m, Eq m) => Measured a m  where 
    measure :: a -> m

-- | API unifying FingerTree and Vec operations
class Structure (s :: * -> * -> *) where

    -- | Adds element at the beginning of the Structure
    infixr 5 <|
    (<|) ::(Measured a m) => a -> s m a -> s m a
    
    -- | Adds element at the end of the Structure
    infixl 5 |>
    (|>) ::(Measured a m) => s m a -> a -> s m a
    
    -- | Safely remove element from the end of the structure and return it along with new Structure
    popRSafe :: (Measured a m) => s m a -> Maybe (a, s m a)

    -- | Safely remove element from the beginning of the structure and return it along with new Structure
    popLSafe :: (Measured a m) => s m a -> Maybe (a, s m a)


    

    -- | Maps structure while changing annotation
    --
    -- /Note: Haskell unfortunately doesn't permit anything like 
    -- (Measured a m, Measured b m) => Functor (FingerTree m)  
    -- to make FingerTree a Functor whenever both 'a' and 'b' can be measured, 
    -- so general Functor instace needs to be instantiated separately for each concrete implemenatation /
    mapS :: (Measured a m, Measured b n) => (a -> b) -> s m a -> s n b

    -- | Traverses structure while changing annotation
    traverseS ::(Measured a m, Measured b n, Applicative f) => (a -> f b) -> s m a -> f (s n b)

    -- | Removes element from beginning of Structure and returns it along with new Structure
    popL:: (Measured a m) => s m a -> (a, s m a)
    popL = fromMaybe (error "cannot get any element from an empty tree") . popLSafe

    -- | Removes element from end of Structure and returns it along with new structure. Throws error if unable to retrieve any element
    popR :: (Measured a m) => s m a -> (a, s m a) 
    popR = fromMaybe (error "cannot get any element from an empty tree") . popRSafe
    
    -- | Safely get the first element of the Structure
    getLSafe :: (Measured a m) => s m a -> Maybe a     
    getLSafe s = fst <$> popLSafe s  

    -- | Safely get the first element of the Structure
    getRSafe :: (Measured a m) => s m a -> Maybe a     
    getRSafe s = fst <$> popRSafe s

    -- | Get the first element of the Structure.Throws error if unable to retrieve any element
    getL :: (Measured a m) => s m a -> a     
    getL = fst . popL  

    -- | Get the last element of the Structure.Throws error if unable to retrieve any element
    getR :: (Measured a m) => s m a -> a     
    getR = fst . popR

----------------------------------------------------------------------------------------
-- Vector
----------------------------------------------------------------------------------------
-- | List with length tracking and annotation, 
-- which provides auxiliary information about its elements
data Vec m a = Vec {
    annotation :: m,
    len :: Int,
    elems :: [a]
} deriving Eq

instance (Show a, Show m) => Show (Vec m a) where
    show (Vec ann l e) = "Vec { ann = "++show ann++", elems = "++show e++" }"

 

maxLen = 3 :: Int

-- | Make vector from single element
--
-- /O(1)/
mkVec :: Measured a m => a -> Vec m a
mkVec a = Vec (measure a) 1 [a]

-- | Predicate for whether vector has one element
--
-- /O(1)/
isOne:: Vec m a -> Bool
isOne v = len v == 1

-- | Predicate for whether vector is full
--
-- /O(1)/
isFull:: Vec m a -> Bool
isFull v = len v == maxLen 

instance Measured a m => Measured (Vec m a) m where
    measure = annotation 

instance Structure Vec where
    a <| v | isFull v = error "full vector"
           | otherwise = v {annotation = annotation v <> measure a, len = len v + 1, elems = a : elems v}
    
    v |> a | isFull v = error "full vector"
           | otherwise = v {annotation = getMeasure e ,len = len v + 1, elems = e}
        where e = elems v ++ [a]
    
    popLSafe v = Just (head $ elems v, v {annotation = getMeasure e, len = len v - 1, elems = e})
        where e = tail $ elems v
    
    popRSafe v = Just (last $ elems v, v {annotation = getMeasure e, len = len v - 1, elems = e})  
        where e = init $ elems v

    mapS f v = Vec (getMeasure e) (len v) e   --need to build new Vec because record update apparently cannot map type parameter
        where e = map f . elems $ v

    traverseS f v= (Vec . getMeasure <$> e <&> ($ len v)) <*> e
        where e = traverse f (elems v)


instance Measured a m => IsList (Vec m a) where
    type Item (Vec m a) = a
    
    fromList l | length l > maxLen = error "too many elements to put into vector"
                | otherwise = Vec (getMeasure l) (length l) l

    toList = elems
        
instance Foldable (Vec m) where
    foldr f b = foldr f b . elems
    foldMap f = foldMap f . elems

----------------------------------------------------------------------------------------
-- FingerTree
----------------------------------------------------------------------------------------
-- | General purpose tree-like structure, with annotation which provides auxiliary information about its elements thus enabling more efficient operations
data FingerTree m a 
    = Empty    -- ^ No elements 
    | Single a  -- ^ Single element 
    | Deep m (Vec m a) (FingerTree m (Vec m a)) (Vec m a)  -- ^ Tree-node with nonempty B+ tree on each side and pointer to next layer, whose B+ trees are one level deeper
    deriving (Show, Eq)


-- | Smart constructor for Deep which automaticaly resolves annotation
--
-- /O(1)/
deep :: Measured a m => Vec m a -> FingerTree m (Vec m a) -> Vec m a-> FingerTree m a
deep prefix deeper suffix = Deep annotation prefix deeper suffix 
    where annotation = measure prefix <> measure deeper <> measure suffix 


instance Measured a m => Measured (FingerTree m a) m where
    measure Empty = mempty
    measure (Single a) = measure a
    measure (Deep ann _ _ _) = ann

instance Structure FingerTree where
    -- | amortized O(1)
    -- Worst case /O(log n)/
    a <| Empty = Single a
    a <| Single b = deep (mkVec a) Empty (mkVec b)
    a <| Deep _ prefix tree suffix 
        | isFull prefix = deep (mkVec a) (prefix <| tree) suffix
        | otherwise =  deep (a <| prefix) tree suffix

    -- | amortized O(1)
    -- Worst case /O(log n)/
    Empty |> a = Single a
    Single b |> a = deep (mkVec b) Empty (mkVec a)
    Deep _ prefix tree suffix |> a 
        | isFull suffix = deep prefix (tree |> suffix) (mkVec a)
        | otherwise =  deep prefix tree (suffix |> a)

    -- | amortized O(1)
    -- Worst case /O(log n)/
    popLSafe Empty = Nothing
    popLSafe (Single a) = Just (a, Empty)
    popLSafe (Deep _ prefix Empty suffix) 
        | isOne prefix && isOne suffix = Just (getL prefix, Single $ getL suffix)
        | isOne prefix =  let (b, newSuf) = popL suffix in Just (getL prefix, deep (mkVec b) Empty newSuf) 
    popLSafe (Deep _ prefix tree suffix) 
        | isOne prefix = let (node, rest) = popL tree in Just (getL prefix, deep node rest suffix)
        | otherwise = fmap2 (\newPref -> deep newPref tree suffix) $ popLSafe prefix
    
    -- | amortized O(1)
    -- Worst case /O(log n)/
    popRSafe Empty = Nothing
    popRSafe (Single a) = Just (a, Empty)
    popRSafe (Deep _ prefix Empty suffix) 
        | isOne prefix && isOne suffix = Just (getR suffix, Single $ getL prefix)
        | isOne suffix =  let (b, newPref) = popR suffix in Just (getR suffix, deep newPref Empty (mkVec b)) 
    popRSafe (Deep _ prefix tree suffix) 
        | isOne suffix = let (node, rest) = popR tree in Just (getR prefix, deep node rest suffix)
        | otherwise =  fmap2 (deep prefix tree) $ popRSafe suffix

    -- | /O(n)/
    mapS _ Empty = Empty
    mapS f (Single a) = Single $ f a
    mapS f (Deep _ prefix tree suffix) = deep (mapS f prefix) (mapDeeper f tree) (mapS f suffix)
        where mapDeeper = mapS . mapS

    -- | /O(n)/
    traverseS f Empty = pure Empty
    traverseS f (Single a) = Single <$> f a
    traverseS f (Deep m prefix deeper suffix) = (deep <$> fprefix) <*> fdeeper <*> fsuffix
        where
            fprefix = traverseS f prefix
            fdeeper =  traverseS (traverseS f) deeper
            fsuffix = traverseS f suffix

instance Measured a m => IsList (FingerTree m a) where
    type Item (FingerTree m a) = a
    
    -- | /O(n)/ , could be improved by vectorising elements all at once instead of inserting them one by one
    fromList l = concatTrees Empty l Empty
   
    -- | /O(n)/
    toList = foldr (:) []


instance Foldable (FingerTree m) where
    foldMap _ Empty = mempty
    foldMap f (Single a) = f a 
    foldMap f (Deep _ prefix deeper suffix) = foldMap f prefix <> foldMap (foldMap f) deeper <> foldMap f suffix

-- | Concatenation of two FingerTrees
--
-- /O(log n)/
--
-- @Not an associative operation => FingerTree is __not__ a Semigroup@
(><) :: (Measured a m ) => FingerTree m a -> FingerTree m a -> FingerTree m a
left >< right = concatTrees left [] right


-- | Monadic bind that requires measured instance
--
-- /O(n)/
bind :: (Measured a m) => FingerTree m a -> (a -> FingerTree m a) -> FingerTree m a
bind t f = foldl' (\acc a -> acc >< f a) Empty t


-- | Concatenates two trees together and puts additional elements in the middle
--
-- /O(n)/
--
-- Best case /O(log n)/ when number of elements in middle is asymptoticaly irelevant 
concatTrees :: Measured a m 
           => FingerTree m a    -- ^ tree1
           -> [a]               -- ^ elements to put between the two trees
           -> FingerTree m a    -- ^ tree 2 
           -> FingerTree m a 

concatTrees Empty [] right = right
concatTrees Empty (x:xs) right = x <| concatTrees Empty xs right
concatTrees (Single y) xs right = y <| concatTrees Empty xs right

concatTrees left [] Empty = left
concatTrees left xs Empty = concatTrees left (init xs) Empty |> last xs
concatTrees left xs (Single y) = concatTrees left xs Empty |> y

--forms a new Deep using left prefix and right suffix. Left suffix and right prefix are added to buffer, then flushed into deeper layer
concatTrees (Deep _ prefix1 deeper1 suffix1) buffer (Deep _ prefix2 deeper2 suffix2) = deep prefix1 concatDeeper suffix2
    where
        concatDeeper = concatTrees deeper1 buffer' deeper2
        buffer' =  suffix1 : vectorise [prefix2] buffer       
       
        -- | puts elements into vector
        -- /O(n)/
        vectorise :: Measured a m 
            => [Vec m a]  -- ^ list to prepend to
            -> [a]      -- ^ elements to put into vectors
            -> [Vec m a]
        vectorise s [] = s
        vectorise s l = Vec (getMeasure taken) (length taken) taken : vectorise s (drop maxLen l)
            where taken = take maxLen l



-- | Update first element which satisfies annotation predicate
--
-- /O(log n)/
update  :: Measured a m
        => (m -> Bool)          -- ^ annotation predicate
        -> (a->a)               -- ^ updating function
        -> FingerTree m a       -- ^ structure to update
        -> (a, FingerTree m a)  -- ^ (oldValue, newFingerTree)
update p up = update' (\_ a -> (a, up a)) p mempty 
    where    
        update':: forall a b m. Measured a m
            => (m -> a -> (b,a))        -- ^ update element from nested vectors               
            -> (m -> Bool)              -- ^ predicate 
            -> m                        -- ^ accumulated annotation
            -> FingerTree m a     
            -> (b, FingerTree m a)      -- ^ popped element is of type 'a' from the view of top-level Fingertree,
                                        -- ^ but while recursing the return type changes to (a, Fingertree m (Vec(..(Vec a))),
                                        -- ^ so there needs to be 'b' in order to typecheck 
        update' f p m0 Empty = notFound
        update' f p m0 (Single a) = if p $ m0 <> measure a 
            then f m0 a <&> Single 
            else notFound
        update' f p m0 (Deep ann prefix deeper suffix)
            | not . p $ m0 <> ann = notFound
            | p mPrefix = updatedPrefix <&> \prefix' -> deep prefix' deeper suffix 
            | p mDeeper =  updatedDeeper <&> \deeper' -> deep prefix deeper' suffix
            | otherwise =  updatedSuffix <&> deep prefix deeper 
            
            where
                mPrefix = m0 <> measure prefix
                mDeeper = mPrefix <> measure deeper

                updatedPrefix = updateVec f m0 prefix
                updatedDeeper = update' (updateVec f) p mPrefix deeper
                updatedSuffix = updateVec f mDeeper suffix

                updateVec :: (m -> a -> (b, a)) -> m -> Vec m a -> (b, Vec m a)       
                updateVec f ann v =  fmap (rebuild $ len v) . mapFirst f ann . elems $ v

                mapFirst :: (m -> a -> (b,a)) -> m -> [a] ->(b,[a])
                mapFirst f m0 (x:xs) 
                    | p m = (:xs) <$> f m0 x
                    | otherwise =  (x:) <$> mapFirst f m xs
                    where m = m0 <> measure x

                rebuild :: Int -> [a]  -> Vec m a
                rebuild len newElems = Vec (getMeasure newElems) len newElems

        notFound = error "Element not found"

-- | Replaces first element satifying annotation predicate
--
-- /O(log n)/
replace  :: Measured a m
        => (m -> Bool)          -- ^ predicate
        -> a                    -- ^ new value
        -> FingerTree m a       -- ^ structure 
        -> (a, FingerTree m a)  -- ^ (oldValue, newFingerTree)
replace p new = update p (const new)



-- Helper function which maps rank2 functors
fmap2 ::(Functor f, Functor g) => (a -> b) -> f (g a) -> f (g b)
fmap2 = fmap . fmap

-- | Measures a foldable
getMeasure :: (Foldable f, Monoid m , Measured a m) => f a -> m
getMeasure = foldMap measure


----------------------------------------------------------------------------------------
-- Applications
----------------------------------------------------------------------------------------

type Seq a = FingerTree Size (Value a)

type PriorityQueue a =  FingerTree (Minimax Int) (Prioritized a)

type Heap a = FingerTree (Minimax a) (Value a)

type SimpleFingerTree a = FingerTree () (Value a)

type SegmentTree a = FingerTree (Segment a) (Value a)

type IntervalTree = FingerTree (Minimax Int) Interval
              
-- | Removes minimal element and returns it along with modified tree
--
-- /O(log n)/
popMin ::(Ord a, Ord b, Measured a (Minimax b)) => FingerTree (Minimax b) a -> (a, FingerTree (Minimax b) a)
popMin (Single a )= (a, Empty)
popMin t =  if min == minLeft 
            then (left, rest)
            else replace (\(Minimax(m,_)) -> min == m) left rest
    where 
        (left, rest) = popL t
        (Minimax (min,_)) = measure t
        (Minimax (minLeft,_)) = measure left 
    
-- | Removes maximal element and returns it along with modified tree
--
--  /O(log n)/
popMax ::(Ord a, Ord b, Measured a (Minimax b)) => FingerTree (Minimax b) a -> (a, FingerTree (Minimax b) a)
popMax (Single a) = (a, Empty)
popMax t =  if max == maxLeft 
            then (left, rest)
            else replace (\(Minimax(_,m)) -> max == m) left rest
    where 
    (left, rest) = popL t
    (Minimax (_,max)) = measure t
    (Minimax (_,maxLeft)) = measure left 


-- | Finds first occurence in tree which ovelaps with supplied exclusive interval 
--
-- /O(log n)/
overlapExclusive :: Interval -> IntervalTree -> Interval
overlapExclusive i t = fst $ update pred id t 
    where pred (Minimax(Min min, Max max))= low i < max && min < high i

-- | Finds first occurence in tree which ovelaps with supplied inclusive interval 
--
-- /O(log n)/
overlapInclusive :: Interval -> IntervalTree -> Interval
overlapInclusive i t = fst $ update pred id t 
    where pred (Minimax(Min min, Max max))= low i <= max && min <= high i

class Indexed i where
    -- | Locates size inside a datatype
    getSize :: i -> Int

    -- | Adjusts n-th element
    adjust :: Measured a i => (a -> a) -> Int -> FingerTree i a -> (a,FingerTree i a)
    adjust f i = update ((>= i).getSize) f

    -- | Gets n-th element 
    (!) :: Measured a i => FingerTree i a -> Int -> a
    tree ! i 
        | i > 1 = fst $ update ((>= i).getSize) id tree 
        | otherwise = error "Index needs to be bigger than 1"

    -- | Replaces n-th element
    replaceAt ::Measured a i => a -> Int -> FingerTree i a -> (a, FingerTree i a)
    replaceAt a = adjust (const a)


-- | tracking of minimum with monoidical identity 
data Max a = Max a | MinusInf deriving (Show, Eq)

-- | tracking of maximum with monoidical identity 
data Min a = Min a | Inf   deriving (Show, Eq)

-- | Tracking of both maximum and minimum
newtype Minimax a = Minimax (Min a, Max a)  deriving (Show, Eq, Semigroup, Monoid)

-- | Tracking of size and sum
newtype Segment a = Segment (Size, Sum a) deriving (Show, Eq, Semigroup, Monoid)


-- | Data with priority
data Prioritized a = Prioritized {
    priority :: Int,
    val :: a
} deriving (Show,Functor)

-- | Interval with start and end 
data Interval = Interval {
    low::Int, 
    high::Int
} deriving Show

newtype Size = Size Int deriving (Show, Eq, Ord)

newtype Value a = Value a deriving (Functor, Eq, Ord)

instance Show a => Show (Value a) where
    show (Value a) = show a



instance Measured Interval (Minimax Int) where
    measure (Interval l h) = Minimax (Min l, Max h)  

instance (Eq a, Num a) => Measured (Value a) (Segment a) where
    measure (Value a) = Segment (Size 1,Sum a)

instance Indexed Size where
    getSize (Size s) = s
instance Indexed (Segment a) where 
    getSize (Segment (Size s, _)) = s
    
instance Semigroup Size where
    Size x <> Size y = Size $ x + y

instance Monoid Size where
    mempty = Size 0
    
instance Measured (Value a) Size where
    measure _ = Size 1
    
instance Ord a => Semigroup (Max a) where
    MinusInf <> p = p
    p <> MinusInf = p
    Max a <> Max b = Max $ bigger a b
        where bigger a b = if a > b then a else b

instance Ord a => Monoid (Max a) where 
    mempty = MinusInf

instance Ord a => Semigroup (Min a) where
    Inf <> p = p
    p <> Inf = p
    Min a <> Min b = Min $ smaller a b
        where smaller a b = if a < b then a else b

instance Ord a => Monoid (Min a) where 
    mempty = Inf

instance Ord a => Measured (Prioritized a) (Minimax Int) where
    measure = Minimax . (\p -> (Min p, Max p)) . priority

instance Ord a => Measured (Value a) (Minimax a) where
    measure (Value a) = Minimax (Min a, Max a)

instance Measured (Value a) () where
    measure _ = ()
    

---------------------------------------------------------------------------------------
-----------------------------------------------------------------------------------------------------
       
--s n= fromList  $ map Value [1..n] :: SegmentTree Int
