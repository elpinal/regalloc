module Main

import Data.SortedMap
import Data.SortedSet

data Node = MkNode String Int

Eq Node where
  (MkNode s1 i1) == (MkNode s2 i2) = s1 == s2 && i1 == i2

getName : Node -> String
getName (MkNode s _) = s

getWeight : Node -> Int
getWeight (MkNode _ i) = i

node0 : String -> Node
node0 s = MkNode s 0

data Graph = MkGraph (List (Node, List String))

mapGraph : (List (Node, List String) -> List (Node, List String)) -> Graph -> Graph
mapGraph f (MkGraph x) = MkGraph $ f x

inc : Node -> Node
inc (MkNode name i) = MkNode name $ i + 1

neighbors : Graph -> String -> Maybe (List String)
neighbors (MkGraph []) _ = Nothing
neighbors (MkGraph ((n, ss) :: ps)) s = if getName n == s then Just ss else neighbors (MkGraph ps) s

heaviest : (Maybe (Node, List String)) -> Graph -> Graph -> (Maybe (Node, List String), Graph, Graph)
heaviest n (MkGraph []) g = (n, MkGraph [], g)
heaviest mn (MkGraph ((n, ns) :: ps)) (MkGraph qs) =
  let w = getWeight n in
    if w > maybe (-1) (getWeight . fst) mn
      then heaviest (Just (n, ns)) (MkGraph ps) (MkGraph $ f mn)
      else heaviest mn (MkGraph ps) (MkGraph $ (n, ns) :: qs)
        where
          f Nothing = qs
          f (Just p) = p :: qs

first : (a -> b) -> (a, c) -> (b, c)
first f (x, y) = (f x, y)

incNeighbors : List String -> Graph -> Graph
incNeighbors _ (MkGraph []) = MkGraph []
incNeighbors ns (MkGraph (p :: ps)) =
  f $ if getName (fst p) `elem` ns
    then first inc
    else id
  where
    f : ((Node, List String) -> (Node, List String)) -> Graph
    f g = mapGraph (\x => g p :: x) $ incNeighbors ns $ MkGraph ps

-- Maximum cardinality search
mcs : Graph -> List (String, List String)
mcs g =
  let (qq, _, g') = heaviest Nothing g (MkGraph []) in
    case qq of
      Nothing => []
      Just (n, ns) => (getName n, ns) :: mcs (incNeighbors ns g')

Color : Type
Color = Int

lowest : List Color -> Color
lowest = f 0 . sort
  where
    f : Int -> List Color -> Color
    f n [] = n
    f n (c :: cs) = if n /= c then n else f (n + 1) cs

coloring' : List (String, List String) -> SortedMap String Color -> SortedMap String Color
coloring' [] m = m
coloring' ((name, ns) :: xs) m = coloring' xs $ insert name n m
  where
    f : List (Maybe a) -> List a
    f [] = []
    f (Nothing :: x) = f x
    f (Just a :: x) = a :: f x

    n : Color
    n = lowest $ f $ map (\n => lookup n m) ns

coloring : List (String, List String) -> SortedMap String Color
coloring xs = coloring' xs empty

namespace instruction
  data Inst = Mov String String | Add String String String

  Graph : Type
  Graph = SortedMap String (SortedSet String)

  update : Ord a => k -> SortedMap k (SortedSet a) -> (SortedSet a -> SortedSet a) -> SortedMap k (SortedSet a)
  update k m f = (\v => insert k v m) $ f $ fromMaybe empty $ lookup k m

  interfere : String -> instruction.Graph -> SortedSet String -> instruction.Graph
  interfere d g u = foldr (\x, acc => update x acc $ insert d) (update d g $ union u) u

  buildGraph : List Inst -> instruction.Graph
  buildGraph = snd . foldr (\i, acc => f i acc) (empty, empty)
    where
      f : Inst -> (SortedSet String, instruction.Graph) -> (SortedSet String, instruction.Graph)
      f (Mov d s)     (u, g) = (insert s $ delete d u             , interfere d g $ delete s $ delete d u)
      f (Add d s1 s2) (u, g) = (insert s2 $ insert s1 $ delete d u, interfere d g $ delete d u)
