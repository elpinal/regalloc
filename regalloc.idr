module Main

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
mcs : Graph -> List Node
mcs g =
  let (qq, _, g') = heaviest Nothing g (MkGraph []) in
    case qq of
      Nothing => []
      Just (n, ns) => n :: mcs (incNeighbors ns g')
