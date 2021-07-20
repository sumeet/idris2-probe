module GOL

import Data.Fin
import Data.Fin.Extra
import Data.Vect
import Data.List
import System.Random

export
Point : {w: Nat} -> {h: Nat} -> Type
Point = (Fin w, Fin h)

export
getx : {w: Nat} -> Point {w=w, h=_} -> Fin w
getx = fst

export
gety : {h: Nat} -> Point {w=_, h=h} -> Fin h
gety = snd

data CoordDiff = Decr | None | Incr

applyDiff : {n: Nat} -> Fin n -> CoordDiff -> Maybe (Fin n)
applyDiff x None = Just x
applyDiff FZ Decr = Nothing
applyDiff (FS k) Decr = Just $ weaken k
applyDiff k Incr = strengthen $ shift 1 k

add : {w: Nat} -> {h: Nat} -> Point {w = w, h = h} ->
      (CoordDiff, CoordDiff) -> Maybe (Point {w = w, h = h})
add (x,y) (dx,dy) = Just (!(applyDiff x dx), !(applyDiff y dy))

countFin : (x -> Bool) -> Vect n x -> Fin (n + 1)
countFin f [] = FZ
countFin f (x :: xs) = let rest = countFin f xs in
    if f x then shift 1 $ rest else weaken rest

NumNeighbors : Type
NumNeighbors = Fin 9

export
zipWithIndex : {n: Nat} -> Vect n a -> Vect n (Fin n, a)
zipWithIndex v = zip Data.Vect.Fin.range v

export
Grid : Nat -> Nat -> Type
Grid w h = Vect w (Vect h Bool)

get : Grid w h -> Fin w -> Fin h -> Bool
get grid x y = y `index` (x `index` grid)

-- Any live cell with two or three live neighbours survives.
-- Any dead cell with three live neighbours becomes a live cell.
-- All other live cells die in the next generation. Similarly, all other dead cells stay dead.
applyConwayRules : Bool -> NumNeighbors -> Bool
applyConwayRules True 2 = True
applyConwayRules True 3 = True
applyConwayRules False 3 = True
applyConwayRules _ _ = False

numOnNeighbors : {w: Nat} -> {h: Nat} -> Grid w h -> Point {w = w, h = h}
                 -> NumNeighbors
numOnNeighbors grid xy = let neighbors = map (add xy) dxdys in
    countFin (\case Nothing => False
                    Just (x,y) => get grid x y) neighbors
    where
        dxdys : Vect 8 (CoordDiff, CoordDiff)
        dxdys = [(Decr, Decr), (Decr, None), (Decr, Incr),
                 (None, Decr), (None, Incr),
                 (Incr, Decr), (Incr, None), (Incr, Incr)]

export
nextGrid : {w: Nat} -> {h: Nat} -> Grid w h -> Grid w h
nextGrid grid =
    let cols = map (zipWithIndex {n = h}) grid
        cells = zipWithIndex {n = w} cols in
    map (\(x, cols) =>
            map (\(y, cell) =>
                    applyConwayRules cell $ numOnNeighbors grid (x,y))
                cols)
        cells


export
flatGrid : {w: Nat} -> {h: Nat} -> Grid w h ->
           Vect (w * h) (Point {w=w, h=h}, Bool)
flatGrid grid =
    let cols = map (zipWithIndex {n = h}) grid
        cells = zipWithIndex {n = w} cols
        gridWithIndex =
            map (\(x, cols) =>
                    map (\(y, cell) => ((x,y), cell)) cols)
                cells in
    concat gridWithIndex


export
initGrid : {w: Nat} -> {h: Nat} -> IO (Grid w h)
initGrid = do
    sequence $ Data.Vect.replicate w $
        sequence $ Data.Vect.replicate h (rndSelect [True, False])
