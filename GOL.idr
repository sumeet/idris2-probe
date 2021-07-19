module GOL

import Data.Fin
import Data.Fin.Extra
import Data.Vect
import Data.List
import System.Random

export
Grid : Nat -> Nat -> Type
Grid w h = Vect w (Vect h Bool)

get : Grid w h -> Fin w -> Fin h -> Bool
get grid x y = y `index` (x `index` grid)

Point : {w: Nat} -> {h: Nat} -> Type
Point = (Fin w, Fin h)

add : {w: Nat} -> {h: Nat} -> Point {w = w, h = h} -> (Integer, Integer)
      -> Maybe (Point {w = w, h = h})
add (x,y) (dx,dy) = do
    x' <- integerToFin ((finToInteger x) + dx) w
    y' <- integerToFin ((finToInteger y) + dy) h
    Just (x', y')

export
initGrid : {w: Nat} -> {h: Nat} -> IO (Grid w h)
initGrid = do
   sequence $ Data.Vect.replicate w $
    sequence $ Data.Vect.replicate h (rndSelect [True, False])

countFin : (x -> Bool) -> Vect n x -> Fin (n + 1)
countFin f [] = FZ
countFin f (x :: xs) = let rest = countFin f xs in
    if f x then shift 1 $ rest else weaken rest

numOnNeighbors : {w: Nat} -> {h: Nat} -> Grid w h -> Point {w = w, h = h}
                 -> Fin 9
numOnNeighbors grid xy = 
    let neighbors = map (add xy) dxdys in
        countFin (\case Nothing => False
                        Just (x,y) => get grid x y) neighbors
    where
        dxdys : Vect 8 (Integer, Integer)
        dxdys = [(-1, -1), (-1, 0), (-1, 1),
                (0, -1), (0, 1),
                (1, -1), (1, 0), (1, 1)]