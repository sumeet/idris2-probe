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

add : {w: Nat} -> {h: Nat} -> Point {w = w, h = h} -> (CoordDiff, CoordDiff)
      -> Maybe (Point {w = w, h = h})
add (x,y) (dx,dy) = do
    x' <- applyDiff x dx
    y' <- applyDiff y dy
    Just (x', y')


countFin : (x -> Bool) -> Vect n x -> Fin (n + 1)
countFin f [] = FZ
countFin f (x :: xs) = let rest = countFin f xs in
    if f x then shift 1 $ rest else weaken rest

NumNeighbors : Type
NumNeighbors = Fin 9

export
zipWithIndex : {n: Nat} -> Vect n a -> List (Integer, a)
zipWithIndex v = zip (take n [0..]) $ toList v

export
Grid : Nat -> Nat -> Type
Grid w h = Vect w (Vect h Bool)

get : Grid w h -> Fin w -> Fin h -> Bool
get grid x y = y `index` (x `index` grid)

conwayRules : Bool -> Nat -> Bool
conwayRules b n = n == 3 || n == 4 && b

export
nextGrid : Grid w h -> Grid w h
nextGrid grid = zipWith (zipWith conwayRules) grid numNeighbors
  where boolToNat : Bool -> Nat
        boolToNat True = 1
        boolToNat False = 0
        go : (a -> b) -> (b -> b -> b) -> (b -> b -> b -> b) -> b -> b -> Vect n a -> Vect (S n) b
        go c p p2 a b [] = [p a b]
        go c p p2 a b (x::xs) = let x' = c x in p2 a b x' :: go c p p2 b x' xs
        f : (a -> b) -> (b -> b -> b) -> (b -> b -> b -> b) -> Vect n a -> Vect n b
        f c _ _ [] = []
        f c _ _ [x] = [c x]
        f c p p2 (x::y::xs) = let x' = c x ; y' = c y in p x' y' :: go c p p2 x' y' xs
        add3 : Nat -> Nat -> Nat -> Nat
        add3 a b c = a + b + c
        numNeighbors : ?
        numNeighbors = f (f boolToNat (+) add3) (zipWith (+)) (zipWith3 add3) grid


export
flatGrid : {w: Nat} -> {h: Nat} -> Grid w h ->
           List ((Integer, Integer), Bool)
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
