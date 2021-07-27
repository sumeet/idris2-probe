module GOL

import Data.Fin
import Data.Fin.Extra
import Data.Linear.Array
import Data.List
import Data.Maybe
import Data.Vect
import System.Random

%builtin Natural Nat
%builtin Natural Fin
%builtin NaturalToInteger finToInteger
-- %builtin IntegerToNatural integerToFin

partial
lolFromJust : Maybe t -> t
lolFromJust (Just x) = x

ConstantVect : Nat -> Type -> Type
ConstantVect n t = IArray t

infixl 9 !!
partial
(!!) : Fin n -> ConstantVect n t -> t
n !! arr = lolFromJust $ read arr (cast $ finToInteger n)

export
zipWithIndex : {n: Nat} -> Vect n a -> Vect n (Fin n, a)
zipWithIndex v = zip Data.Vect.Fin.range v

partial
zip : {n: Nat} -> Vect n t1 -> ConstantVect n t2 -> Vect n (t1, t2)
zip v cv = map (\(i, vItem) => (vItem, (i !! cv))) $ zipWithIndex v

partial
withIndex : {n: Nat} -> ConstantVect n t -> Vect n (Fin n, t)
withIndex cv = zip Data.Vect.Fin.range cv

data HLPair : Type -> Type -> Type where
  (#) : a -> (1 _ : b) -> HLPair a b

fromLinRes : (1 _ : Res _ (const t)) -> t
fromLinRes (_ # x) = x

linFold' : ((1 _ : acc) -> el -> acc) -> (1 _ : acc) -> List el -> acc
linFold' fn acc [] = acc
linFold' fn acc (x::xs) = linFold' fn (fn acc x) xs

linFold : Foldable t => ((1 _ : acc) -> el -> acc) -> (1 _ : acc) -> t el ->
          acc
linFold fn acc foldable = linFold' fn acc $ toList foldable

export
fromVect : {n: Nat} -> {t: Type} -> Vect n t ->
           ConstantVect n t
fromVect vect = newArray (cast n) $ \mutArray =>
  let firstAcc : HLPair Int (LinArray t) = 0 # mutArray
      (max # arr) =
        linFold (\(i # arr), elem => (i + 1) # (fromLinRes $ (write arr i elem)))
                firstAcc
                vect in
      toIArray arr $ id

partial
mapToVect : {n: Nat} -> (t1 -> t2) -> ConstantVect n t1 -> Vect n t2
mapToVect f cv = map (\(n, item) => f (n !! cv)) $ withIndex cv

export
Point : {w: Nat} -> {h: Nat} -> Type
Point = (Fin w, Fin h)

export
getx : {w: Nat} -> Point {w=w, h=_} -> Fin w
getx = fst

export
gety : {h: Nat} -> Point {w=_, h=h} -> Fin h
gety = snd

add : {w: Nat} -> {h: Nat} -> Point {w = w, h = h} ->
      (Integer, Integer) -> Maybe (Point {w = w, h = h})
add (x,y) (dx,dy) = do
    x' <- integerToFin ((finToInteger x) + dx) w
    y' <- integerToFin ((finToInteger y) + dy) h
    Just (x', y')

--countFin : (x -> Bool) -> Vect n x -> Fin (n + 1)
--countFin f [] = FZ
--countFin f (x :: xs) = let rest = countFin f xs in
--    if f x then shift 1 $ rest else weaken rest

NumNeighbors : Type
NumNeighbors = Nat

export
Grid : Nat -> Nat -> Type
Grid w h = ConstantVect w (ConstantVect h Bool)

partial
get : Grid w h -> Fin w -> Fin h -> Bool
get grid x y = y !! (x !! grid)

-- Any live cell with two or three live neighbours survives.
-- Any dead cell with three live neighbours becomes a live cell.
-- All other live cells die in the next generation. Similarly, all other dead cells stay dead.
applyConwayRules : Bool -> NumNeighbors -> Bool
applyConwayRules True 2 = True
applyConwayRules True 3 = True
applyConwayRules False 3 = True
applyConwayRules _ _ = False

partial
numOnNeighbors : {w: Nat} -> {h: Nat} -> Grid w h -> Point {w = w, h = h}
                 -> NumNeighbors
numOnNeighbors grid xy = let neighbors = map (add xy) dxdys in
    cast $ count (\case Nothing => False
                        Just (x,y) => get grid x y) neighbors
    where
        dxdys : Vect 8 (Integer, Integer)
        dxdys = [(-1, -1), (-1, 0), (-1, 1),
                 (0, -1), (0, 1),
                 (1, -1), (1, 0), (1, 1)]

export
partial
nextGrid : {w: Nat} -> {h: Nat} -> Grid w h -> Grid w h
nextGrid grid =
    let cols = mapToVect (withIndex {n = h}) grid
        cells = zipWithIndex {n = w} cols in
    fromVect $ map (\(x, cols) =>
            fromVect $ map (\(y, cell) =>
                    applyConwayRules cell $ numOnNeighbors grid (x,y))
                cols)
        cells

export
partial
flatGrid : {w: Nat} -> {h: Nat} -> Grid w h ->
           Vect (w * h) (Point {w=w, h=h}, Bool)
flatGrid grid =
    let cols = mapToVect (withIndex {n = h}) grid
        cells = zipWithIndex {n = w} cols
        gridWithIndex =
            map (\(x, cols) =>
                    map (\(y, cell) => ((x,y), cell)) cols)
                cells in
    concat gridWithIndex

initGrid' : {w: Nat} -> {h: Nat} -> IO (Vect w (Vect h Bool))
initGrid' = do
    sequence $ Data.Vect.replicate w $ sequence $
      Data.Vect.replicate h (rndSelect [True, False])

export
initGrid : {w: Nat} -> {h: Nat} -> IO (Grid w h)
initGrid = do
  grid <- initGrid' {w=w, h=h}
  pure $ fromVect $ map fromVect grid
