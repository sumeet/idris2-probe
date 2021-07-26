module GOL

import Data.Fin
import Data.Fin.Extra
import Data.Linear.Array
import Data.List
import Data.Maybe
import Data.Vect
import System.Random

ConstantVect : Nat -> Type -> Type
ConstantVect n t = IArray t

partial
lolFromJust : Maybe t -> t
lolFromJust (Just x) = x

infixl 9 !!
partial
(!!) : Fin n -> ConstantVect n t -> t
n !! arr = lolFromJust $ read arr (cast $ finToInteger n)

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
NumNeighbors = Nat

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
    cast $ count (\case Nothing => False
                        Just (x,y) => get grid x y) neighbors
    where
        dxdys : Vect 8 (CoordDiff, CoordDiff)
        dxdys = [(Decr, Decr), (Decr, None), (Decr, Incr),
                 (None, Decr), (None, Incr),
                 (Incr, Decr), (Incr, None), (Incr, Incr)]

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
        numNeighbors : Vect w (Vect h NumNeighbors)
        numNeighbors = f (f boolToNat (+) add3) (zipWith (+)) (zipWith3 add3) grid


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
