module Main

import Control.Linear.LIO
import SDL
import SDL.Foreign
import Data.Nat
import Data.Fin
import Data.Vect
import Data.List

import GOL

putError : LinearIO io => (err : SDLError) -> L io ()
putError = putStrLn . show

width : Nat
width = 500

height : Nat
height = 500

windowOpts : SDLWindowOptions
windowOpts =
  MkSDLWindowOptions { name = "GoL"
                     , x = SDLWindowPosCentered
                     , y = SDLWindowPosCentered
                     , width = cast Main.width
                     , height = cast Main.height
                     , flags = []
                     }

%auto_implicit_depth 256
black : SDLColor
black = RGBA 0 0 0 255

white : SDLColor
white = RGBA 255 255 255 255
%auto_implicit_depth 50

delay : Nat
delay = 50 -- in ms

drawPoints : LinearIO io => {w: Nat} -> {h: Nat} -> (1 _ : SDL WithRenderer)
             -> List (Point {w=w, h=h}, Bool) -> L {use = 1} io (SDL WithRenderer)
drawPoints s [] = pure1 s
drawPoints s ((point, onOrOff) :: xs) =
  let x = finToInteger $ getx point
      y = finToInteger $ gety point
      rect = MkRect (cast x) (cast y) 1 1 in do
  Success s <- fillRect rect s
    | Failure s err => do putError err
                          pure1 s
  drawPoints s xs
  

myGameLoop : LinearIO io => {w: Nat} -> {h: Nat} -> (1 _ : SDL WithRenderer) -> Grid w h -> L {use = 1} io (SDL WithRenderer)
myGameLoop s grid = do
    Success s <- setColor white s
        | Failure s err => do putError err
                              pure1 s

    Success s <- clear s
        | Failure s err => do putError err
                              pure1 s

    Success s <- setColor black s
        | Failure s err => do putError err
                              pure1 s
    s <- drawPoints s $ filter (\(_, onOrOff) => onOrOff) $ toList $ flatGrid grid
    s <- render s

    delaySDL delay
    myGameLoop s $ nextGrid grid


sdlLoop : (LinearIO io) => L io ()
sdlLoop = initSDL [SDLInitVideo] (\err => putStrLn "Fatal error: \{show err}") $ \s => do
  Success s <- newWindow windowOpts s
    | Failure s err => handleInitedError s (putError err)

  Success s <- newRenderer Nothing [SDLRendererSoftware] s
    | Failure s err => handleWindowedError s (putError err)

  grid <- liftIO $ initGrid {w=width, h=height}

  s <- myGameLoop s grid
  s <- closeRenderer s
  s <- closeWindow s
  quitSDL s

main : IO ()
main = do
    run sdlLoop
