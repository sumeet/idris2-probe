module Main

import Control.Linear.LIO
import SDL
import SDL.Foreign
import Data.Nat
import Data.Fin
import Data.Vect
import Data.List

import GOL

%builtin Natural Nat
%builtin Natural Fin
%builtin NaturalToInteger finToInteger
%builtin NaturalToInteger natToInteger

putError : LinearIO io => (err : SDLError) -> L io ()
putError = putStrLn . show

width : Nat
width = 250

height : Nat
height = 250

scale : Nat
scale = 4

windowOpts : SDLWindowOptions
windowOpts =
  MkSDLWindowOptions { name = "GoL"
                     , x = SDLWindowPosCentered
                     , y = SDLWindowPosCentered
                     , width = cast (Main.width * scale)
                     , height = cast (Main.height * scale)
                     , flags = []
                     }

%auto_implicit_depth 256
black : SDLColor
black = RGBA 0 0 0 255

white : SDLColor
white = RGBA 255 255 255 255
%auto_implicit_depth 50

background : SDLColor
background = black

foreground : SDLColor
foreground = white

delay : Nat
delay = 50 -- in ms

drawPoints : LinearIO io => (1 _ : SDL WithRenderer) ->
             List ((Integer, Integer), Bool) ->
             L {use = 1} io (SDL WithRenderer)
drawPoints s [] = pure1 s
drawPoints s (((x, y), onOrOff) :: xs) =
  let rect = MkRect (cast x * cast scale) (cast y * cast scale) (cast scale) (cast scale) in do
  Success s <- fillRect rect s
    | Failure s err => do putError err
                          pure1 s
  drawPoints s xs

myGameLoop : LinearIO io => {w: Nat} -> {h: Nat} ->
             (1 _ : SDL WithRenderer) -> Grid w h ->
             L {use = 1} io (SDL WithRenderer)
myGameLoop s grid = do
    Success s <- setColor background s
        | Failure s err => do putError err
                              pure1 s
    Success s <- clear s
        | Failure s err => do putError err
                              pure1 s
    Success s <- setColor foreground s
        | Failure s err => do putError err
                              pure1 s
    s <- drawPoints s $ filter (\(_, onOrOff) => onOrOff) $ flatGrid grid
    s <- render s
    delaySDL delay
    pure1 s
    --myGameLoop s (nextGrid grid)


sdlLoop : (LinearIO io) => L io ()
sdlLoop = initSDL [SDLInitVideo] (\err => putStrLn "Fatal error: \{show err}") $ \s => do
  Success s <- newWindow windowOpts s
    | Failure s err => handleInitedError s (putError err)

  Success s <- newRenderer Nothing [SDLRendererSoftware] s
    | Failure s err => handleWindowedError s (putError err)

  grid <- liftIO $ initGrid {w=width, h=height}

  s <- myGameLoop s $ nextGrid grid
  s <- closeRenderer s
  s <- closeWindow s
  quitSDL s

main : IO ()
main = do
    run sdlLoop
