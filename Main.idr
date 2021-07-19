module Main

import System.Random
import Control.Linear.LIO
import SDL
import SDL.Foreign
import Data.Nat
import Data.Vect
import Data.List

import GOL

putError : LinearIO io => (err : SDLError) -> L io ()
putError = putStrLn . show

windowOpts : SDLWindowOptions
windowOpts =
  MkSDLWindowOptions { name = "GoL"
                     , x = SDLWindowPosCentered
                     , y = SDLWindowPosCentered
                     , width = 500
                     , height = 500
                     , flags = []
                     }

%auto_implicit_depth 256
black : SDLColor
black = RGBA 0 0 0 255

red : SDLColor
red = RGBA 255 0 0 255
%auto_implicit_depth 50

delay : Nat
delay = 1000 -- in ms


myGameLoop : LinearIO io => (1 _ : SDL WithRenderer) -> L {use = 1} io (SDL WithRenderer)
myGameLoop s = do
    color <- liftIO $ rndSelect [red, black]

    Success s <- setColor color s
        | Failure s err => do putError err
                              pure1 s

    Success s <- clear s
        | Failure s err => do putError err
                              pure1 s

    s <- render s

    delaySDL delay
    myGameLoop s


sdlLoop : (LinearIO io) => L io ()
sdlLoop = initSDL [SDLInitVideo] (\err => putStrLn "Fatal error: \{show err}") $ \s => do
  Success s <- newWindow windowOpts s
    | Failure s err => handleInitedError s (putError err)

  Success s <- newRenderer Nothing [SDLRendererSoftware] s
    | Failure s err => handleWindowedError s (putError err)

  s <- myGameLoop s
  s <- closeRenderer s
  s <- closeWindow s
  quitSDL s

main : IO ()
main = do
    run sdlLoop
