module Main

import System.Random
import Control.Linear.LIO
import SDL
import SDL.Foreign
import Data.Nat
import Data.Vect
import Data.List

putError : LinearIO io => (err : SDLError) -> L io ()
putError = putStrLn . show

windowOpts : SDLWindowOptions
windowOpts =
  MkSDLWindowOptions { name = "Example"
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
  putStrLn "=> SDL Inited"

  --let winops : SDLWindowOptions = record { width = size, height = size } defaultWindowOpts
  Success s <- newWindow windowOpts s
    | Failure s err => handleInitedError s (putError err)
  putStrLn "=> Window created"

  Success s <- newRenderer Nothing [SDLRendererSoftware] s
    | Failure s err => handleWindowedError s (putError err)
  putStrLn "=> Renderer operational"

  s <- myGameLoop s

  s <- closeRenderer s
  putStrLn "=> Renderer closed"
  s <- closeWindow s
  putStrLn "=> Window closed"
  quitSDL s
  putStrLn "=> SDL quitted"


main : IO ()
main = do
    run sdlLoop
