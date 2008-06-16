import DeMonad
import System.Environment

main = do 
    (src:_) <- getArgs
    mod     <- workFile src
    putStrLn mod 
    return ()

