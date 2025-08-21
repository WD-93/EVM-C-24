import Distribution.Simple
import System.Process
import System.Directory

main :: IO ()
main = defaultMainWithHooks simpleUserHooks
  { preBuild = \args flags -> do
        let grammar = "E.cf"
        putStrLn $ "Regenerating parser from " ++ grammar
        error "Woop"
        callProcess "bnfc" ["--haskell",
                            --"--ghc",
                            --"--ghcopts=\"XMonadFailDesugaring\"",
                            "-o", "E", grammar]
        callProcess "alex" ["E/Lexer.x"]
        callProcess "happy" ["E/Parser.y"]
        preBuild simpleUserHooks args flags
  }
