import Distribution.Simple
import System.Process
import System.Directory

--This seems to have no effect... the options are outdated now anyway.
--Replacing preBuild with a noop.
main :: IO ()
main = defaultMainWithHooks simpleUserHooks
  { preBuild = \args flags -> do
      {-
        let grammar = "E.cf"
        putStrLn $ "Regenerating parser from " ++ grammar
        error "Woop"
        callProcess "bnfc" ["--haskell",
                            --"--ghc",
                            --"--ghcopts=\"XMonadFailDesugaring\"",
                            "-o", "E", grammar]
        callProcess "alex" ["E/Lexer.x"]
        callProcess "happy" ["E/Parser.y"]
-}
        preBuild simpleUserHooks args flags
  }
