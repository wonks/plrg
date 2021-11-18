{- *Note:*
   Compile by `agda --compile HelloWorld.agda` .
-}

{-# OPTIONS --guardedness #-}

module HelloWorld where
  open import IO
  main = run {Agda.Primitive.lzero} (putStrLn "Hello, World!")
