{-# LANGUAGE DeriveGeneric, TypeOperators, TypeFamilies #-}
import Data.MemoTrie
import GHC.Generics (Generic) 

data Color = RGB Int Int Int
           | NamedColor String 
  deriving (Generic) 

instance HasTrie Color where
  newtype (Color :->: b) = ColorTrie { unColorTrie :: Reg Color :->: b } 
  trie      = trieGeneric ColorTrie 
  untrie    = untrieGeneric unColorTrie
  enumerate = enumerateGeneric unColorTrie

runColor (RGB r g b) = r + g + b
runColor (NamedColor s) = length [1..10e7] 

runColorMemoized = memo runColor 

main =
  do putStrLn "first call (should take a few seconds): " 
     print$ runColorMemoized (NamedColor "")
     putStrLn "cached call (should be instantaneous): " 
     print$ runColorMemoized (NamedColor "") 

