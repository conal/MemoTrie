{-# LANGUAGE DeriveGeneric, TypeOperators, TypeFamilies #-}
import Data.MemoTrie
import GHC.Generics (Generic) 

data Color 
 = RGB Int Int Int
 | Color String 
 deriving (Generic) 

instance HasTrie Color where
 newtype (Color :->: b) = ColorTrie { unColorTrie :: Reg Color :->: b } 
 trie = trieGeneric ColorTrie 
 untrie = untrieGeneric unColorTrie
 enumerate = enumerateGeneric unColorTrie

runColor (RGB r g b) = r + g + b
runColor (Color s) = length [1..10e7] 

runColorMemoized = memo runColor 

main = do 
 putStrLn "first call (should take a few seconds): " 
 print$ runColorMemoized (Color "")
 putStrLn "cached call (should be instantaneous): " 
 print$ runColorMemoized (Color "") 

