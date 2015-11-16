{-# LANGUAGE CPP, PackageImports #-}
module Data.MemoTrie.Extra 
 ( Void
 ) where 

#if MIN_VERSION_base(4,8,0)
import "base" Data.Void
#else
import "void" Data.Void
#endif

