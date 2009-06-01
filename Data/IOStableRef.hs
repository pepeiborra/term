-----------------------------------------------------------------------------
-- |
-- Module      :  Data.IOStableRef
-- Copyright   :  (c) Andrew Bromage 2002
-- License     :  BSD-style (see the file libraries/base/LICENSE)
-- 
-- Maintainer  :  libraries@haskell.org
-- Stability   :  experimental
-- Portability :  portable
--
-- Mutable references in the IO monad, with stable orderings.
--
-----------------------------------------------------------------------------

module Data.IOStableRef
  ( 
   IOStableRef,-- abstract, instance of: Eq, Ord, Typeable
   newIOStableRef,-- :: a -> IO (IOStableRef a)
   readIOStableRef,-- :: IOStableRef a -> IO a
   writeIOStableRef,-- :: IOStableRef a -> a -> IO ()
   modifyIOStableRef,-- :: IOStableRef a -> (a -> a) -> IO ()
   hashIOStableRef,-- :: IOStableRef a -> Int
   ) where

import Prelude
import Data.IORef
import Data.Unique

data IOStableRef a
  = IOStableRef !Unique !(IORef a)


instance Eq (IOStableRef a) where
  IOStableRef u1 _ == IOStableRef u2 _  = u1 == u2

instance Ord (IOStableRef a) where
  IOStableRef u1 _ <  IOStableRef u2 _  = u1 <  u2
  IOStableRef u1 _ <= IOStableRef u2 _  = u1 <= u2
  IOStableRef u1 _ >  IOStableRef u2 _  = u1 >  u2
  IOStableRef u1 _ >= IOStableRef u2 _  = u1 >= u2
  compare (IOStableRef u1 _) (IOStableRef u2 _) = compare u1 u2

hashIOStableRef :: IOStableRef a -> Int
hashIOStableRef (IOStableRef u _)
  = hashUnique u

newIOStableRef :: a -> IO (IOStableRef a)
newIOStableRef x
  = newUnique >>= \u -> newIORef x >>= \r -> return (IOStableRef u r)

readIOStableRef :: IOStableRef a -> IO a
readIOStableRef (IOStableRef _ r)
  = readIORef r

writeIOStableRef :: IOStableRef a -> a -> IO ()
writeIOStableRef (IOStableRef _ r)
  = writeIORef r

modifyIOStableRef :: IOStableRef a -> (a -> a) -> IO ()
modifyIOStableRef (IOStableRef _ r) f
  = modifyIORef r f

