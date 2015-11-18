#!/usr/bin/runhaskell

module NKMemLayout where

import Data.Array
type RAM    = Array Int Int
data Frame  = F Int RAM         -- The Int is the width of the RAM
            deriving Show

newRAM :: Int -> RAM
newRAM 0 = error "RAM must have at least one cell."
newRAM w = array (1,w) [(i,0) | i <- [1..w]]

-- asFrame :: RAM -> Frame
-- asFrame []      = error "Must have at least one Cell to make a Frame."
-- asFrame (_:xs)  = F (length xs) xs

-- asRAM :: Frame -> RAM
-- asRAM F w r = w : r
-- 
-- writeFrame :: Frame -> Int -> Int -> Frame
-- writeFrame (F w r)
