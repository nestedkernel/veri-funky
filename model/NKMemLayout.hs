#!/usr/bin/runhaskell

module NKMemLayout where

import Data.Array
data Frame  = F FType FTable FRAM
            deriving Show
type FType  = (Int, Int, Int)
fTypeW      = 3
bottomF     :: FType
bottomF     = (0, 0, 0)

type FTable = [Int]
inBounds :: FTable -> (Int, Int) -> Bool
inBounds fLocs (low, high) = none (\fL -> fL < low || high < fL) fLocs

type FRAM   = [Int]
data FrameType  = Invalid | Valid

isType :: FrameType -> Frame -> Bool
frameType (F (0, _, _) _ _)             = Invalid
frameType (F (1, _, _) _ _)             = Invalid
frameType (F (2, _, _) _ _)             = Invalid   -- `fW >= 3`
frameType frameRAM@(F (fW, fT, fTableW) fTable fRAM)
    | fW /= length (asFRAM frameRAM)    = Invalid   -- `fW` accurate
    | fTableW /= length fTable          = Invalid   -- `fTableW` accurate
    | fT == 0                           = Invalid   -- Invalid `fT` flag
    | not (fTable `inBounds` fRAMBound) = Invalid   -- Bad `fTable`
    | otherwise                         = Valid
    where
        fRAMBound = (fTypeW + fTableW, fW)
asFRAM :: Frame -> FRAM
asFRAM (F (fW, fType, fTableW) fTable fRAM) = fW : fType : fTableW : fTable ++ fRAM
validAsFrame :: FRAM -> Bool
validAsFrame frameRAM@(fW : fT : fTableW : restFRAM)
                = case frameType (Frame (fW, fT, fTableW) fTable fRAM) of
                    Invalid -> False    -- FrameType is Invalid
                    -       -> True     -- Some not-Invalid FrameType
    where
        (fTable, fRAM)  = splitAt fTableW restFRAM
validAsFrame _  = False                 -- Must be 3+ cells
