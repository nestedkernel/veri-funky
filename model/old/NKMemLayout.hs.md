---
title: Nested Kernel Memory Model
geometry: margin=2.5cm
...


The Nested Kernel needs to provide structural guarantees about the metadata
describing the layout of RAM for its clients. This file tries to lay out how it
operates "logically", so that we can verify properties about our "ideal" Nested
Kernel. Then implementing an acutal Nested Kernel is providing (in hardware as
an MMU, or in software as a virtualization layer) the (hopefully) small set of
functions the Nested Kernel needs to operate.

```haskell
#!/usr/bin/runhaskell

module NKMemLayout where

import Data.Array
```


Data Definition
===============

Frames
------

### In RAM Model

`Frame`s are isolated chunks of data in RAM. They have a nested structure (can
have a `Frame` inside a `Frame`). When you are reading/writing to a `Frame` you
cannot read/write outside of its bounds. Additionally, modifications to
sub`Frame`s and your `Frame` table is restricted by a mediation function.

`Frame`s have some type `FType`, a structure information table called `FTable`,
and a region of RAM called `FRAM`. Any locations the `Frame` stores (such as
subframe locations) is in reference to the absolute beginning of the `Frame`,
taking into account the width of `FType` and `FTable`.

```haskell
type RAM    = Array Int Int
data Frame  = F Int RAM         -- The Int is the width of the RAM
            deriving Show

newRAM :: Int -> RAM
newRAM 0 = error "RAM must have at least one cell."
newRAM w = array (1,w) [(i,0) | i <- [1..w]]

asFrame :: RAM -> Frame
asFrame []      = error "Must have at least one Cell to make a Frame."
asFrame (_:xs)  = F (length xs) xs

-- asRAM :: Frame -> RAM
-- asRAM F w r = w : r
-- 
-- writeFrame :: Frame -> Int -> Int -> Frame
-- writeFrame (F w r)
```

The idea is that the Nested Kernel can read `FType` to know what enforcements
apply to the region of RAM described by the `Frame`. This could also lead to
providing convenient acces functions to data structures in `FRAM`.

    ```haskell
    type FType  = (Int, Int, Int)
    fTypeW      = 3
    bottomF     :: FType
    bottomF     = (0, 0, 0)

    type FTable = [Int]
    inBounds :: FTable -> (Int, Int) -> Bool
    inBounds fLocs (low, high) = none (\fL -> fL < low || high < fL) fLocs

    type FRAM   = [Int]
    ```

The `FType` is intended to be the total width of the `Frame`, a type descriptor,
and the width of the `Frame`s associated `FTable`. The `bottomF :: FType` type
may be thought of as an "error" `Frame` type, though it could also be used for
things like signaling a garbage collector.

`FTable` describes any subframe locations inside the current `Frame`. The
simplest check we can perform on it is whether every value in the table is
within some specified bound.

`FRAM` is straightforward, it describes all the non-metadata data in a `Frame`.
This is the "storage" space of the `Frame`, it holds the subframes and any other
information that the `Frame` is interested in tracking. A `Frame` is responsible
for keeping track of any data not in its subframes itself.

### Logical Model

We also want to be able to reason about a `Frame` in a logical sense (taking
advantage of Haskell's type system). To do so, we define a `FrameType`, which is
just an enumeration of all the types a `Frame` could be. We also define a
function `frameType :: Frame -> FrameType` which will allows us to use the
Haskell `case` statement to decide how to act on `Frame`s.

    ```haskell
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
    ```

So far we only have `Invalid` and `Valid` frames.

Interface
---------

We should be able to interperet a `Frame` as just a chunk of `FRAM`.

    ```haskell
    asFRAM :: Frame -> FRAM
    asFRAM (F (fW, fType, fTableW) fTable fRAM) = fW : fType : fTableW : fTable ++ fRAM
    ```

We want to be able to tell if a `FRAM` could be a valid `Frame`. All `Frame`s
must have the `fW` field accurately reflect the width of the `Frame`.
Additionally, all entries in the `FTable` must point to somewhere within the
`FRAM` of the `Frame`.

    ```haskell
    validAsFrame :: FRAM -> Bool
    validAsFrame frameRAM@(fW : fT : fTableW : restFRAM)
                    = case frameType (Frame (fW, fT, fTableW) fTable fRAM) of
                        Invalid -> False    -- FrameType is Invalid
                        -       -> True     -- Some not-Invalid FrameType
        where
            (fTable, fRAM)  = splitAt fTableW restFRAM
    validAsFrame _  = False                 -- Must be 3+ cells
    ```

First, we want to check if the specified sub`Frame` locations are in the bounds
of the `FRAM` of the `Frame`. This takes a `FTable`, the location of the actual
`FRAM` they are supposed to fit into, and returns `True` if any of the `FTable`
is out of bounds of the `FRAM`. This function assumes you have already pulled off
the first two entries of the `FTable`, which are the total and table widths.

    ```haskell
    outOfBound :: FTable -> (Loc, Loc) -> Bool
    outOfBound []                _      = False
    outOfBound [_]               _      = error "Invalid FTable."
    outOfBound (fs : fe : fRest) (s, e) =   (  (fs < s)
                                            || (fe > e)
                                            || (fe <= fs)
                                            || fRest `outOfBound` (s, e)
                                            )
    ```

We also need to check if any of the sub`Frame`s overlap. This function takes a
`FTable`, and returns `True` if any of the sub`Frame`s overlap with each
other. This check is independent of the `outOfBound` check, so both must be
performed to verify that a `FTable` is valid. This function also assumes you
have already pulled off the first two entries of the `FTable`.

    ```haskell
    framesOverlap :: FTable -> Bool
    framesOverlap []                = False
    framesOverlap [_]               = error "Invalid FTable."
    framesOverlap (f1s : f1e : f2s : f2e : frames)
        | f1s == f2s                = True
        | f1s < f2s && f1e > f2s    = True
        | f2s < f1s && f2e > f1s    = True
        | otherwise                 =   (  framesOverlap (f1s : f1e : frames)
                                        || framesOverlap (f2s : f2e : frames)
                                        )
    ```

Right now this `framesOverlap` function is not very efficient. For small
`FTable`s, this is fine, but if they grow we'll want to consider more
efficient strategies. One way may be to store the `FTable`s in sorted order
(by where they are in `FRAM`), then checking whether any of the sub`Frame`
locations overlap would be as simple as checking if the integers in the segment
of `FRAM` representing the `FTable` are weakly monotonic positive.

Invariants
----------

    ```haskell
    -- Reference Frame
    Frame FTable                            FRAM
    Frame lT@(width : tWidth : subFrames)   restFRAM :: Frame Valid
    ```

Frame Invariant 1)
:   The width of a `Frame` must be accurately reflected by the `fW` field.

    ```haskell
    sFRAM !! 0 == length . asFRAM
    ```

Frame Invariant 2)
:   The width of a `FTable` must be accurately reflected by it's `Frame`s
    `fTableW` field.

    ```haskell
    frame :: Frame
    asFRAM !! 2 == length . 
    ```


I1)
:   `FInterface`s should not change how much RAM a `Frame` uses.

    ```haskell
    fInterface  :: FInterface
    length . asRAM . fInterface == length . asRAM
    ```

I1)
:   `width` accurately reflects how much FRAM the `Frame` takes.

    ```haskell
    width == tWidth + length restFRAM
    ```

I2)
:   `tWidth` accurately reflects the size of `lT`.

    ```haskell
    tWidth == length lT
    ```

I3)
:   Sub`Frame`s exist inside the current `Frame` (and are sensible).

    ```haskell
    subFrames `outOfBound` (tWidth, width) == False
    ```

I4)
:   Sub`Frame`s do not overlap

    ```haskell
    framesOverlap subFrames == False
    ```

Interface
---------

### Internal - Only `MMU` can call

Create an empty `Frame` with a total size. This will be used at "boot" to
specify how much `FRAM` is available.

    ```haskell
    newFrame :: Loc -> Frame Valid
    newFrame width = Frame [width, 2] (replicate (width - 2) 0)
    ```

The function `asFRAM` takes a `Frame` (either `Valid` or `Invalid`) and
interperets it as a chunk of `FRAM` - this can be used for internal manipulations
on the `Frame` index. It can also be used to verify that a `Frame` is never
magically changing its size by checking that `length . asFRAM` is constant
throughout all allowed transitions.

    ```haskell
    asFRAM :: Frame a -> FRAM
    asFRAM (Frame lT ram) = lT ++ ram
    ```

Acts as a "coercive" type-cast, creates a `Frame Invalid`, which must be passed
through the `validateFrame` function to become a `Frame Valid`.

    ```haskell
    asFrame :: FRAM -> Frame Invalid
    asFrame []                          = error "Empty FRAM can't be a Frame."
    asFrame [_]                         = error "Frame needs at least two cells of FRAM."
    asFrame ram@(width : tWidth : rest) = Frame frameTable restFRAM
        where (frameTable, restFRAM) = splitAt tWidth ram
    ```

Function used by our "logical" `MMU` to check that a new `Frame` is valid. We
see here that all of the invariants specified above are checked for.

    ```haskell
    invalidFrame :: Frame Invalid -> Bool
    invalidFrame (Frame lT@(width : tWidth : subFrames) restFRAM)
        | width /= totalWidth               = True
        | tWidth /= length lT               = True
        | subFrames `outOfBound` ramBound   = True
        | framesOverlap subFrames           = True
        | otherwise                         = False
        where
            totalWidth  = length lT + length restFRAM
            ramBound    = (tWidth, width)
    ```

### External - Commands `MMU` Allows

Commands that the `MMU` exports must be of type `Frame Valid -> Frame Valid`.
This ensures that only the `MMU` ever deals with `Frame Invalid`s, and that all
operations on `Frame Valid`s happen atomically with respect to the ones on
`Frame Invalid`s.

We need to be able to request that a sub`Frame` be added to the current `Frame`s
list of sub`Frame`s. The steps to doing so (from the external CPUs perspective):

-   Write down a valid `Frame` somewhere in the current `Frame`s memory - the
    Nested Kernel will verify while you are writing that you are not writing on
    any of the metadata or on any of the other sub`Frame`s.

-   Write down the start and end position of the `Frame` (relative to the
    current `Frame`s chunk of `FRAM`) in the *first two positions* of your
    current `FRAM`. If the first two positions of your `FRAM` are occupied by a
    sub`Frame`, you are responsible for using the `MMU` interface to shuffle the
    `Frame`s around accordingly.

-   Call the `addSubFrame` function. It will either increment the current
    `Frame`s `tWidth` number or fail silently. Either way. the returned `Frame`
    will still be valid. Because you wrote down the start and end position of
    your `Frame` as the first two cells in `FRAM`, all it has to do is increment
    the `tWidth` number to include the new sub`Frame`. Additionally, the
    function does not need any inputs other than which `Frame` you want to add a
    sub`Frame` to, which the `MMU` will know. To check if it suceeded, the CPU
    may manually inspect the `tWidth` number to see if it changed - as we do not
    restrict reading the current `Frame`s metadata.

    ```haskell
    addSubFrame :: Frame Valid -> Frame Valid
    addSubFrame f@(Frame lT@(width : tWidth : subFrames) (fs : fe : restFRAM))
        | newSubFs `outOfBound` newFRAMBound = f     -- Specified frame outside this frame
        | framesOverlap newSubFs            = f     -- Interferes with existing subFrame
        | invalidFrame (asFrame frameFRAM)   = f     -- Invalid subFrame provided
        | otherwise                         = Frame (width : tWidth + 2 : newSubFs) restFRAM
        where
            newSubFs    = drop 2 (take (tWidth + 2) (asFRAM f))
            newFRAMBound = (tWidth + 2, width)
            frameFRAM    = take (fe - fs) (drop fs (asFRAM f))
    addSubFrame f@(Frame _ _)               = f     -- Anything else fails
    ```


MMU  *Unfinished*
=================


Look up BlueDBM - "in-memory processors". Also, MONET, CORFU, XSD, IBM CAPI


Ideas
=====

I think one thing we should think about is never allowing `error` statements.
The Nested Kernel should fail gracefully whenever possible (hopefully by
reverting to before the error state).

`NKMMU` as a type class where you have to provide some functions but can provide
others? Then get class heirarchy of `MMU`s of various power?
