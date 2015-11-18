---
title: Nested Kernel Memory Model
geometry: margin=2.5cm
...


We first must define what our basic unit of storage is. For our memory, it is a
`MACHINE-INT`. These are fixed sized machine integers. We should maybe only
allow unary operators at this level, as the individual memory cells can't
inspect each others content.

```maude
fmod RENAMED-INT is
    protecting INT *    ( sort Zero to MachineZero
                        , sort NzNat to MachineNzNat
                        , sort Nat to MachineNat
                        , sort NzInt to MachineNzInt
                        , sort Int to MachineInt
                        , op s_ : Nat -> NzNat to $succ_ .
                        , op sd_ : Nat Nat -> Nat to $sd_ .
                        , op -_ : Int -> Int to $neg_ .
                        , op _+_ : Int Int -> Int to $add__ .
                        , op _-_ : Int Int -> Int to $sub__ .
                        , op _*_ : Int Int -> Int to $mult__ .
                        , op _quo_ : Int NzInt -> Int to $quo__ .
                        , op _rem_ : Int NzInt -> Int to $rem__ .
                        , op _^_ : Int Nat -> Int to $pow__ .
                        , op abs : NzInt -> NzNat to $abs_ .
                        , op gcd__ : NzInt Int -> NzNat to $gcd__ .
                        , op lcm : NzInt NzInt -> NzNat to $lcm__ .
                        , op min : NzInt NzInt -> NzInt to $min__ .
                        , op max : NzInt NzInt -> NzInt to $max__ .
                        , op _xor_ : Int Int -> Int to $xor__ .
                        , op _>>_ : Int Int -> Int to $shr__ .
                        , op _<<_ : Int Int -> Int to $shl__ .
                        , op _divides_ : NzInt Int -> Bool to $divides__ .
                        ) .
endfm

fth BIT-WIDTH is
    protecting RENAMED-INT .
    op $nrBits : -> MachineNzNat .
    var N : MachineNzNat .
    eq ($divides 2 $nrBits) = true [nonexec] .
    ceq ($divides 2 N) = true
        if ($divides N $nrBits) /\ (N > 1) [nonexec] .
endfth

view 64-BIT from BIT-WIDTH to RENAMED-INT is
    op $nrBits to term 64 .
endv

fmod MACHINE-INT{W :: BIT-WIDTH} is
    vars I, J : MachineInt .
    var K : MachineNzInt .

    op $mask : -> MachineNzInt [memo] .
    eq $mask = $sub $nrBits 1 .

    op $sign : -> MachineNzInt [memo] .
    eq $sign : $pow 2 $mask

    op maxMachineInt : -> MachineNzInt [memo] .
    eq maxMachineInt = $sub $sign 1 .

    op minMachineInt : -> MachineNzInt [memo] .
    eq minMachineInt = $neg $sign .

    op $wrap_ : MachineInt -> MachineInt .
    op $wrap I = (I & maxMachineInt) | ($neg (I & $sign)) .
endfm
```


    ```maude
    fmod MEM is
        protecting MACHINE-INT{64-BIT} .
        sorts Mem .
        op ____ : Bit Bit Bit Bit -> Cell [ctor] .
        op __ : Cell Cell -> Mem [ctor assoc] .
    endfm

    fmod MEMR is
        protecting MEM .
        op read__ : Mem Cell -> Cell .
    endfm

    fmod MEMW is
        protecting MEM .
        op write___ : Mem Cell Cell -> Cell .
    endfm

    fmod MEMRW is
        protecting MEMR .
        protecting MEMW .
    endfm
    ```

I would like you to be able to say `MEM[(60,5)]`, indicating a memory that is 60
`Cell`s wide with a `Cell` being 5 `Bit`s wide. This requires parameterized
modules, with a theory on the `MEMSPEC` (tuple of two natural numbers),
indicating that the whole memory is addressable from one cell in the memory.

Or perhaps when a memory is created, an `Address` type for what is being stored
there is generated. This type is generated according to the minimum amount of
`Cell`s required to address the whole space.

The Nested Kernel needs to provide structural guarantees about the metadata
describing the layout of RAM for its clients. This file tries to lay out how it
operates "logically", so that we can verify properties about our "ideal" Nested
Kernel. Then implementing an acutal Nested Kernel is providing (in hardware as
an MMU, or in software as a virtualization layer) the (hopefully) small set of
functions the Nested Kernel needs to operate.


Memory
======

Definition
----------

I want to express here that `MEMR` is a parameterized module taking in a
memory-cell width `X`, and the number of memory cells `Y`. This module can only
`read` from the memory cells.

    ```maude
    fmod MEMR{X :: BIT-WIDTH, Y :: VECT{MACHINE-INT{X}, 2^X} is
        sort Mem .
        subsort MachineInt < Mem .
        op read : Mem Y -> Y .
    endfm
    ```
This module defines the functionality to `write` to memory cells.

    ```maude
    fmod MEMW{X :: BIT-WIDTH, Y :: MACHINE-INT{X-BIT}} is
        sort Mem .
        subsort MachineInt < Mem .
        op write : Mem Y -> Mem .
    endfm
    ```

But we also want memory we can `read` and `write` to:

    ```maude
    fmod MEMRW{X :: BIT-WIDTH, Y :: MACHINE-INT{X-BIT}} is
        protecting MEMR{X, Y} .
        protecting MEMW{X, Y} .
    endfm
    ```

System Memory
-------------

System memory may be a collection of many memories. We specify here that it must
satisfy the `NKMEM` theory constraint - which enforces the "Nested Kernel"
semantics on the `MEM`.

    ```maude
    fmod MEM{M :: NKMEM} is
        protecting MEMR .
        protecting MEMW .
        protecting MEMRW .
        sorts MemR MemW MemRW Mem .
        subsorts MemR MemW < MemRW < Mem .
        op __ : Mem Mem -> Mem .
    ```

    ```maude
    fmod MEM{MR :: LIST{MEMR}, MW :: LIST{MEMW}
    ```

The `NKMEM` theory constraint means that the `MEM` must have a certain

    ```maude
    fth NKMEM is

    endfth
    ```

We also want to be able to separate regions of memory for isolation of process
memory. This means we must have some memory which can lay virtual maps on top of
memory and decide if `read`s and `write`s to that memory are valid. I called
this `STORE` for "Nested Kernel memory". This memory has the semantic
constraints of the Nested Kernel imposed on it - the Nested Kernel decides
whether `read`s and `write`s between two memories are valid.

Memory Separation
-----------------

    ```maude
    fmod STORE{M :: NKMEM} is
        protecting MEM .
        sort SMem .
        subsort SMem < Mem .
    ```

The constraints on the `NKMEM` are expressed as the theory `SMEM`
