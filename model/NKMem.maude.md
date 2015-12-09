---
title: Nested Kernel Memory Model
geometry: margin=2.5cm
execute: maude
...


```maude{exec}
fmod CELL is
    protecting NAT .

    sort Cell .
    op cNil : -> Cell [ctor] .
    op _|=>_ : Nat Nat -> Cell [ctor prec 33] .
    op _;_ : Cell Cell -> Cell [assoc comm id: cNil prec 34] .

    op read_from_ : Nat Cell -> Cell .

    vars N M : Nat .
    var C : Cell .

    eq read N from (N |=> M ; C) = N |=> M .
    eq read N from C = cNil [owise] .
endfm

fmod RANGE is
    protecting NAT .
    protecting BOOL .

    --- Locations in RAM described by Nats, comparable as Nats

    sort Loc .

    op loc : Nat -> Loc [ctor] .
    op _<_ : Loc Loc -> Bool .
    op _<=_ : Loc Loc -> Bool .

    vars N M : Nat .

    eq loc(N) < loc(M) = N < M .
    eq loc(N) <= loc(M) = N <= M .

    --- A location range is a pair of two locations.
    --- We can test if a location is contained in a sequence of location ranges.

    sort LocRange .

    op (_,_) : Loc Loc -> LocRange [ctor] .
    op _|_ : LocRange LocRange -> LocRange [assoc ctor] .
    op _in_ : Loc LocRange -> Bool .

    vars L1 L2 L3 : Loc .
    vars LR1 LR2 : LocRange .

    eq (L1, L1) | LR1 = LR1 .
    eq L1 in (L2, L3) = (L2 <= L1) and (L1 < L3) .
    eq L1 in (LR1 | LR2) = (L1 in LR1) or (L1 in LR2) .

    --- Ultimately location ranges have to be stored in memory, so we need to
    --- know how much memory they take up.

    op size : LocRange -> Nat .

    eq size((L1, L2)) = 2 .
    eq size(LR1 | LR2) = size(LR1) + size(LR2) .
endfm

fmod PERMISSION is
    sorts Perm Permissions .
    subsort Perm < Permissions .

    op none : -> Perm [ctor] .
    op read : -> Perm [ctor] .
    op write : -> Perm [ctor] .
    op _|_ : Permissions Permissions -> Permissions [assoc comm id: none] .

    var N : Permissions .

    eq read | read = read .
    eq write | write = write .
endfm

fmod MEM is
    protecting CELL .
    protecting RANGE .
    protecting PERMISSION .

    sort Mem .
endfm
```

```maude
fmod NKMEM is
    protecting MEM-BOUNDS .
    protecting CELL .

    op mem : LocRange Cell -> Mem [ctor] .
    op _with_ : Mem Cell -> Mem .
    op read_from_ : Nat Mem -> Cell .

    var M : Mem .
    var N : Nat .
    var LR : LocRange .

    eq mem(LR) 
endfm
```


Retired Code
============

```maude
fmod CELL is
    protecting NAT .
    sorts Bit Cell .
    subsort Bit < Cell .
    ops b1 b0 : -> Bit [ctor] .
    op cNil : -> Cell [ctor] .
    op __ : Cell Cell -> Cell [ctor assoc id: cNil] .
    op makeCell : Nat -> Cell .

    var N : Nat .
    eq makeCell(0) = cNil .
    eq makeCell(s(N)) = b0 makeCell(N) .
endfm

fmod MEM is
    protecting CELL .
    protecting NAT .
    sort Mem .
    subsort Cell < Mem .
    op mNil : -> Mem [ctor] .
    op _|_ : Mem Mem -> Mem [ctor assoc id: mNil] .
    op makeMem : Nat Cell -> Mem .
    op doubleMem : Nat Mem -> Mem .
    op makeSquareMem : Nat -> Mem .
    op writeMem : Mem Cell Cell -> Mem .

    var N : Nat .
    var C : Cell .
    var M : Mem .

    eq makeMem(0, C) = mNil .
    eq makeMem(s(N), C) = C | makeMem(N, C) .
    eq doubleMem(0, M) = M .
    eq doubleMem(s(N), M) = doubleMem(N, M | M) .
    eq makeSquareMem(N) = doubleMem(N, makeCell(N)) .
endfm

mod MEM is
    including CONFIGURATION .
    protecting CELL .
    protecting QID .

    sort Memory .
    sort Mask .

    subsort Cell < Attribute .
    subsort Memory < Configuration .

    op Mem : -> Cid [ctor] .
    op  : Qid -> Oid [ctor] .
    op makeMemory : Nat -> Memory .
    op makeProcess : Oid Nat -> Process .

    vars N1 N2 N3 N4 N5 N6 : Nat .
    vars P1 P2 P3 : Oid .
    var A : AttributeSet .
    vars M1 M2 : Msg .

    eq makeMemory(0) = none .
    eq makeMemory(s(N1)) = cell(s(N1),0) , makeMemory(N1) .

    eq makeProcess(P1, N1) = < P1 : Proc | makeMemory(N1) > .

    --- eq M1 ; M2 = 

    rl [copyWithin] :
        < P1 : Proc | cell(N1,N2) , cell(N3, N4) , A >
            copy(N1, N3)
        => < P1 : Proc | cell(N1, N4) , cell(N3, N4) , A > .

    rl [writeVal] :
        < P1 : Proc | cell(N1,N2) , A >
            write(N1,N3)
        => < P1 : Proc | cell(N1,N3) , A > .
endm

fmod MEM is
    protecting CELL .
    protecting QID .

    sort Mem .
    subsort Cell < Mem .

    --- Making memory

    vars N M : Nat .

    op __ : Mem Mem -> Mem [assoc id: cNil] .
    op makeMemory : Nat -> Mem .

    eq makeMemory(0) = cNil .
    eq makeMemory(s(N)) = cell(s(N),0) | makeMemory(N) .

    --- Making a memory read-/write-only

    op roMem : Mem -> Mem [ctor] .
    op woMem : Mem -> Mem [ctor] .
    op rwMem : Mem -> Mem [ctor] .

    --- Read/write to memory

    op writeMem : Mem Nat Nat -> Mem .
    op readMem : Mem Nat -> Cell .

    var M* : Mem .

    eq writeMem(woMem(cell(N,M) M*), N, P) = cell(N,P) M* .
    eq writeMem(rwMem(cell(N,M) M*), N, P) = cell(N,P) M* .
    eq writeMem(M*, N, P) = M* [owise] .

    eq readMem(roMem(cell(N,M) M*), N) = cell(N,M) .
    eq readMem(rwMem(cell(N,M) M*), N) = cell(N,M) .
    eq readMem(M*, N) = cNil [owise] .
endfm

fmod NKMEM is
    protecting MEM .
    sorts WMask RMask .
    sort Proc .
    sort Comp .
    op makeProc : WMask RMask -> Proc .
    --- op makeComp : Mem 
endfm
```

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
