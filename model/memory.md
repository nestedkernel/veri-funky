---
title: Memory Model
author: Everett Hildenbrandt
subtitle: Jose Meseguer
geometry: margin=2.5cm
execute: memory-model.maude
...


Introduction
============

Memory is a ubiqitous part of compute hardware. Most (if not all) computation is
centered around manipulating memory. Everything about a computer's state has to
be stored in memory somewhere.

Most programming is done in programming languages that make it hard to reason
about memory - informal sequential concurrent programs focus on a list of
instructions to feed the machine and hope its state is correct afterwards. This
problem runs all the way down to hardware; assembly languages are hard to
understand because hardware is hard to understand. We are writing for the
machines, not for ourselves.

### Formal Description of Memory

Many formal languages eschwew this idea and embrace high-level abstractions.
Those abstractions are then translated into hard-to-reason about code which we
hope performs as expected.

To help this cause, we need formal "assembly-like" languages. Fortunately, to
begin, we don't actually have to make a formal assembly. We can instead compile
some formal language into a subset of some informal hardware language; then
formalize the informal language in the formal one.

To formalize the informal language, we'll need a model of memory. Then we define
the operational semantics of the informal language in terms of that memory
model, allowing us to reason about the language itself.

### Hardware Inspiration

If a memory model also happened to mimic closely what happened at the hardware
level, it could actually serve as an assembly for that hardware. Then we
wouldn't compile formal languages to informal ones to run them - instead we
would use the defined operational semantics of the informal ones as a compiler
to our "memory" assembly. Our hardware is making it hard to reason about memory;
CPUs are large complicated things with lots of inherent non-determinism.

Normal CFPGAs (Field Programmable Gate Arrays), on the other hand, are
comparatively simple to reason about. In the simplest case, we can think of them
as lots of configurable LUTs (lookup tables), which are functions in the set
`[BitVect{X} -> BitVect{X}]` (with `X` a bit width). We can select which
particular function each is, and how they are hooked up to each other.

With some careful planning, we could add a layer of FPGA logic between our
hard-to-reason-about CPUs and our memory. The FPGA could perform many of the
common datastructure operations in memory for us - things like balancing trees
and multiplying matrices. The CPU could make higher-level requests of the memory
leveraging that layer of logic[^BlueDBM]. FPGAs also have the added benefit of
being power efficient and fast at many highly-parallel algorithms.

[^BlueDBM]: Some projects (like BlueDBM[@bluedbm]) have shown that representing
    much of the database queries in FPGA logic is possible. As a lot of
    computing boils down to database queries, I think this is promising work.

### Proposal

I have tried to make a memory model which is both formal and mimics hardware a
bit. To make it formal, I'm simply making the model in Maude. Mimicking hardware
is a bit harder though, any "Maude magic" I use makes the hardware I use have to
be able to do that. My basic idea is that anything in the equational subset of
Maude should be implementable in FPGAs, rewriting may be harder.


Implementation
==============

### `Cell`s

We start with the basic unit of memory - a `Cell`. A `Cell` is a map from
addresses to values. The addresses of sort `Addr` and the values of sort `Cell`
are both supersorts of `Nat`. This is a convenience, and does not affect much
about how they behave; though as the memory model gets more concrete they should
be switched to `MachineInt`s.

`Cell`s also grow as large as you want, it's up to higher levels of the
description to make sure they don't do so in an unrealistic manner. This is
another convenience. `Cell`s maps can be updated.

```maude
fmod ADDR is
    protecting BOOL .
    protecting NAT .

    sort Addr AddrDomain .
    subsort Nat < Addr < AddrDomain .

    op noNum : -> Addr [ctor] .
    ---------------------------

    var N : Nat .
    vars A B : Addr .

    op min : Addr Addr -> Addr [ditto] .
    op max : Addr Addr -> Addr [ditto] .
    ------------------------------------
    eq min(noNum, A) = noNum .
    eq max(noNum, A) = noNum .

    vars E S : Nat .

    op (_,_) : Addr Addr -> AddrDomain [ctor] .
    -------------------------------------------
    eq (noNum,E)        = noNum .
    eq (S,noNum)        = noNum .
    ceq (S,E)           = noNum if E <= S .

    op _u_ : AddrDomain AddrDomain -> AddrDomain [ctor assoc comm id: noNum] .
    --------------------------------------------------------------------------
    eq E u (S,E)            = (S, s(E)) .
    ceq S u (S1,E1)         = (S1,E1)               if S1 <= S /\ S < E1 .
    ceq (S1,E1) u (S2,E2)   = (S1, max(E1,E2))      if S1 <= S2 /\ S2 <= E1 .

    vars E1 E2 S1 S2 : Nat .
    vars AD1 AD2 AD3 : AddrDomain .

    op valid : AddrDomain -> Bool .
    -------------------------------
    eq valid (noNum)        = false .
    eq valid (S)            = true .
    eq valid (S, E)         = S < E .
    eq valid (AD1 u AD2)    = valid (AD1) and valid (AD2) .

    op _\_ : AddrDomain AddrDomain -> AddrDomain .
    ----------------------------------------------
    ---eq noNum \ AD1          = noNum .
    ---eq AD1 \ noNum          = AD1 .
    eq AD1 \ ((S,E) u AD3)  = (AD1 \ (S,E)) \ AD3 .
    eq ((S,E) u AD2) \ AD3  = ((S,E) \ AD3) u (AD2 \ AD3) .
    ceq S1 \ S2             = noNum                 if S1 == S2 .
    ceq S1 \ S2             = S1                    if S1 =/= S2 .
    ceq (S1,E1) \ (S2,E2)   = (S1, min(E1,S2))      if valid(S2,E2) and S1 <= S2 .
    ceq (S1,E1) \ (S2,E2)   = (max(S1,s(E2)), E1)   if valid(S2,E2) and S2 <= S1 .
    ceq S \ (S2,E2)         = S                     if valid(S2,E2) and (S < S2 or E2 <= S) .
    ceq S \ (S2,E2)         = noNum                 if valid(S2,E2) and (S2 <= S and S < E2) .
    ceq (S1,E1) \ S         = (S1,S) u (s(S), E1)   if S1 <= S and S < E1 .
    ceq (S1,E1) \ S         = (S1,E1)               if S < S1 or E1 <= S .

    op isect : AddrDomain AddrDomain -> AddrDomain [comm] .
    -------------------------------------------------------
    eq isect (AD1, AD2)     = AD1 \ (AD1 \ AD2) .

    op sdiff : AddrDomain AddrDomain -> AddrDomain [comm] .
    -------------------------------------------------------
    eq sdiff (AD1, AD2)     = (AD1 u AD2) \ isect(AD1, AD2) .

    op _in_ : AddrDomain AddrDomain -> Bool .
    -----------------------------------------
    eq AD1 in AD2 = (AD1 \ AD2) == noNum .
endfm
```

### Memory Segmentation

Operating systems need to isolate memory between different components of
computers. To do this, we'll need some way to describe ranges of memory. Here we
have `ADDR-RANGE`, which will be used to act as a restriction on the domains of
higher-level memory operations.

The sort `AddrDomain` is added. It represents a set of `Addr` which can be used
by a process. `AddrDomain`s can be added and subtracted (with the normal notions
of set addition and subtraction) with the operators `|` (addition) and `|-`
(subtraction). From these definitions follows the `intersect` and `sd`
(symmetric differenc) operations.

```maude
fmod CELL is
    protecting NAT .

    sorts Addr Val .
    subsorts Nat < Addr Val .
    sort Cell .

    var A : Addr .
    vars V V1 V2 : Val .
    vars C C1 C2 : Cell .

    op noVal : -> Val [ctor] .
    op noAddr : -> Addr [ctor] .
    ----------------------------

    op cNil : -> Cell [ctor] .
    op _->_ : Addr Val -> Cell [ctor] .
    op _|_ : Cell Cell -> Cell [ctor assoc comm id: cNil] .
    -------------------------------------------------------
    eq A -> noVal = cNil .
    eq noAddr -> V = cNil .

    op _@_ : Cell Addr -> Val .
    ---------------------------
    eq ((A -> V) | C) @ A   = V .
    eq C @ A                = noVal [owise] .

    op _*_ : Cell Cell -> Cell [gather (E e)].
    ------------------------------------------
    eq ((A -> V1) | C1) * ((A -> V2) | C2)  = ((A -> V2) | C1) * C2 .
    eq C1 * C2                              = C1 | C2 [owise] .
endfm
```

```maude{exec:memory-model.maude}
set include BOOL off .

fmod MEM is
    sort AddrMap .
    sort Mem .

    vars AM AM1 AM2 AM3 : AddrMap .
    vars M M' M1 M2 : Mem .

    op aNil : -> AddrMap [ctor] .
    op aID : -> AddrMap [ctor] .
    op _._ : AddrMap AddrMap -> AddrMap [gather (e E)] .
    ----------------------------------------------------

    op mNil : -> Mem [ctor] .
    op _|_ : Mem Mem -> Mem [ctor assoc comm id: mNil] .
    ----------------------------------------------------

    op _->_ : AddrMap Mem -> Mem [ctor] .
    -------------------------------------
    eq (AM1 . AM2) -> M1                = AM2 -> (AM1 -> M1) .

    op _@_ : Mem AddrMap -> Mem .
    -----------------------------
    eq ((AM1 -> M1) | M) @ AM1          = M1 .
    eq ((AM1 -> M1) | M) @ (AM3 . AM2)  = ((AM1 -> M1) | M) @ AM2 @ AM3 .
    eq M @ AM                           = mNil [owise] .

    op _*_ : Mem Mem -> Mem [gather (E e) id: mNil] .
    -------------------------------------------------
    eq ((AM1 -> M1) | M) * ((AM1 -> M2) | M')
                                = ((AM1 -> M2) | M) * M' .
    eq ((AM1 -> M1) | M) * ((AM2 -> M2) | M')
                                = ((AM2 -> M2) | (AM1 -> M1) | M) * M' [owise] .
endfm

fmod CELL is
    protecting MEM .

    sort Cell .
    subsort Cell < Mem .

    op mNil : -> Cell [ctor ditto] .
    op 0 : -> Cell [ctor] .
    op c : Cell -> Cell [ctor iter] .
endfm

fmod COMP-ADDR is
    protecting MEM .
    protecting BOOL .

    sort CompAddr .
    subsort CompAddr < AddrMap .

    vars A1 A2 : CompAddr .

    op aNil : -> CompAddr [ctor ditto] .
    ------------------------------------

    op _<_ : CompAddr CompAddr -> Bool .
    op _<=_ : CompAddr CompAddr -> Bool .
    -------------------------------------
    eq aNil < A2    = false .
    eq A1 < aNil    = false .
    eq A1 < A1      = false .
    eq A1 <= A2     = (A1 == A2) or A1 < A2 .
endfm

fmod NAT-ADDR is
    protecting COMP-ADDR .

    sort NatAddr .
    subsort NatAddr < CompAddr .

    vars A1 A2 : NatAddr .

    op aNil : -> NatAddr [ctor ditto] .
    op 0 : -> NatAddr [ctor] .
    op a : NatAddr -> NatAddr [ctor iter] .
    ---------------------------------------
    eq a(A1) < a(A2)    = A1 < A2 .
    eq 0 < a(A2)        = true .
    eq a(A1) < 0        = false .
endfm

fmod BTREE-CELL is
    protecting CELL .
    protecting NAT-ADDR .

    sorts BTreeField BTreeKey .
    subsort BTreeField < AddrMap .
    subsort BTreeKey < CompAddr .

    vars A1 A2 : CompAddr .
    var M1 M2 : Mem .
    vars K K' : BTreeKey .
    var F : BTreeField .

    op btree : NatAddr -> BTreeKey [ctor] .
    ops v l h : -> BTreeField [ctor] .

    eq btree(A1) < btree(A2) = A1 < A2 .

    ceq (K' -> M1) @ K          = M1 @ (K . l)                      if K < K' .
    ceq (K' -> M1) @ K          = M1 @ (K . h)                      if K' < K .
    ceq (K' -> M1) * (K -> M2)  = (K' -> (M1 * ((K . l) -> M2)))    if K < K' .
    ceq (K' -> M1) * (K -> M2)  = (K' -> (M1 * ((K . h) -> M2)))    if K' < K .
endfm
```

```maude
fmod BOUNDED-MEM is
    extending MEM .

    sort AddrComp .
    subsorts Addr < AddrComp < AddrMap .

    vars A AS AE : AddrComp .

    op bounded : AddrComp AddrComp -> AddrMap [ctor] .
    --------------------------------------------------
    ceq bounded(AS, AE) @ A = A if AS <= A and A < AE .
    ceq bounded(AS, AE) @ A = noAddr if A < AS or AE <= A .
endfm
```

```maude
--- set include off .
---
---
--- fmod CELL is
--- ---- ====
---     sort Cell .
---
---     op 0 : -> Addr [ctor] .
---     op s : Addr -> Addr [ctor iter] .
---     ---------------------------------
---     eq s^18446744073709551616(0) = 0 .
--- endfm


fmod MEM is
---- ===
    protecting NAT .
    protecting BOOL .

    sorts Addr Val .
    subsorts Nat < Addr Val .
    sorts Mem MemType .

    op noVal : -> Val [ctor] .
    --------------------------

    op mNil : -> Mem [ctor] .
    op _|=>_ : Addr Val -> Mem [ctor] .
    op _|_ : Mem Mem -> Mem [ctor assoc comm id: mNil] .
    ----------------------------------------------------

    var A : Addr .
    vars V V1 V2 : Val .
    vars M M' M1 M2 : Mem .

    op _@_ : Mem Addr -> Val [gather (E e)] .
    -----------------------------------------
    eq ((A |=> V) | M) @ A  = A .
    eq M @ A                = noVal [owise] .

    op _*_ : Mem Mem -> Mem [gather (E e)] .
    ----------------------------------------
    eq ((A |=> V1) | M1) * ((A |=> V2) | M2)
                            = ((A |=> V2) | M1) * M2 .
    eq (M | M1) * (M' | M2) = M | M1 | M' | M2 [owise] .

    op _\_ : Mem Addr -> Mem [gather (E e)] .
    -----------------------------------------
    eq ((A |=> V) | M) \ A  = M .
    eq (M | M1) \ A         = M | M1 [owise] .

    op set? : Mem Addr -> Bool .
    op unset? : Mem Addr -> Bool .
    ------------------------------
    eq set? (M, A)          = (M @ A) =/= noVal .
    eq unset? (M, A)        = (M @ A) == noVal .
endfm

fmod MEM-BOUNDED is
---- ===========
    extending MEM .

    var V : Val .
    vars K A1 A2 : Addr .
    vars M M' : Mem .

    op bounded : Addr Addr -> MemType [ctor] .
    ------------------------------------------

    op _in(_,_) : Addr Addr Addr -> Bool .
    op _notin(_,_) : Addr Addr Addr -> Bool .
    -----------------------------------------
    eq K in(A1, A2)             = A1 <= K and K < A2 .
    eq K notin(A1, A2)          = not (K in(A1, A2)) .

    ceq M : bounded(A1, A2) @ K = M @ K
                                if K in(A1, A2) .
    ceq M : bounded(A1, A2) @ K = noVal
                                if K notin(A1, A2) .
    ceq M : bounded(A1, A2) * ((K |=> V) | M')
                                = (M * (K |=> V)) : bounded(A1, A2) * M'
                                if K in(A1, A2) .
    ceq M : bounded(A1, A2) * ((K |=> V) | M')
                                = M : bounded(A1, A2) * M'
                                if K notin(A1, A2) .
endfm

fmod BTREE is
    extending MEM .

    var V : Val .
    vars A K : Addr .
    vars M M' : Mem .

    op btree : Addr -> MemType [ctor] .
    -----------------------------------

    op nextAddr : Mem -> Addr .
    ---------------------------
    ceq nextAddr (M : btree(A)) = A if unset?(M, A) .
    ceq nextAddr (M : btree(A)) = nextAddr (M : btree(A + 4)) if set?(M, A) .

    op newEntry : Addr Addr Val -> Mem .
    ------------------------------------
    eq newEntry(A, K, V) = (A |=> K) * (A + 1 |=> V) .

    ceq M : btree(A) @ K    = M @ s(A)
                            if (M @ A) == K .
    ceq M : btree(A) @ K    = M : btree(M @ (A + 2)) @ K
                            if K < (M @ A) and set?(M, A + 2) .
    ceq M : btree(A) @ K    = M : btree(M @ (A + 3)) @ K
                            if (M @ A) < K and set?(M, A + 3) .

    ceq M : btree(A) * ((K |=> V) | M')
                            = (M \ A + 2 \ A + 3)
                                * (A |=> K) * (A + 1 |=> V) : btree(0) * M'
                            if unset?(M, A) .

    ceq M : btree(A) * ((K |=> V) | M')
                            = M * (A + 1 |=> V) : btree(0) * M'
                            if (M @ A) == K .

    ceq M : btree(A) * ((K |=> V) | M')
                            = M  : btree(M @ (A + 2)) * ((K |=> V) | M')
                            if K < (M @ A) and set?(M, A + 2) .

    ceq M : btree(A) * ((K |=> V) | M')
                            = M : btree((M @ (A + 3))) * ((K |=> V) | M')
                            if (M @ A) < K and set?(M, A + 3) .

    ceq M : btree(A) * ((K |=> V) | M')
                            = M * (A + 2 |=> nextAddr(M : btree(0))) : btree(A)
                                * ((K |=> V) | M')
                            if K < (M @ A) and unset?(M, A + 2) .

    ceq M : btree(A) * ((K |=> V) | M')
                            = M * (A + 3 |=> nextAddr(M : btree(0))) : btree(A)
                                * ((K |=> V) | M')
                            if (M @ A) < K and unset?(M, A + 3) .
endfm

fmod STRUCT is
    extending MEM .


endfm

fmod BTREE-ELEMS is
    protecting BTREE .

    op btree-elem : Addr Addr Addr -> MemType [ctor] .
    --------------------------------------------------

    
endfm
```

### Memory Typing

Operating systems (and programs) don't want to just segment memory (which is
what permissions try for). They also want to type it - many programming
languages have untyped memory models. Introducing a flexible type system at a
low level makes it easier to build up layers of abstractions quickly.

I use a new sort `MemType` to store information about the memory. `MemType` can
be a basic type (declared as a constant operator of that sort), or as the union
of other `MemType`s. Right now I'm only implementing some basic permissions
using this. Later we could even have something like a `balanced-btree` type,
which would serve as an instruction to an FPGA that it should implement certain
functions (like tree rotations, insertions, etc...) in hardware, allowing the
CPU to use higher-level acces and manipulation commands.

We could also (though I have not done it yet) implement generic order-typed
memory - making our memory look more like an order-sorted algebra. In addition
to having equations for type equality, we could have t


References
==========

---
csl: ieee.csl
references:
-   id: nestedkernel
    type: article-journal
    author:
    -   family: Dautenhahn
        given: Nathan
    issued:
    -   year: 2015
    title: 'Nested kernel: An operating system architecture for intra-kernel
            privilege separation'
    title-short: Nested kernel
-   id: bluedbm
    type: article-journal
    author:
    -   family: Jun
        given: Sang-Woo
    -   family: Liu
        given: Ming
    -   family: Lee
        given: Sungjin
    -   family: Hicks
        given: Jamey
    -   family: Ankcorn
        given: John
    -   family: King
        given: Myron
    -   family: Xu
        given: Shuotao
    -   family: Arvind
    issued:
    -   year: 2015
    title: 'BlueDBM: An Appliance for Big Data Analytics'
-   id: rop-gadgets
    type: article-journal
    author:
    -   family: Roemer
        given: Ryan
    -   family: Buchanan
        given: Erik
    -   family: Shacham
        given: Hovav
    -   family: Savage
        given: Stefan
    issued:
    -   year: 2012
    title: 'Return-Oriented Programming: Systems, Languages, and Applications'
...
