---
title: Memory Model
author: Everett Hildenbrandt
geometry: margin=2.5cm
execute: memory-model.maude
format: latex
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

Normal FPGAs (Field Programmable Gate Arrays), on the other hand, are
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

Addresses and Cells
-------------------

The basic parts of memory are addresses and cells. They have a very simple
initial algebra - addresses can be composed (with `_._`) and cells can be held
next to each other (with `_|_`).

```maude{exec:memory-model.maude}
set include BOOL off .

fmod ADDR is
    sort Addr .

    op aNil : -> Addr [ctor] .
    op _._ : Addr Addr -> Addr [gather (e E)] .
    -------------------------------------------
endfm

fmod CELL is
    sort Cell .

    op cNil : -> Cell [ctor] .
    op _|_ : Cell Cell -> Cell [ctor assoc comm id: cNil] .
    -------------------------------------------------------
endfm
```

When creating your specific type of address or cell, make them a subsort of the
sorts `Addr` and `Cell` respectively. Some example address and cell
implementations are given here.

### Natural Number Cells

We can start with cells which are isomorphic to the natural numbers. A new sort
`NatCell` is declared as a subsort of `Cell` (so that the operations available
to generic `Cell`s are available here). Each one of these could be one "word" or
"byte" in computer memory.

```maude{exec:memory-model.maude}
fmod NAT-CELL is
    protecting CELL .

    sort NatCell .
    subsort NatCell < Cell .

    op 0 : -> NatCell [ctor] .
    op c : NatCell -> NatCell [ctor iter] .
    ---------------------------------------
endfm
```

Real memory isn't unbounded like the natural numbers. By importing
`BOUNDED-NAT-CELL` instead of `NAT-CELL`, we can specify the wrap-around point
of the naturals we use. Below I've supplied a 64-bit `NatCell` implementation.

```maude{exec:memory-model.maude}
fmod BOUNDED-NAT-CELL is
    including NAT-CELL .

    eq c^18446744073709551616(0) = 0 .      --- 64 bit wrap-around
endfm
```

### Natural Number Addresses

The first functionality we can add to normal addresses is comparability. This
can assist with data-structure traversals and usage. For this, we create a new
sort `CompAddr` and make it a sub-sort of `Addr`, as well as defining the
operations `_<_` and `_<=_` for `CompAddr`.

```maude{exec:memory-model.maude}
fmod COMP-ADDR is
    protecting ADDR .
    protecting BOOL .

    sort CompAddr .
    subsort CompAddr < Addr .

    vars A1 A2 : CompAddr .

    op _<_ : CompAddr CompAddr -> Bool .
    op _<=_ : CompAddr CompAddr -> Bool .
    -------------------------------------
    eq A1 < A1  = false .
    eq A1 <= A2 = (A1 == A2) or A1 < A2 .
endfm
```

Here I've implemented natural-number addresses. These are made a sub-sort of
`CompAddr`, with `_<_` defined appropriately. I've also provided
`BOUNDED-NAT-ADDR` if you want to use more realistic bounded natural numbers.

```maude{exec:memory-model.maude}
fmod NAT-ADDR is
    protecting COMP-ADDR .

    sort NatAddr .
    subsort NatAddr < CompAddr .

    vars A1 A2 : NatAddr .

    op 0 : -> NatAddr [ctor] .
    op a : NatAddr -> NatAddr [ctor iter] .
    ---------------------------------------
    eq a(A1) < a(A2)    = A1 < A2 .
    eq 0 < a(A2)        = true .
    eq a(A1) < 0        = false .
endfm

fmod BOUNDED-NAT-ADDR is
    including NAT-ADDR .

    eq a^18446744073709551616(0) = 0 .      --- 64 bit wrap-around
endfm
```

Memory
------

Memory is a pointer from addresses to cells (`_->_`). The result can be treated
as a new cell - thus memory structures can be nested arbitrarily.

For every type of memory, you must provide the definitions of the operators
`_@_` (lookup) and `_*_` (update). The default ones can handle addresses which
are only comparable with equality. If you want to use comparable addresses (with
the `_<_` operator), for example, you'll have to define how that operator
affects the memory lookup (`_@_`) and update (`_*_`) operators.

```maude{exec:memory-model.maude}
fmod MEM is
    protecting ADDR .
    protecting CELL .

    vars A A' A1 A2 : Addr .
    vars C C' C1 C2 : Cell .

    op _->_ : Addr Cell -> Cell [ctor] .
    ------------------------------------
    eq (A2 . A1) -> C           = A1 -> (A2 -> C) .

    op _@_ : Cell Addr -> Cell [gather (e E)] .
    -------------------------------------------
    eq ((A1 -> C1) | C) @ A1    = C1 .
    eq C @ (A2 . A1)            = (C @ A1) @ A2 .
    eq C @ A                    = cNil [owise] .

    op _*_ : Cell Cell -> Cell [gather (E e)] .
    -------------------------------------------
    eq C * cNil                 = C .
    eq cNil * C                 = C .
    eq ((A1 -> C1) | C) * ((A1 -> C2) | C')
                                = ((A1 -> (C1 * C2)) | C) * C' .
    eq C * ((A2 -> C2) | C')    = ((A2 -> C2) | C) * C' [owise] .
    eq C * C'                   = C' [owise] .
endfm
```

### Bounded Naturals Memory

To now make a memory where the cells and addresses are bounded natural numbers,
we just have to import the `MEM` module, along with the `BOUNDED-NAT-ADDR` and
`BOUNDED-NAT-CELL` modules.

```maude{exec:memory-model.maude}
fmod BOUNDED-NAT-MEM is
    protecting MEM .
    protecting BOUNDED-NAT-ADDR .
    protecting BOUNDED-NAT-CELL .
endfm
```

### Bounded Naturals Binary Tree

Suppose we want a more complex data-structure. Here I've implemented a sample
binary tree (`BOUNDED-NAT-BTREE-MEM`). I've imported `BOUNDED-NAT-MEM` so we're
working with bounded naturals as the keys and values.

I've also added new sorts `BTreeKey` and `BTreeField`. `BTreeKey` is used as an
address with the current node's key, which here I've specified is `NatAddr`
(with the `btree : NatAddr -> BTreeKey` operator). Notice that `BTreeKey` is a
subsort of `CompAddr`, which means that whatever you pick as `BTreeKey` must
have the `_<_` defined for it.

`BTreeField` is a subsort of `Addr`, meaning there are no restrictions on the
type of addresses that can be used for `BTreeField`. Here I supply three
`BTreeField` constructors: `v` for "value", `l` for "low", and `h` for "high".
Thus, when performing a query for some `BTreeKey`, if it's equal to the key of
the current node then the value can be returned by using `v`. If it's lower,
then the lower branch of the binary tree can be accessed with `l` - similarly
for `h` as well.

```maude{exec:memory-model.maude}
fmod BOUNDED-NAT-BTREE-MEM is
    protecting BOUNDED-NAT-MEM .

    sorts BTreeKey BTreeField .
    subsort BTreeKey < CompAddr .
    subsort BTreeField < Addr .

    vars A1 A2 : CompAddr .
    var C C1 C2 : Cell .
    vars K K' : BTreeKey .
    var F : BTreeField .

    op btree : NatAddr -> BTreeKey [ctor] .
    ---------------------------------------
    eq btree(A1) < btree(A2) = A1 < A2 .

    ops v l h : -> BTreeField [ctor] .
    ----------------------------------

    --- op _@_ : Cell Addr -> Cell .
    ceq (K' -> C1) @ K          = C1 @ (K . l)                      if K < K' .
    ceq (K' -> C1) @ K          = C1 @ (K . h)                      if K' < K .
    --- op _*_ : Cell Cell -> Cell .
    ceq (K' -> C1) * (K -> C2)  = (K' -> (C1 * ((K . l) -> C2)))    if K < K' .
    ceq (K' -> C1) * (K -> C2)  = (K' -> (C1 * ((K . h) -> C2)))    if K' < K .
endfm
```


Testing
=======

I provide a module `BOUNDED-NAT-BTREE-MEM-TEST` here for demonstration purposes.

```maude{exec:memory-model.maude}
fmod BOUNDED-NAT-BTREE-MEM-TEST is
    protecting BOUNDED-NAT-BTREE-MEM .

    op initialBTree : -> Cell .
    ---------------------------
    eq initialBTree = (btree(a^3(0)) -> (v -> c^6(0)))
                        * (btree(a^2(0)) -> (v -> c^10(0)))
                        * (btree(a^13(0)) -> (v -> c^26(0)))
                        * (btree(a^7(0)) -> (v -> c^24(0))) .
endfm
```

The term `initialBTree` starts off by inserting the elements `3 -> 6`, `2 ->
10`, `13 -> 26`, and `7 -> 24` (`key -> value`) into an empty binary tree (in
that order). So the resulting binary tree should have `3` at the root, with `2`
as a left child, `13` as a right child, and `7` as a left child of `13`.

We would expect that accessing the elements defined here would return the
correct value - demonstrated below:

```maude{exec:memory-model.maude}
reduce initialBTree @ (v . btree(a^3(0))) .
reduce initialBTree @ (v . btree(a^2(0))) .
reduce initialBTree @ (v . btree(a^13(0))) .
reduce initialBTree @ (v . btree(a^7(0))) .
```

which results in the expected output below:

```maude
==========================================
reduce in BOUNDED-NAT-BTREE-MEM-TEST : initialBTree @ v . btree(a^3(0)) .
rewrites: 53 in 0ms cpu (0ms real) (~ rewrites/second)
result NatCell: c^6((0).NatCell)
==========================================
reduce in BOUNDED-NAT-BTREE-MEM-TEST : initialBTree @ v . btree(a^2(0)) .
rewrites: 60 in 0ms cpu (0ms real) (~ rewrites/second)
result NatCell: c^10((0).NatCell)
==========================================
reduce in BOUNDED-NAT-BTREE-MEM-TEST : initialBTree @ v . btree(a^13(0)) .
rewrites: 66 in 0ms cpu (0ms real) (~ rewrites/second)
result NatCell: c^26((0).NatCell)
==========================================
reduce in BOUNDED-NAT-BTREE-MEM-TEST : initialBTree @ v . btree(a^7(0)) .
rewrites: 78 in 0ms cpu (0ms real) (~ rewrites/second)
result NatCell: c^24((0).NatCell)
```

We would also like to verify that updating one of the keys with a new value,
then accessing that key again would reflect the update value. An example is
shown below:

```maude{exec:memory-model.maude}
reduce (initialBTree * (btree(a^13(0)) -> (v -> c^100(0)))) @ (v . btree(a^13(0))) .
```

which results in the expected output:

```maude
==========================================
reduce in BOUNDED-NAT-BTREE-MEM-TEST : (initialBTree * (btree(a^13(0)) -> v ->
c^100(0))) @ v . btree(a^13(0)) .
rewrites: 85 in 1ms cpu (0ms real) (85000 rewrites/second)
result NatCell: c^100((0).NatCell)
```


Future Work
===========

The current memory model is better for the level of abstraction it provides than
previous versions, though it has moved further from something directly
implementable in hardware. It would be nice to isolate exacly which bits of the
memory model need to be compiled down to FPGA logic. I suspect that only the
equations which simplify out the lookup and update operators (`_@_` and `_*_`
respectively) would be necessary to implement as FPGA logic - this would allow
our memory (RAM) to export very simple functions for lookup and query on
arbitrary datastructures.

For example, we can use the same lookup and update operators on a flat memory
region (`BOUNDED-NAT-MEM`), or on a binary tree (`BOUNDED-NAT-BTREE-MEM`), and
the equational simplification rules just "do the right thing" based on the
underlying datastructure. By putting these equational simplification rules in
FPGA logic, our CPUs can issue generic lookup and update commands to the memory
and the memory will just "do the right thing" under the hood, allowing for
datastructure implementation details to be forgotten by the CPU.

I also haven't had the time to implement basic memory permissions and
segmentation using this memory model. In previous versions (see the [github
page](https://github.com/nested-kernel/veri-funky)) I have implemented
permissions and memory bounding. They boil down to a new type of address which
restricts the reads and writes that make it to the underlying `Cell`. I hope to
implement something like the Nested Kernel memory model[@nestedkernel], which
would allow for RAM hooked up to an FPGA to act like the ideal MMU (memory
management unit) that the Nested Kernel expects.

Once I have more primitive memory address types specified, it would also be nice
to do some verification of the memory model. Most of it will be "correct by
construction", which means that verification boils down to inductive proofs that
the construction was actually correct. I also suspect that what I've written
here acts a lot like the Haskell notion of a "lens". Haskell lenses (and prisms)
have very nice composability properties, so if I could prove that what I have
here is a lens or a prism then I can use all the existing math of lenses and
prisms. Perhaps this can also be used to inspire more general lookup and update
operations as well.


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
