# Overview #

This repository contains mechanizations of different semantics for [monotonic
references](https://doi.org/10.1007/978-3-662-46669-8_18) to enable efficient
gradual typing. To handle correctness in the case of cyclic casts for structural
types, monotonic references write cast expressions to the heap that is reduced
using a small-step reduction relation where intermediate redexes are also
written to the heap. Another approach is to write values only to the heap and
maintain a queue of casts on addresses. We mechanize both approaches, both with
simple coercions and with space-efficient coercions.

# Getting Started

You will need to have the following dependencies installed:

  - [Agda](https://agda.readthedocs.io/en/v2.5.4.2/getting-started/installation.html)
  - [Agda standard library](https://github.com/agda/agda-stdlib/tree/5819a4dd9c965296224944f05b1481805649bdc2)
  - [Agda standard library++](https://github.com/deyaaeldeen/stdlib-plusplus.agda/tree/0d468ea0187ca70c49dc8721501622a9fc180f5a)
  
Agda standard library++ is part of the [Metaborg](https://metaborg.github.io/) project and is used in the work presented by POPL'18 paper [Intrinsically-Typed Interpreters for Imperative Languages](https://dl.acm.org/citation.cfm?id=3158104). I maintain a fork to work with the latest version of Agda standard library, which can be installed by executing `make lib`.

# Mechanizations

- [Simple Semantics With Evolving Stores](MonoRef/Dynamics/Simple/EvStore/TypeSafety.agda): Type safety proof for a space-inefficient variation of monotonic references with evolving stores. Type preservation is proved by construction for [all reduction rules](MonoRef/Dynamics/Simple/EvStore/Reduction.agda). On the other hand, the progress proof consists of two parts, [progress proof for when the store contains values only](MonoRef/Dynamics/Simple/EvStore/NormalStoreProgress.agda) and [one for when there is at least one delayed cast expression that is not a value](MonoRef/Dynamics/Simple/EvStore/EvolvingStoreProgress.agda).

- [Efficient Semantics With Evolving Stores](MonoRef/Dynamics/Efficient/EvStore/TypeSafety.agda): Type safety proof for a space-efficient variation of monotonic references. To establish space efficiency, a [normal form grammar for coercions](MonoRef/Coercions/NormalForm/Plain/Syntax.agda) is defined along with a [composition operator](MonoRef/Coercions/NormalForm/Plain/Compose.agda). The termination of composition is also established by reasoning about the sizes of coercions in each case. A [height bound](MonoRef/Coercions/NormalForm/Plain/Height.agda) on coercion creation and composition is also provided. [Type preservation](MonoRef/Dynamics/Efficient/EvStore/Reduction.agda) and progress for both cases of [a normal store](MonoRef/Dynamics/Efficient/EvStore/NormalStoreProgress.agda) and [evolving store](MonoRef/Dynamics/Efficient/EvStore/EvolvingStoreProgress.agda) are proved.

- Simple Semantics With A Queue: A space-inefficient variation of monotonic references with a queue on the side. Type preservation is proved by construction for [all reduction rules](MonoRef/Dynamics/Simple/StdStore/Reduction.agda). On the other hand, the progress proof consists of two parts, [progress proof for when the queue is empty](MonoRef/Dynamics/Simple/StdStore/NormalStoreProgress.agda) and [one for when the queue is not empty](MonoRef/Dynamics/Simple/StdStore/SuspendedCastProgress.agda).

- Efficient Semantics With A Queue: A space-efficient variation of monotonic references with a queue on the side. Coercions are the same as the ones in the efficient semantics with evolving stores. [Type preservation](MonoRef/Dynamics/Efficient/StdStore/Reduction.agda) and progress for both cases of [an empty queue](MonoRef/Dynamics/Efficient/StdStore/NormalStoreProgress.agda) and [not an empty queue](MonoRef/Dynamics/Efficient/StdStore/SuspendedCastProgress.agda) are proved.
