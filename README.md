# Overview #

This repository contains mechanizations of different semantics for [monotonic
references](https://doi.org/10.1007/978-3-662-46669-8_18) to enable efficient
gradual typing.

# Getting Started

You will need to have the following dependencies installed:

  - [Agda](https://agda.readthedocs.io/en/v2.5.4.2/getting-started/installation.html)
  - [Agda standard library](https://github.com/agda/agda-stdlib/tree/5819a4dd9c965296224944f05b1481805649bdc2)
  - [Agda standard library++](https://github.com/deyaaeldeen/stdlib-plusplus.agda/tree/0d468ea0187ca70c49dc8721501622a9fc180f5a)
  
Agda standard library++ is part of the [Metaborg](https://metaborg.github.io/) project and is used in the work presented by POPL'18 paper [Intrinsically-Typed Interpreters for Imperative Languages](https://dl.acm.org/citation.cfm?id=3158104). I maintain a fork to work with the latest version of Agda standard library, which can be installed by executing `make lib`.

# Mechanizations

- [Simple Semantics](MonoRef/Dynamics/Simple/TypeSafety.agda): Type safety proof for a space-inefficient variation of monotonic references. Type preservation is proved by construction for [all reduction rules](MonoRef/Dynamics/Simple/Reduction.agda). On the other hand, the progress proof consists of two parts, [progress proof for when there is no strong casted values in the store](MonoRef/Dynamics/Simple/NormalStoreProgress.agda) and [one for when there is at least one](MonoRef/Dynamics/Simple/EvolvingStoreProgress.agda). To establish the latter, we need to reason about some notion of [progress for the store](MonoRef/Dynamics/Simple/StoreProgress.agda).

- [Efficient Forgetful Semantics](MonoRef/Dynamics/Efficient/Forgetful/TypeSafety.agda): Type safety proof for a space-efficient variation of monotonic references. It is forgetful because the composition of two reference coercions forgets about the first coercion and just returns the second. To establish space efficiency, a [normal form grammar for coercions](MonoRef/Coercions/NormalForm/Syntax.agda) is defined along with a [composition operator](MonoRef/Coercions/NormalForm/Compose.agda). The termination of composition is also established by reasoning about the sizes of coercions in each case. [Type preservation](MonoRef/Dynamics/Efficient/Forgetful/Reduction.agda) and progress for both cases of [a normal store](MonoRef/Dynamics/Efficient/Forgetful/NormalStoreProgress.agda) and [evolving store](MonoRef/Dynamics/Efficient/Forgetful/EvolvingStoreProgress.agda) are proved.

- [Efficient Faithful Semantics](MonoRef/Dynamics/Efficient/Faithful/TypeSafety.agda): Type safety proof for a space-efficient variation of monotonic references. It is faithful because the composition of two reference coercions creates a new one with the greatest lower bound of the inputs' types. To establish space efficiency, a [normal form grammar for coercions](MonoRef/Coercions/NormalForm/Syntax.agda) is defined along with a [composition operator](MonoRef/Coercions/NormalForm/Compose.agda). The termination of composition is also established by reasoning about the sizes of coercions in each case. [Type preservation](MonoRef/Dynamics/Efficient/Faithful/Reduction.agda) and progress for both cases of [a normal store](MonoRef/Dynamics/Efficient/Faithful/NormalStoreProgress.agda) and [evolving store](MonoRef/Dynamics/Efficient/Faithful/EvolvingStoreProgress.agda) are proved.
