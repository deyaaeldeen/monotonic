# Overview #

This repository contains mechanizations of different dynamic semantics for
[monotonic references](https://doi.org/10.1007/978-3-662-46669-8_18) to enable
efficient gradual typing.

# Getting Started

You will need to have the following dependencies installed:

  - [Agda](https://agda.readthedocs.io/en/v2.5.4.2/getting-started/installation.html)
  - [Agda standard library](https://github.com/agda/agda-stdlib/tree/5819a4dd9c965296224944f05b1481805649bdc2)
  - [Agda standard library++](https://github.com/deyaaeldeen/stdlib-plusplus.agda/tree/0d468ea0187ca70c49dc8721501622a9fc180f5a)
  
Agda standard library++ is part of the [Metaborg](https://metaborg.github.io/) project and is used in the work presented by POPL'18 paper [Intrinsically-Typed Interpreters for Imperative Languages](https://dl.acm.org/citation.cfm?id=3158104). I maintain a fork to work with the latest version of Agda standard library, which can be installed by executing `make lib`.
