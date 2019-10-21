# Linear, Intrinsically-Typed Interpreters

An Agda library for programming with separation logic, based on proof-relevant separation algebras.
The code is organized as follows:

```
└── src
    ├── Everything.agda       Development entrypoint
    ├── Relation
    │   └── Ternary           The library
    ├── Sessions              Session-types case study
    │   ├── Semantics.agda
    │   ├── Syntax.agda
    │   ├── ...
    ├── Typed
    │   ├── LTLC.agda         LTLC semantics
    │   ├── LTLCRef.agda      LTLCRef semantics
```

The code has been type-checked using Agda 2.6.0.1.
The standard library version that was used is included in `lib/`.

[Agda](https://agda.readthedocs.io/en/latest/) is usually developed in Emacs.
It is highly recommended to use Agda's 
[emacs mode](https://agda.readthedocs.io/en/latest/tools/emacs-mode.html) to typecheck the code.
This does not only provide type-sensitive highlighting, but also allows you to navigate the
code by jumping to definitions.
