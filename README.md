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
