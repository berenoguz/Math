Formalizing Mathematics in Agda
===============================

This is an open-ended project to formalize mathematics using the type theory of Agda programming language. Currently, I am focusing on formalizing Group Theory. My current long-term goal is to formalize a significant portion of undergraduate algebra (group, ring, field, module and Galois theories), basic algebraic geometry (curves, surfaces, Grassmanian varieties) and probability theory.

I will be focusing on classical mathematics. This means, all of these proofs (possibly) depend on the law of excluded middle. Moreover, I currently do not plan to spend any effort seperating theorems depend on this principle and those that do not. Once I get satisfactory results in my project, I might work on some constructive theories.

## Requirements & Proof Checking
You can see the proofs without needing any special software; although identifiers make use of Unicode characters (such as ∀, ∃, 𝔄, →), so, you should be able to see them.

You need Agda version >=2.5.3 to check proofs, this is the only proof. Run:

```
make check
```

This command will run `agda` on all source files. You can confirm that all proofs are checked by Agda.

## License

All my work is released under GNU GPLv3+. You're welcome to study, change, redistribute, share all my proofs.

## Progress

### First-Order Logic

Basic logical connectives and quantifiers are defined. Basic theorems are proved.

### Group Theory

Defined group. 

Proved theorems:

 * Identity is unique
 * For each element, its inverse is unique
