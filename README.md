Formalizing Mathematics in Agda
===============================

This is an open-ended project to formalize mathematics using the type theory of Agda programming language. Currently, I am focusing on formalizing Group Theory. My current long-term goal is to formalize a significant portion of undergraduate algebra (group, ring, field, module and Galois theories), basic algebraic geometry (curves, surfaces, Grassmanian varieties) and probability theory.

## Requirements & Proof Checking
You can see the proofs without needing any special software; although identifiers make use of Unicode characters (such as ∀, ∃, 𝔄, →), so, you should be able to see them.

You need Agda version >=2.5.3 to check proofs, this is the only dependency. Run:

```
make check
```

This command will run `agda --safe --without-K` on all source files. You can confirm that all proofs are checked by Agda. Since classical and constructive theorems are separated via modules, agda can be run on `--safe` mode which makes sure I don't lead myself to contradiction.

## License

All my work is released under GNU GPLv3+. You're welcome to study, change, redistribute, share all my proofs.

## Progress

### First-Order Logic

Basic logical connectives and quantifiers are defined. Basic theorems are proved.

### Group Theory

Defined group. Defined group order, group homomorphism, group isomorphism, group action, subgroup and group centralizer. Defined quotient group.

Proved theorems:

Completed all standard group bookkeeping theorems:
 * Identity is unique
 * For each element, its inverse is unique
 * (a⁻¹)⁻¹ = a
 * (a · b)⁻¹ = b⁻¹ · a⁻¹
 
Subgroup Theorems:
 * Subgroup criterion
 * Centralizer is a subgroup
 
 
