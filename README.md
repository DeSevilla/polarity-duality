# Polarized

A simple polarized type system for computational propositional logic, following the model of Downen & Ariola's [Duality in Action](https://drops.dagstuhl.de/storage/00lipics/lipics-vol195-fscd2021/LIPIcs.FSCD.2021.1/LIPIcs.FSCD.2021.1.pdf).
I've defined a focusing proof search for it, to improve my understanding of both polarized types/logic
and focusing in general.

It's set up to build and run with Stack (`stack run`).
It will prompt you for a polarized type, search for a value of that type, and 
(if successful) verify that it has that type.

* Atomic types are ALL CAPS letters (`A`, `B`, `X`, `Y`, `SOMETHING`, `OTHER`).
* Top/True/Unit is `tt`.
* Bottom/False/Void is `ff`.
* Positive conjunction is `(<subterm> * <subterm>)`.
* Positive disjunction is `(<subterm> + <subterm>)`. 
* Positive negation is `-<subterm>`.
* Negative conjunction is `(<subterm> & <subterm>)`.
* Negative disjunction is `(<subterm> | <subterm>)`, because ⅋ is too hard to type.
* Negative negation is `~<subterm>`.
* Up-shift is `^<subterm>` and down-shift is `v<subterm>`.
* Incorrectly mixing positive and negative terms will result in a parse error.

For example, there are multiple ways to formulate the law of the excluded middle
for a positive atomic type A.
`^(vA | ~A)` is inhabited, but `(A + ^~A)` is uninhabited.
This is because the former type corresponds to A -> A, whereas `+` behaves
like an ordinary (intuitionistic) sum type and requires a definite value either of A
or of not-A. However, by adding a double polarity shift to the latter, we get the
inhabited `^v(A + ^~A)` -- which represents the *classical* law of the excluded middle,
and is inhabited by [Wadler's devil](https://homepages.inf.ed.ac.uk/wadler/papers/dual/dual.pdf)
([see also](https://www.cs.cmu.edu/~cmartens/if/dem.html))

# To Do/Future Work

* Quantifiers, which seem to require unification, unlike the rest of the terms.
* Evaluation, which is rather fiddly. The rules involve a value restriction that's not built in to this implementation.
* Improve error handling, which is not good currently.
* ???