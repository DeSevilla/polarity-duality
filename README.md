# Polarized

A simple polarized type system for computational propositional logic, following the model of Downen & Ariola's [Duality in Action](https://drops.dagstuhl.de/storage/00lipics/lipics-vol195-fscd2021/LIPIcs.FSCD.2021.1/LIPIcs.FSCD.2021.1.pdf).
I've defined a focusing proof search for it, to improve my understanding of both polarized types/logic
and focusing in general.

# Building

Using Stack, should be as simple as `stack run`.
Edit /app/Main.hs to change what it does.
By default, it runs a few test cases.

# To Do/Future Work

* Quantifiers - seem to require unification, unlike the rest of the terms.
* Evaluation - rather fiddly. The rules involve a value restriction that's not built in to this implementation.
* Improve error messages.
* Defining a parser so I can write this normally. Or weirdly, even.
* ???