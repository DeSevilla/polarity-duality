# Polarized

A simple polarized type system for computational propositional logic, following the models of Downen & Ariola's [Duality in Action](https://drops.dagstuhl.de/storage/00lipics/lipics-vol195-fscd2021/LIPIcs.FSCD.2021.1/LIPIcs.FSCD.2021.1.pdf) and Zeilberger's [On the Unity of Duality](https://www.lix.polytechnique.fr/~zeilberger/papers/unity-duality.pdf).
I've defined a focusing proof search for it, to improve my understanding of both polarized types/logic
and focusing in general.

It's set up to build and run with Stack (`stack run`).
It will prompt you for a polarized type, search for a value of that type, and 
(if successful) verify that it has that type.

* Atomic types are ALL CAPS (`A`, `B`, `X`, `Y`, `SOMETHING`, `OTHER`).
  Their polarity is inferred.
* Top/True/Unit is `top`, while Bottom/False/Void is `btm`.
* Positive connectives: conjunction is `(<pos> * <pos>)`, disjunction is `(<pos> + <pos>)`.
  and negation is `-<neg>`.
* Negative connectives: conjunction is `(<neg> & <neg>)`, disjunction is `(<neg> | <neg>)`
  (because ⅋ is too hard to type), and negation is `~<pos>`.
* Up-shift is `^<neg>` and down-shift is `v<pos>`.
* The function type `(<pos1> => <pos2>)` is syntax sugar for `^(~<pos1> | v<pos2>)`.
* Parentheses are required on all binary operators, including `=>`, and otherwise disallowed.
* To quit, use Ctrl+C or type `QUIT` (all-caps).

For example, there are multiple ways to formulate the law of the excluded middle
for a positive atomic type A.
`^(vA | ~A)` is inhabited, but `(A + ^~A)` is uninhabited.
The former type corresponds to A -> A (indeed, `(A => A)` is parsed as the same value).
It is inhabited by the identity function.
On the other hand, `+` behaves like an ordinary, intuitionistic sum type and requires a definite value
either of A or of not-A. Since A is atomic, we have neither.

However, by adding a double polarity shift, we get the inhabited `^v(A + ^~A)`!
This represents the *classical* law of the excluded middle, and its inhabitant is
[Wadler's devil](https://homepages.inf.ed.ac.uk/wadler/papers/dual/dual.pdf)
([see also](https://www.cs.cmu.edu/~cmartens/if/dem.html)).

Some other inhabited types:
* `((A + B) => ^(vA | vB))`
* `(A => (A + B))`
* `(((^(vA | ~A) * (A => (A + B))) * (((A + B) => ^(vA | vB)) * ^v(A + ^~A))) * ^(v^(vA | vB) | ~(A + B)))`

Incorrectly mixing positive and negative terms will result in a parse error.
Using an atomic type both positively and negatively will result in a search failure.
Neither of these is ideal.

# To Do/Future Work

* Quantifiers, which are more complex than the rest of the types as they involve substitution
  (might need unification?)
* Evaluation, which is rather fiddly -- the rules involve a value restriction that's not built in to this implementation.
* Improve error handling, which is not good currently.
* Improve parsing, which is inflexible.
* Improve display of terms.
