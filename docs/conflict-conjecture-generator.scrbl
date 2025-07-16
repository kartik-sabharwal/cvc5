#lang scribble/base

@(require latex-utils/scribble/math latex-utils/scribble/utils)

@title[#:date ""]{Conflict Conjecture Generator}

@section{Synthesizing Conjectures with SyGuS}

Here are the broad strokes.
@itemlist[
#:style 'ordered
@item{@tt{candDeq} is populated with the equalities in the equivalence class of false.}

@item{The terms in @tt{candDeq} are `concretized' using the model values of the symbols they mention.}

@item{We use some approach, disregarding the exact details, to `expand' the equivalence classes of the candidate disequalities.}

@;We never substitute a function with its model value.
@;We never substitute in the model value for a symbol that appears in a universally quantified formula.
@;We always substitute in the model value if our variable is a skolem.
]

@section{Task}

Let's write a function that collects equalities in the equivalence class of false, concretizes them, and assigns a variable to each equivalence class that occurs in such an equality.

@section{Understanding @tt{checkDisequality()}}

@tt{checkDisequality()} starts by clearing the conjecture buffer but let's forget about that for now.

It takes a disequality @m{s = t} and produces variables for the representatives of @m{s} and @m{t}'s equivalence classes.

@section{Understanding @tt{getGeneralizationsInternal()}}

@(define lparen (elem "("))
@(define rparen (elem ")"))
@(define (surround elt) (list lparen elt rparen))
@(define (fvs elt) (list @elem[#:style "operatorname"]{fvs} (surround elt)))
@(define V @fvs{t})
@(define (var elt) @elem[elt #:style "mathit"])

The current environment maintains a bijection between some subset of the current equivalence class representatives and a set of variables.
Let's call each of these variables a @emph{representative variable}.

@tt{getGeneralizationsInternal()} essentially traverses a graph.
The nodes in this graph are terms that can be constructed using the available function symbols and the 



accepts a representative variable @m{v} as input.




This function tracks the 


It collects the known expansions of @m{v} in @m{@var{grecs}}.