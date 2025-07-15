#lang scribble/base

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