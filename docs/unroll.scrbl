#lang scribble/base

@(require
  latex-utils/scribble/math
  latex-utils/scribble/utils)

@(define plus @elem[#:style "operatorname"]{plus})
@(define S @elem[#:style "operatorname"]{S})
@(define ite @elem[#:style "operatorname"]{ite})
@(define P @elem[#:style "operatorname"]{p})
@(define is-Z @elem[#:style "operatorname"]{is-Z})
@(define (bv n) (list @elem[#:style "mathit"]{bv} "_{" (number->string n) "}"))
@(define (Set . xs) (list "\\{" xs "\\}"))
@(define Unroll @elem[#:style "operatorname"]{Unroll})
@(define Combine @elem[#:style "operatorname"]{Combine})
@; vector of x's
@(define vx @elem[#:style "mathbf"]{x})
@(define id @elem[#:style "mathsf"]{id})
@(define (mathbf str) @elem[#:style "mathbf" str])

@title[#:date ""]{Unrolling recursive definitions in cvc5}

@section[#:style 'hidden-number]{Implementation}

@tt{define-fun-rec} is an SMT-LIB command.
The first layer of the onion that handles this command is @tt{defineFunRec} in @emph{api/cpp/cvc5.cpp}.
The onion's next layer is @tt{defineFunctionRec} in @emph{smt/solver_engine.cpp}, followed by @tt{defineFunctionsRec} in the same file.
@tt{defineFunctionsRec} creates a `lemma' corresponding to the recursive definition.
To be concrete, if a user supplies this command:

@verbatim{
(define-fun-rec plus ((x Nat) (y Nat)) Nat
  (match x
    (((Z)    y)
     ((S px) (S (plus px y))))))
}

@tt{defineFunctionsRec} translates it into this universally quantified formula.

@verbatim{
(forall ((x Nat) (y Nat))
  (= (plus x y)
     (ite (is-Z x)
          y
          (S (plus (p x) y)))))
}

Once @tt{defineFunctionsRec} creates this formula, it passes the formula to @tt{addDefineFunDefinition} in @emph{smt/assertions.cpp}.
@tt{addDefineFunDefinition} puts this formula in @tt{d_globalDefineFunLemmas}.
The contents of @tt{d_globalDefineFunLemmas} appear to be re-asserted by the function @tt{refresh} in @emph{smt/assertions.cpp} each time cvc5 executes a @tt{(check-sat)} command.
@tt{refresh} grows the formula list by calling @tt{addFormula} (also in @emph{smt/assertions.cpp}) on each element of @tt{d_globalDefineFunLemmas}.
@emph{Before adding your own trace messages, peruse the body of} @tt{addFormula}.
This also means that the universally quantified formulas that represent recursive function definitions are pre-processed once for each @tt{(check-sat)} call.
Consequently if we make definition unrolling a pre-processing pass it'll happen once for each @tt{(check-sat)} call and this may cause us to repeat the work associated with unrolling.
For the moment, let's unroll within @tt{defineFunctionsRec}.

@section[#:style 'hidden-number]{Unrolling strategy}

Suppose we have a type @m{S}, three function symbols @m{f}, @m{u}, @m{v : S → S}, and another function symbol @m{p : S × S → S}.
@m{u}, @m{v}, and @m{p} are `opaque' in the sense that their definitions cannot be unrolled.
The only transparent, and therefore unrollable, function symbol is @m{f}.
Its body is:

@mp{
f(x) = p(f(u(x)), f(v(x)))
}

Our unrolling strategy involves extracting three nuggets of information from this body.

@itemlist[
@item{
The number of recursive calls @m{n}.  
Here @m{n = 2}.
}
@item{
A function @m{C} (for `combiner') that plugs in concrete expressions for the recursive calls in the body.
This function has one argument for each recursive call.
Here we need some representation of the function @m{(h_0, h_1) ↦ p(h_0, h_1)}.
We'll use a cvc5 @tt{Subs} object.
}
@item{
Functions @m{T_0} through @m{T_{n-1}} (for `transformer') that map the formal arguments to the actual arguments of the recursive calls.
Each of these functions has the same formal parameters as the function we want to unroll.
There are as many functions as there are recursive calls.
Here we need some representation of the functions @m{x ↦ u(x)} and @m{x ↦ v(x)}.
We'll use cvc5 @tt{Subs} objects.
}
]

@subsection[#:style 'hidden-number]{Abstraction}

To grab @m{n}, @m{C} and the @m{T}'s from the body of the original function $m{f}, we will perform a DFS over the function's body.
If we see a call to @m{f} in the body, we'll replace it with a fresh variable (of kind @tt{BOUND_VARIABLE}) and record it in a vector.
This means that all function symbols that occur in the arguments of a recursive call to @m{f} -- including @m{f} itself -- are opaque.
Conseqeuently our unrolling strategy isn't perfect though it ought to work on many examples that appear in practice.

What are the inputs to the @tt{makeAbstract()} function?
These should be the usual -- the function symbol, the formals, and the body.
What should be its outputs?
It ought to return 

@itemlist[
@item{The abstraction of the function's body, @m{C}.}
@item{The vector that contains the abstraction variables, in other words the bound variables introduced during abstraction.}
@item{The number of abstraction variables @m{n}, which equals the number of recursive calls.}
@item{The vector of substitutions @m{@mathbf{T}} over the formals, one substitution @m{T_i} for each recursive call.}
]

@subsection[#:style 'hidden-number]{Commands}

Next, we write a command interpreter that supports two commands @m{@Unroll} and @m{@Combine}.
@m{@Unroll} takes 2 arguments, the first of which is expected to be a number that represents the number of pending unrollings.
The second argument of @m{@Unroll} is expected to be a substitution from the formals of the original function to the actuals of a recursive call in @emph{some} unrolling of the original function.
@m{@Combine} takes no arguments.

@subsection[#:style 'hidden-number]{Interpretation}

Let @m{f} denote the original function and let @m{@vx} denote its formals.
The interpreter has a job stack as well as a result stack.
The job stack starts with an @m{@Unroll(k, @id)} command where @m{@id} denotes the identity substitution on @m{@vx}.
To interpret @m{@Unroll(0, σ)}, push @m{f(@vx σ)} on to the result stack.
To interpret @m{@Unroll(m, σ)}, push a @m{@Combine} on to the job stack.
Then for each @m{i} in the range @m{0} through @m{n-1} push @m{@Unroll(m-1, σ ∘ T_i)} where @m{σ ∘ T_i} (substitution composition) represents the act of applying the substitution @m{σ} to the range of @m{T_i}.
Finally, to interpret @m{@Combine}, pop the top @m{n} terms from the result stack and feed them to @m{C}.  Push the new term on to the result stack.

@section{Miscellaneous advice from Andy}

@itemlist[
@item{Make a new module that does reduction from recursive functions to the proper assertions.}
@item{Look at impl. of --quant-dsplit, 'checkOwnership' specifically.}
@item{SynthEngine in 'registerQuantifier' seems to be doing what I want.}
@item{Promote d_funDefEvaluator to a QuantifiersUtil in QuantifiersEngine.}
@item{Also look at ppNotifyAssertions.}
]