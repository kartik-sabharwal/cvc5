#lang scribble/base

@(require
  latex-utils/scribble/math
  latex-utils/scribble/utils
  (rename-in scribble/base [?- soft-hyphen])
  (only-in scribble/core make-style make-color-property))

@(define (?-) soft-hyphen)
@(define concat string-append)
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
@(define (vec str) @elem[#:style "overline" str])
@(define (Tuple . xs) (list "\\langle " xs "\\rangle "))
@(define (equiv str) @elem[#:style "tilde" str])
@(define (red str) (elem #:style (make-style #f (list (make-color-property "red"))) str))

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

@section[#:style 'hidden-number]{Update}

Suppose we want to unroll the definition of the function symbol @m{f}.
Let the formals of @m{f} be written as @m{@vec{x}}.
Let the first unrolling of @m{f(@vec{x})} be @m{e[@vec{x}]}.
Since @m{f} is recursively defined, @m{e[@vec{x}]} will contain @m{n ≥ 1} subterms of the form @m{f(@vec{x} τ_i)} where @m{i} ranges from 1 through @m{n}.

Let @m{u}, for `uniquify', be the function that freshens all the bound variables in its argument.
It returns a pair where the first component is the uniquified expression and the second component is the uniquifying substitution.
We'll denote uniquified & alpha-equivalent variants with @m{e}'s and uniquifying substitutions with @m{υ}'s.
Here's why tracking the substitutions is important.
Say we start with @m{e[@vec{x}]} which contains @m{f(@vec{x} τ)} as a subterm.
Suppose also that @m{u(e[@vec{x}]) = @Tuple{@equiv{e}[@vec{x}], υ}}.
We remark that the domain of @m{τ} is @m{@vec{x}}.
The range of @m{τ} can contain variables bound in @m{e[@vec{x}]}.
This is exactly the domain of @m{υ}.
So it makes sense to apply @m{υ} to the range of @m{τ}.
Therefore @m{f(@vec{x} τ)} in @m{e[@vec{x}]} corresponds with @m{f(@vec{x} τ υ) = f(@vec{x} (υ ∘ τ))} in @m{@equiv{e}[@vec{x}]}.

Any @m{@Unroll} job takes 4 arguments.
@itemlist[
#:style 'ordered
@item{
The number of unrollings that remain.
}
@item{
A substitution @m{σ} over the formals @m{@vec{x}} of @m{f}.  
The idea is that the call being unrolled by this job is @m{f(@vec{x} σ)}.
So if 0 unrollings remain then the result of this job is literally @m{f(@vec{x} σ)}.
In the initial job it is the identity substitution over the formals.
In subsequent jobs, we use the value of a preceding @m{ω} substitution.
}
@item{
This is an abstraction @m{a[@vec{x}]} of some term @m{e_i[@vec{x}]}.
All the @m{n} calls to @m{f} in @m{e_i[@vec{x} σ]}, namely @m{f(@vec{x} ω_1)} through @m{f(@vec{x} ω_n)}, have been abstracted away as `holes' @m{H_1} through @m{H_n}.
In other words @m{f(@vec{x} ω_1)} through @m{f(@vec{x} ω_n)} fit into the holes @m{H_1} through @m{H_n} of @m{a[@vec{x} σ]} to get @m{e_i[@vec{x} σ]}.
@m{e_0[@vec{x}]} is just @m{e[@vec{x}]}, and @m{@Tuple{e_{i+1}@vec{x}, υ_{i+1}} = u(e_i @vec{x})}.
In the initial job it is the abstraction of @m{e[@vec{x} σ]}, which is really just the abstraction of @m{e[@vec{x}]} because @m{σ} is the identity substitution.
}
@item{
The list of @m{n} substitutions @m{ω_1} through @m{ω_n} introduced above.
It is important to note that @m{ω_j = υ_i ∘ σ}, but this only applies in all jobs after the initial job (remember, there is no @m{υ_0}).
In the initial job, @m{ω_j = τ_j}.
The domain of any @m{ω} substitution is always @m{@vec{x}}.
}
]

Any @m{@Combine} job takes a single abstraction as an argument.
It gets the abstraction from its `parent' @m{@Unroll} job.

@section{Preamble}

The common preamble for all our queries is as follows.
The value of the @emph{unroll} option is not set in stone.
It can be increased as necessary.

@verbatim{
(set-logic ALL)

(set-option :produce-models true)
(set-option :fmf-fun true)
(set-option :fmf-fun-rlv true)
(set-option :unroll 50)

(declare-datatypes ((List 1))
  ((par (T) ((cons (head T) (tail (List T))) (nil)))))

(define-fun-rec list.length.int ((l (List Int))) Int
  (ite (= l (as nil (List Int))) 0 (+ 1 (list.length.int (tail l)))))

(define-fun-rec list.get.int ((l (List Int)) (idx Int)) Int
  (ite (= idx 0) (head l) (list.get.int (tail l) (- idx 1))))

(define-fun-rec list.index.rec.int ((i Int) (l (List Int)) (val Int)) Int
  (ite (= l (as nil (List Int))) -1 (ite (= (head l) val) i (list.index.rec.int (+ 1 i) (tail l) val))))

(define-fun list.index.int ((l (List Int)) (val Int)) Int
  (list.index.rec.int 0 l val))

(define-fun-rec list.length.string ((l (List String))) Int
  (ite (= l (as nil (List String))) 0 (+ 1 (list.length.string (tail l)))))

(define-fun-rec list.get.string ((l (List String)) (idx Int)) String
  (ite (= idx 0) (head l) (list.get.string (tail l) (- idx 1))))

(define-fun-rec list.sum.int ((l (List Int))) Int
  (ite (= l (as nil (List Int))) 0 (+ (head l) (list.sum.int (tail l)))))

(define-fun-rec list.append.int ((l1 (List Int)) (l2 (List Int))) (List Int)
  (ite (= l1 (as nil (List Int))) l2 (cons (head l1) (list.append.int (tail l1) l2))))

(define-fun-rec list.append.string ((l1 (List String)) (l2 (List String))) (List String)
  (ite (= l1 (as nil (List String))) l2 (cons (head l1) (list.append.string (tail l1) l2))))

(define-fun-rec list.map_add.int ((l (List Int)) (val Int)) (List Int)
  (ite (= l (as nil (List Int))) (as nil (List Int)) (cons (+ (head l) val) (list.map_add.int (tail l) val))))

(define-fun-rec list.count.int ((l (List Int)) (val Int)) Int
  (ite (= l (as nil (List Int))) 0 (+ (ite (= (head l) val) 1 0) (list.count.int (tail l) val))))

(define-fun-rec list.count.string ((l (List String)) (val String)) Int
  (ite (= l (as nil (List String))) 0 (+ (ite (= (head l) val) 1 0) (list.count.string (tail l) val))))

(define-fun-rec list.count.bool ((l (List Bool)) (val Bool)) Int
  (ite (= l (as nil (List Bool))) 0 (+ (ite (= (head l) val) 1 0) (list.count.bool (tail l) val))))

(define-fun-rec list.count.real ((l (List Real)) (val Real)) Int
  (ite (= l (as nil (List Real))) 0 (+ (ite (= (head l) val) 1 0) (list.count.real (tail l) val))))

(define-fun list.contains.int ((l (List Int)) (val Int)) Bool
  (> (list.count.int l val) 0))

(define-fun list.contains.string ((l (List String)) (val String)) Bool
  (> (list.count.string l val) 0))
}

@section{Problem List}

Here are the problems from the holey set that cvc5 should be able to solve.

@itemlist[
@item{Study_4:0.  Done!}
@item{Study_5:0.  Extra, done!}
@item{Study_24:0.  Done!}
@item{LongestMonotonicSubstring:3.  Done!}
@item{LongestMonotonicSubstring:4.  Done!}
@item{LongestMonotonicSubstringTricky:2.  Done!}
@item{FirstNegCumulative:1.  Done!}
@item{FirstNegCumulative:2.  Done!}
@item{FirstNegCumulative:4.  Done!}
@item{FindContainers:0.  Done!}
@item{FindContainers:1.  Done!}
@item{FindContainers:2.  Done!}
@item{FindContainers:3.  Done!}
@item{FindContainers:4.  Done!}
@item{RollingMax:1.  Done!}
@item{RollingMax:2.  Done!}
@item{FindExtensions:1.  Done!}
@item{FindExtensions:2.  Done!}
@item{FindExtensions:3.  Done!}
@item{FindExtensions:4.  Done!}
@item{FindPositives:4.  Done!}
@item{BelowThreshold:0.  Done!}
@item{BelowThreshold:1.  Done!}
@item{BelowThreshold:2.  Done!}
@item{BelowThreshold:3.  Done!}
@item{BelowThreshold:4.  Done!}
@item{ConsonantFilter:1.  Done!}
@item{ConsonantFilter:2.  Done!}
@item{ConsonantFilter:3.  Done!}
@item{StrangeSplit:0.  Done!}
@item{StrangeSplit:1.  Done!}
@item{StrangeSplit:3.  Done!}
@item{StrangeSplit:4.  Done!}
@item{Triple0:0.  Done!}
@item{Triple0:1.  Done!}
@item{Triple0:2.  Done!}
@item{Triple0:3.  Done!}
@item{Triple0:4.  Done!}
@item{AnyEdge:0.  Done!}
@item{AnyEdge:1.  Done!}
@item{AnyEdge:2.  Done!}
@item{AnyEdge:3.  Done!}
@item{AnyEdge:4.  Done!}
@item{FindProductiveList:1.  Done!}
@item{FindProductiveList:2.  Done!}
@item{ListLen:3.  Done!}
]

@section{Changes}

I would like to make unrolling a preprocessing pass.
I want it to happen after @emph{match} expressions have been desugared.
I would like to read the names of the definitions to be unrolled from a file.
Let's plan these changes.

The function @emph{checkSat} in @emph{solver_engine.cpp} calls the function @emph{checkSatInternal} in the same file.
The function @emph{checkSatInternal} calls a different function named @emph{checkSat} defined in @emph{smt_driver.cpp}.
We will disambiguate these function using their namespaces: @emph{SolverEngine::checkSat} and @emph{SmtDriver::checkSat}.
The function @emph{SmtDriver::checkSat} passes a reference to the assertion pipeline to another function @emph{SmtDriver::getNext@(?-)AssertionsInternal}, which hands the same reference over to @emph{SmtDriverSingleCall::@(?-)getNextAssertions}, and this function finally adds assertions to the assertion pipeline.
Once the function @emph{SmtDriver::checkSat} calls @emph{getNextAssertionsInternal} to add assertions to the pipeline, it passes a reference to the pipeline to another function @emph{SmtDriverSingleCall::checkSatNext}, which immediately hands the same reference over to @emph{SmtSolver::preprocess} defined in @emph{smt_solver.cpp}.
The function @emph{SmtSolver::preprocess} subsequently passes the reference to the similarly named @emph{process} defined in @emph{preprocessor.cpp}.
The preprocessor possesses an instance of the class @emph{ProcessAssertions} and passes the reference to the assertions pipeline to this instance's member function @emph{apply}.
The funtion @emph{ProcessAssertions::apply} has numerous calls to the function @emph{applyPass}.
Each call to this @emph{applyPass} function expects two arguments: the first is expected to be a string that identifies the pass within the dictionary @emph{d_passes}, a field of @emph{ProcessAssertions}, and the second is expected to be the reference to the assertions pipeline.
The dictionary @emph{d_passes} maps each pass identifier to a pointer to an instance of the class @emph{PreprocessingPass}.
Each instance of the class @emph{PreprocessingPass} or one of its subclasses implements a function @emph{apply} that accepts a reference to the assertions pipeline and returns an instance of the class @emph{PreprocessingPassResult}.
All subclasses of @emph{PreprocessingPass} are defined in the subdirectory @emph{src/preprocessing/passes}.

@section[#:style 'hidden-number]{New preprocessing pass}

Follow these steps to define a new preprocessing pass named @emph{Unroll}.

@itemlist[
#:style 'ordered
@item{
Create @emph{preprocessing/passes/unroll.h} and @emph{unroll.cpp},
}
@item{
list these freshly created files in the file @emph{CMakeLists.txt},
}
@item{
make a call to the function @emph{registerPassInfo} in the file @emph{preprocessing_pass_registry.cpp} thus mapping the name of your pass to its constructor,
}
@item{
add a switch corresponding to your pass in the appropriate options file, for example @emph{quantifiers_options.toml},
}
@item{
conditionally invoke your pass at the correct point within the body of the function @emph{apply} in the file @emph{process_assertions.cpp}.
}
]

@emph{Note}.  If a preprocessing pass' information has been registered, an instance of the pass is created by the function @emph{finishInit} defined in @emph{process_assertions.cpp}.

@section[#:style 'hidden-number]{Sequence}

You want to execute the new preprocessing pass, @emph{Unroll}, when all @emph{match} expressions have been eliminated in favor of @emph{ite} expressions.
@emph{match} expressions are eliminated in the pass named @emph{ApplySubsts}.
@emph{ApplySubsts} is currently the first pass in the sequence.
The pass @emph{Unroll} should be placed after the pass @emph{ApplySubsts}.
I believe -- but cannot be sure -- that the @emph{Unroll} pass should be placed just before the @emph{QuantifiersPreprocess} pass and its successor, the @emph{FunDefFmf} pass.

@section[#:style 'hidden-number]{Assertion names}

The function @emph{SolverEngine::getUnsatCore} calls @emph{SolverEngine::getUnsatCoreInternal}, which receives a vector of nodes from @emph{UnsatCoreManager::getUnsatCore}, which receives its vector of nodes from @emph{PropEngine::getUnsatCore}, and runs this vector through @emph{UnsatCoreManager::convertPreprocessedToInput}

@section[#:style 'hidden-number]{Assertion pipeline}

@subsection[#:style 'hidden-number]{Study_4}

@section{Miscellaneous advice from Andy}

@itemlist[
@item{Make a new module that does reduction from recursive functions to the proper assertions.}
@item{Look at impl. of --quant-dsplit, 'checkOwnership' specifically.}
@item{SynthEngine in 'registerQuantifier' seems to be doing what I want.}
@item{Promote d_funDefEvaluator to a QuantifiersUtil in QuantifiersEngine.}
@item{Also look at ppNotifyAssertions.}
]