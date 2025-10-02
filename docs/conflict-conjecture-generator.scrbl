#lang scribble/base

@(require latex-utils/scribble/math latex-utils/scribble/utils)

@(define WorksButSlow "https://github.com/kartik-sabharwal/cvc5/releases/tag/WorksButSlow")
@(define plus (elem #:style "mathrm" "plus"))
@(define S (elem #:style "mathrm" "S"))
@(define pr (elem #:style "mathrm" "p"))
@(define is-Z (elem #:style "mathrm" "is\\text{-}Z"))
@(define is-S (elem #:style "mathrm" "is\\text{-}S"))
@(define forall "\\forall")
@(define (bv n) (list @elem[#:style "mathit" "bv"] (string-append "_{" (number->string n) "}")))

@title[#:date ""]{Conflict-Based Conjecture Generator}

@section{Input file}

We're going to use the following input file, @tt{times-right-dist.smt2}, until we have a procedure that is tolerant to our choice of conjecture.

@verbatim{
;; times-right-dist.smt2

(set-logic UFDT)

(declare-datatype Nat ((Z) (S (p Nat))))

(declare-fun plus (Nat Nat) Nat)
(assert 
 (forall ((x Nat) (y Nat)) (! 
   (=> (is-Z x)
       (= (plus x y) y))
 :pattern ((plus x y))
 :qid definition)))
(assert 
 (forall ((x Nat) (y Nat)) (! 
   (=> (is-S x)
       (= (plus x y) (S (plus (p x) y))))
 :pattern ((plus x y))
 :qid definition)))

(declare-fun mult (Nat Nat) Nat)
(assert
 (forall ((x Nat) (y Nat)) (! 
   (=> (is-Z x)
       (= (mult x y) Z))
 :pattern ((mult x y))
 :qid definition)))
(assert 
 (forall ((x Nat) (y Nat)) (! 
   (=> (is-S x)
       (= (mult x y) (plus y (mult (p x) y)))) 
 :pattern ((mult x y))
 :qid definition)))

(assert 
 (not 
  (forall ((x Nat) (y Nat))
    (= (mult x (S y)) (plus x (mult x y))))))

(check-sat)
}

@section{Progress}

If we run cvc5 on @tt{times-right-dist.smt2} with the below option set, and provide either one of these two splitting lemmas, it will reply `unsat'.

@itemlist[
@item{@m{@forall x, y, z. @plus(x, @plus(y, z)) = @plus(y, @plus(x, z))}}
@item{@m{@forall y, x, z. @S(@plus(@S(x), @plus(y, z))) = @plus(@S(y), @S(@plus(x, z)))}}
]

@verbatim{
$CVC5_EXECUTABLE
"--dag-thresh=0"
"--dt-stc-ind"
"--conflict-conjecture-gen"
"--ccgen-expand-reps=3"
"times-right-dist.smt2"
}

Observe that turning on the contextual term enumerator with @tt{@literal{--}ctx-enum} worsens the performance of cvc5.
@; ADD MORE DETAIL!  Can cvc5 prove a conjecture?  Can cvc5 assume it and prove the goal?  If cvc5 can't prove the conjecture, what does that mean for the splitting lemma?

@section{Proposal}

@; Evaluation-based filtering or subsolver with unrolling & finite model finding to prove the goal.
@; Add another filter that uses a subsolver to check whether a candidate conjecture can be proven by structural induction without conjecture generation under the current collection of universally quantified formulas.  If we can't prove the goal, we reject.

@section{A Situation to Diagnose}

We have the following input file.

@verbatim{

(exit)
}

We also have @hyperlink[@WorksButSlow]{this} tagged revision in a fork of cvc5.

We have a set of options with which to invoke cvc5 on the above file.

@verbatim{
$CVC5_EXECUTABLE
--tlimit=600000
--dt-stc-ind
--conflict-conjecture-gen
--ctx-enum
--ctx-enum-limit=15
--seed=2620337509
--ccgen-expand-reps=3
times-right-dist.smt2
}

A debug build of cvc5 replies 'unsat' in approximately 6 minutes.

We'd like to help cvc5 reply more quickly.

@section{Understanding}

Consider the same input file as above.
Run cvc5 on it with the following option set.

@verbatim{
"/home/kartik/Documents/code/c++/cconj-gen-cvc5/build/bin/cvc5"
"--dag-thresh=0"
"--dt-stc-ind"
"--conflict-conjecture-gen"
"--ctx-enum"
"--ctx-enum-limit=20"
"--seed=2620337509"
"--ccgen-expand-reps=3"
"--no-cbqi"
"--user-pat=strict"
"times-right-dist.smt2"
}

Also suppose cvc5 is configured to apply four filters to candidate conjectures.

@itemlist[
@item{is the conjecture already cached, in the sense that it has passed all filters before?}
@item{can we use e-matching to find a substitution that falsifies the conjecture?}
@item{is the conjecture deductively entailed?}
@item{does the user approve?}
]

The fourth filter involves writing a conjecture to standard output, and reading the user's response from standard input.
Here is an example.

@verbatim{
Should the following conjecture be kept?
(forall ((N0 Nat) (N1 Nat)) (= (plus N0 (plus N0 (mult N0 N1))) (mult N0 (S (S N1)))))
[Yes/No]: No
}

Suppose we reject all conjectures before the following one, which is 36th in the sequence, and turn off the conjecture generator immediately after.
cvc5 quickly replies `unsat'.

@verbatim{
(forall ((N1 Nat) (N0 Nat) (N2 Nat)) 
  (= (plus N0 (plus N1 N2)) 
     (plus N1 (plus N0 N2))))
}

I have observed that in practice accepting many conjectures will cause the solver to be overwhelmed with universally quantified formulas and take many minutes to reply `unsat'.
It may be helpful to go over all the conjectures and find a way to prune away some candidates that are clearly bad.
I believe that when we print a conjecture we should also print how many substitutions it was tested with.
Maybe there is a chance that we can reject conjectures that were tested on less than @m{n} substitutions.
I have already changed the filter to reject any conjecture that was tested on zero substitutions.

@section{A Finer Situation}

Start with the same input file as above.

Run cvc5 with the following options.

@verbatim{
$CVC5_EXECUTABLE
--dag-thresh=0
--dt-stc-ind
--conflict-conjecture-gen
--ctx-enum
--ctx-enum-limit=20
--seed=2620337509
--ccgen-expand-reps=3
--no-cbqi
--user-pat=trust
times-right-dist.smt2
}

Manually rejecting conjectures till you find the following.
Keep it and turn off the conjecture generator.

@verbatim{
(forall ((N1 Nat) (N0 Nat) (N2 Nat))
  (= (S (plus (S N0) (plus N1 N2)))
     (plus (S N1) (S (plus N0 N2)))))
}

cvc5 does not respond with `unsat' even after waiting five minutes.
It may be useful to record all inferences after this lemma is sent.

@section{Proved Conjectures}

Store all asserted universally quantified formulas in a set.
Do this only once, during the first call to @tt{ConflictConjectureGenerator::check()}.
Do not clear the set.
Before checking that the conjecture generator is switched off, print all asserted universally quantified formulas that are absent from the set.
Call the set @tt{d_iuqf} for `initial universally quantified formulas'.
@bold{We abandon this section for now.}

@section{Missing Skolemization?}

Consider two situations.
In the first, we have a theorem of the form @m{\forall x, y, z. P(x, y, z)}.
cvc5 will need to skolemize this twice.

@; Any one of these alternatives will suffice independently as a lemma.
@; All can be proved by cvc5 with just structural induction.
@; 
@; 1.  (forall ((x Nat) (y Nat) (z Nat)) (= (plus x (plus y z)) (plus z (plus x y))))
@; 2.  (forall ((x Nat) (y Nat) (z Nat)) (= (plus x (plus y z)) (plus y (plus x z))))
@; 3.  (forall ((a Nat) (b Nat) (c Nat)) (= (S (plus b (plus a c))) (plus (S a) (plus b c))))
@; 4.  (forall ((a Nat) (b Nat) (c Nat)) (= (S (plus b (plus (S a) c))) (plus (S (S a)) (plus b c))))
@; 5.  (forall ((a Nat) (b Nat) (c Nat)) (= (S (plus b (S (plus a c)))) (plus (S (S a)) (plus b c))))
@; 6.  (forall ((a Nat) (b Nat) (c Nat)) (= (plus (S (S b)) (plus a c)) (S (plus a (plus (S b) c)))))
@; 7.  (forall ((a Nat) (b Nat) (c Nat)) (= (plus (S (S b)) (plus a c)) (S (plus a (S (plus b c))))))

@section{Another Situation to Diagnose}

Consider this relatively simple problem.
We're going to solve it as a human being before we check whether cvc5 takes the right steps to solve it.

@mp{
@forall n. @S(@S(@plus(n, n))) = @plus(@S(n), @S(n))
}

We'll try to prove it by induction on @m{n}.
Skolemize @m{n} as @m{k}.
The base case, where @m{@is-Z(k)} holds, is trivial.
Let's skip it.
Now consider the induction case.
That's when @m{@is-S(k)} holds.
The induction hypothesis is:

@mp{
@S(@S(@plus(@pr(k), @pr(k)))) = @plus(@S(@pr(k)), @S(@pr(k)))
}

The goal is:

@mp{
@S(@S(@plus(k, k))) = @plus(@S(k), @S(k))
}

Symbolic evaluation of the goal's LHS yields:

@mp{
@S(@S(@S(@plus(@pr(k), k))))
}

Symbolic evaluation of the RHS yields:

@mp{
@S(@S(@plus(@pr(k), @S(k))))
}

Abstracting away @m{@pr(k)} as @m{m} and @m{k} as @m{n} yields the conjecture:

@mp{
@forall m, n. @S(@S(@S(@plus(m, n)))) = @S(@S(@plus(m, @S(n))))
}

This ought to be provable.
What is cvc5 missing?
Maybe we'll benefit from thinking in terms of equivalence classes.
In our trace, the LHS corresponds with @m{@bv[621]} and the RHS corresponds with @m{@bv[629]}.