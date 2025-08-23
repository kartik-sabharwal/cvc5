#lang scribble/base

@(require latex-utils/scribble/math latex-utils/scribble/utils)

@title[#:date ""]{Conflict-Based Conjecture Generator}

@section{A Situation to Diagnose}

We have the following input file.

@verbatim{
;; times-right-dist.smt2

(set-logic UFDT)

(declare-datatype Nat ((Z) (S (p Nat))))

(declare-fun plus (Nat Nat) Nat)
(assert 
 (forall ((y Nat)) (! 
   (= (plus Z y) y)
 :pattern ((plus Z y)))))
(assert 
 (forall ((x Nat) (y Nat)) (! 
   (= (plus (S x) y) (S (plus x y)))
 :pattern ((plus (S x) y)))))

(declare-fun mult (Nat Nat) Nat)
(assert 
 (forall ((y Nat)) (! 
   (= (mult Z y) Z)
 :pattern ((mult Z y)))))
(assert 
 (forall ((x Nat) (y Nat)) (! 
   (= (mult (S x) y) (plus y (mult x y)))
 :pattern ((mult (S x) y)))))

(assert 
 (not 
  (forall ((x Nat) (y Nat))
    (= (mult x (S y)) (plus x (mult x y))))))

(check-sat)

(exit)
}

We also have this tagged revision in a fork of cvc5.

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