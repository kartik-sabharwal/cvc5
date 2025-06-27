# Conflict Conjecture Generator

## Example Problem

Here is one SMT-LIB problem on which the conflict conjecture generator is effective.

```
;; times-right-dist.smt2

(set-logic UFDT)

(declare-datatype Nat ((Z) (S (p Nat))))

(declare-fun plus (Nat Nat) Nat)
(assert (forall ((x Nat) (y Nat)) (! (=> (is-Z x) (= (plus x y) y)) :qid definition)))
(assert (forall ((x Nat) (y Nat)) (! (=> (is-S x) (= (plus x y) (S (plus (p x) y)))) :qid definition)))

(declare-fun mult (Nat Nat) Nat)
(assert (forall ((x Nat) (y Nat)) (! (=> (is-Z x) (= (mult x y) Z)) :qid definition)))
(assert (forall ((x Nat) (y Nat)) (! (=> (is-S x) (= (mult x y) (plus y (mult (p x) y)))) :qid definition)))

(assert (not (forall ((x Nat) (y Nat)) (= (mult x (S y)) (plus x (mult x y))))))

(check-sat)
```

## cvc5 Settings

Here is a configuration of cvc5 that solves the problem above in about 18 seconds assuming a debug build of cvc5. 
The actual time taken might vary with the computer we're running cvc5 on.

```
cvc5 --tlimit=20000 --dt-stc-ind --ctx-enum --ctx-enum-limit=15 --conflict-conjecture-gen --ccgen-filter-eval times-right-dist.smt2
```
