Require Import Loader.
From hahn Require Import Hahn.

Section Example.

Variable A : Type.

(* assert_eq!(simplify("(;; ( * a) (;; (? a) (? a)))"), "( * a)"); *)
Lemma aaa (r : relation A) : 
  (r^* ;; r^?) ;; r^? ⊆ r^*.
Proof.
  rewrite rt_cr.
  rewrite rt_cr.
  reflexivity.
Qed.

Lemma t1_egg (r : relation A) :
  (r^* ;; r^?) ;; r^? ⊆ r^*.
Proof.
  Cegg solve.
Qed.

Lemma t2_egg (r : relation A) :
  r^* ;; r^? ⊆ r^*.
Proof.
  Cegg solve.
Qed.

Lemma t3_egg (r : relation A) :
  ((r^* ;; r^?) ;; r^?) ;; r^? ⊆ r^?.
Proof.
  Cegg solve.
Abort.

End Example.




