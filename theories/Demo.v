Require Import Loader.
From hahn Require Import Hahn.

Section Example.

Variable A : Type.

(* assert_eq!(simplify("(;; ( * a) (;; (? a) (? a)))"), "( * a)"); *)
Lemma aaa (r : relation A) : 
  (r^* ;; r^?) ;; r^? ≡ r^*.
Proof.
  rewrite rt_cr.
  rewrite rt_cr.
  reflexivity.
Qed.

Lemma aaa_egg (r : relation A) :
  (r^* ;; r^?) ;; r^? ≡ r^*.
Proof.
  Cegg solve.
Qed.

End Example.




