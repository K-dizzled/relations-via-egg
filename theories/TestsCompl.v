Require Import Loader.
From hahn Require Import Hahn.

Section Tests.

Variable A : Type.

Lemma test_1 (r : relation A) :
    (r^+)^* ≡ r^* ;; (r ;; r^*)^?.
Proof. Cegg solve. Admitted.

(* Lemma test (r r' : relation A) :
 ((r ∪ r^+)^+)^+ ≡ (r ∪ r^+)^+.
Proof. Cegg solve eq. Qed. *)

End Tests.