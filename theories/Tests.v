Require Import Loader.
From hahn Require Import Hahn.

Section Tests.

Variable A : Type.

Lemma test_norm_1 (r : relation A) :
  (r^* ;; r^?) ;; r^? ⊆ r^*.
Proof.
  Cegg solve.
Qed.

Lemma test_not_solved_at_end (r : relation A) :
  ((r^* ;; r^?) ;; r^?) ;; r^? ⊆ r^?.
Proof.
  Cegg solve.
Abort.

Lemma invalid_syntax_a (a : bool) (b : bool) :
  andb a b = true -> a = true.
Proof. 
  Fail Cegg solve.
  destruct a.
  - reflexivity.
  - discriminate.
Qed.

Lemma invalid_relation (r : relation A) :
  r = r^*.
Proof.
  Fail Cegg solve.
Abort.

Lemma nothing_to_rewrite (r : relation A) : 
  r^* ⊆ r^?.
Proof.
  Cegg solve.
Abort.

Lemma test_norm_2 (r : relation A) :
  (r^* ;; r^?) ;; (r ∪ r^*) ⊆ r^*.
Proof.
  Cegg solve.
Abort.

Lemma test_norm_3 (r : relation A) :
  ⦗fun _ => True⦘ ;; r ⊆ r.
Proof.
  Cegg solve.
Qed.

Lemma test_norm_4 (r : relation A) :
  (fun _ _ => False) ;; r ⊆ (fun _ _ => False).
Proof.
  Cegg solve.
Qed.

Lemma test_incorrect_lambda (r : relation A) :
  (fun _ _ => True) ;; r ⊆ (fun _ _ => False).
Proof.
  Fail Cegg solve.
Abort.

End Tests.

(* 
                    Проблемы: 
    -- Проблемы с rewrite в нескольких местах
    -- Rewrite сработал не там где надо 
*)