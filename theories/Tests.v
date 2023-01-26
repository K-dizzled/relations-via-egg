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

Variable kek : A -> A -> Prop.
Variable lol : A -> A -> Prop.
Variable mem : A -> A -> Prop.

Record Wf :=
  { 
    kek_in_lol : kek ⊆ lol ;
    lol_in_mem : lol ⊆ mem ;
    mem_in_kek : mem ≡ kek ;; lol^*;
  }.

Cegg config Wf.

Implicit Type WF : Wf.

Lemma bbb WF (r : relation A) :
  kek^* ;; kek^? ⊆ lol^*.
Proof.
  Cegg solve.
  apply inclusion_rt_rt.
  apply WF.
Qed.

Lemma ccc WF (r : relation A) :
  kek ;; lol^* ⊆ mem.
Proof.
  rewrite <- mem_in_kek.
  reflexivity.
  apply 
  Cegg solve eq.  
Qed.

End Tests.

(* 
                    Проблемы: 
    -- Проблемы с rewrite в нескольких местах
    -- Rewrite сработал не там где надо 
    -- Првоерить rewite в обратную сторону
    -- Если конфиг сломался
*)