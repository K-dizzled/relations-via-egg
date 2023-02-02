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

Lemma test_dirs_in_rewrite_1 (r : relation A) : 
  r^+ ⊆ r ;; r^*.
Proof. 
  Cegg solve eq.
Qed.

Lemma test_dirs_in_rewrite_2 (r : relation A) : 
  r ;; r^* ⊆ r^+.
Proof. 
  Cegg solve eq.
Qed.

Lemma ccc WF (r : relation A) :
  kek ;; lol^* ⊆ mem.
Proof.
  Cegg solve eq.
Abort.

End Tests.

(* 
                    Проблемы: 
    -- Проблемы с rewrite в нескольких местах
    -- Rewrite сработал не там где надо 
    -- Если конфиг сломался

    -- Если лемма определена для конкретных отношений и не 
       принимает (r : relation A)
  
    -- Доказательство я получаю с помощью egg::Runner::explain_equivalence 
       а оно паникует, если не получилось доказать еквивалентность
       термов и этого не избежать, так что если тактика "Cegg solve eq"
       вызывается и не отрабатывает до конца, то вылетает стремная ошибка.
       Это фиксится только тем, что мы забиваем на обработку ошибок на вызове 
       этой тактики на стороне Раста и всегда вылетаем с одной и той же ошибкой. 
*)