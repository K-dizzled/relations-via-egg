Require Import Loader.
From hahn Require Import Hahn.

Section Tests.

Variable A : Type.

Lemma test_norm_1 (r : relation A) :
  (r^* ;; r^?) ;; r^? ⊆ r^*.
Proof.
  Cegg solve eq.
Qed.

Lemma test_not_solved_at_end (r : relation A) :
  ((r^* ;; r^?) ;; r^?) ;; r^? ⊆ r^?.
Proof.
  Fail Cegg solve eq.
Abort.

Lemma invalid_syntax_a (a : bool) (b : bool) :
  andb a b = true -> a = true.
Proof. 
  Fail Cegg solve eq.
  destruct a.
  - reflexivity.
  - discriminate.
Qed.

Lemma invalid_relation (r : relation A) :
  r = r^*.
Proof.
  Fail Cegg solve eq.
Abort.

Lemma test_norm_3 (r : relation A) :
  ⦗fun _ => True⦘ ;; r ⊆ r.
Proof.
  Cegg solve eq.
Qed.

Lemma test_norm_4 (r : relation A) :
  (fun _ _ => False) ;; r ⊆ (fun _ _ => False).
Proof.
  Cegg solve eq.
Qed.

Lemma test_incorrect_lambda (r : relation A) :
  (fun _ _ => True) ;; r ⊆ (fun _ _ => False).
Proof.
  Cegg solve.
Abort.

Variable kek : A -> A -> Prop.
Variable lol : A -> A -> Prop.
Variable mem : A -> A -> Prop.

Variable kek_s : A -> Prop.
Variable lol_s : A -> Prop.

Record Wf :=
  { 
    kek_in_lol : kek ⊆ lol ;
    lol_in_mem : lol ⊆ mem ;
    mem_in_kek : mem ≡ kek ;; lol^*;
    e_kek_in_e_lol : ⦗kek_s⦘ ⊆ ⦗lol_s⦘;
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
Proof. Cegg solve eq. Qed.

Lemma test_dirs_in_rewrite_2 (r : relation A) : 
  r ;; r^* ⊆ r^+.
Proof. Cegg solve eq. Qed.

Lemma ccc WF (r : relation A) :
  kek ;; lol^* ⊆ mem.
Proof. Cegg solve eq. Qed.

Lemma test_eqv_rel WF (r : relation A) :
  ⦗kek_s⦘ ⊆ ⦗lol_s⦘.
Proof. Cegg solve eq. Qed.

Lemma test_multiple_args (r1 : relation A) (r2 : relation A) :
  r1 ∩ r2 ⊆ r2 ∩ r1.
Proof. Cegg solve eq. Qed.

Lemma test_minus_false_r (r : relation A) :
  r \ ∅₂ ⊆ r.
Proof. Cegg solve eq. Qed.

Lemma test_minus_false_l (r : relation A) :
  ∅₂ \ r ⊆ ∅₂.
Proof. Cegg solve eq. Qed.

Lemma test_crE (r : relation A) :
  r^? ⊆ ⦗fun _ => True⦘ ∪ r. 
Proof. Cegg solve eq. Qed.

Lemma test_rtE (r : relation A) :
  r^* ⊆ ⦗fun _ => True⦘ ∪ r^+.
Proof. Cegg solve eq. Qed.

Lemma test_csE (r : relation A) :
  r^⋈ ⊆ r ∪ r⁻¹.
Proof. Cegg solve eq. Qed.

Lemma test_crsE (r : relation A) :
  r^⋈? ⊆ ⦗fun _ => True⦘ ∪ r ∪ r⁻¹.
Proof. Cegg solve eq. Qed.

Lemma test_crsEE (r : relation A) :
  r^⋈? ⊆ ⦗fun _ => True⦘ ∪ r^⋈.
Proof. Cegg solve eq. Qed.

Lemma test_rt_begin (r : relation A) :
  r^* ⊆ ⦗fun _ => True⦘ ∪ r ⨾ r^*.
Proof. Cegg solve eq. Qed.

Lemma test_rt_end (r : relation A) :
  r^* ⊆ ⦗fun _ => True⦘ ∪ r^* ⨾ r.
Proof. Cegg solve eq. Qed.

Lemma test_rewrite_ct_rt (r : relation A) :
  r^+ ;; r^* ⊆ r^+.
Proof. Cegg solve eq. Qed.

Lemma test_rt_ct (r : relation A) :
  r^* ⨾ r^+ ⊆ r^+.
Proof. Cegg solve eq. Qed.

Lemma test_cr_ct (r : relation A) :
  r^? ⨾ r^+ ⊆ r^+.
Proof. Cegg solve eq. Qed.

Lemma test_ct_cr (r : relation A) :
  r^+ ⨾ r^? ⊆ r^+.
Proof. Cegg solve eq. Qed.

Lemma test_rt_rt (r : relation A) :
  r^* ⨾ r^* ⊆ r^*.
Proof. Cegg solve eq. Qed.

Lemma test_cr_of_ct (r : relation A) :
  (r^+)^? ⊆ r^*.
Proof. Cegg solve eq. Qed.

Lemma test_cr_of_cr (r : relation A) :
  (r^?)^? ⊆ r^?.
Proof. Cegg solve eq. Qed.

Lemma test_cr_of_rt (r : relation A) :
  (r^*)^? ⊆ r^*.
Proof. Cegg solve eq. Qed.

Lemma test_ct_of_ct (r : relation A) :
  (r^+)^+ ⊆ r^+.
Proof. Cegg solve eq. Qed.

Lemma test_ct_of_union_ct_l (r r' : relation A) :
  (r^+ ∪ r')^+ ⊆ (r ∪ r')^+.
Proof. Cegg solve eq. Qed.

Lemma test_ct_of_union_ct_r (r r' : relation A) :
  (r ∪ r'^+)^+ ⊆ (r ∪ r')^+.
Proof. Cegg solve eq. Qed.

Lemma test_ct_of_cr (r : relation A) :
  (r^?)^+ ⊆ r^*.
Proof. Cegg solve eq. Qed.

Lemma test_ct_of_rt (r : relation A) :
  (r^*)^+ ⊆ r^*.
Proof. Cegg solve eq. Qed.

Lemma test_rt_of_ct (r : relation A) :
  (r^+)^* ⊆ r^*.
Proof. Cegg solve eq. Qed.

Lemma test_rt_of_cr (r : relation A) :
  (r^?)^* ⊆ r^*.
Proof. Cegg solve eq. Qed.

Lemma test_rt_of_rt (r : relation A) :
  (r^*)^* ⊆ r^*.
Proof. Cegg solve eq. Qed.

Lemma test_cr_union_l (r r' : relation A) :
  (r ∪ r')^? ⊆ r^? ∪ r'.
Proof. Cegg solve eq. Qed.

Lemma test_cr_union_r (r r' : relation A) :
  (r ∪ r')^? ⊆ r ∪ r'^?.
Proof. Cegg solve eq. Qed.

Lemma test_cs_union (r r' : relation A) :
  (r ∪ r')^⋈ ⊆ r^⋈ ∪ r'^⋈.
Proof. Cegg solve eq. Qed.

Lemma test_crs_union (r r' : relation A) :
  (r ∪ r')^⋈? ⊆ r^⋈? ∪ r'^⋈?.
Proof. Cegg solve eq. Qed.

Lemma test_unionC (r r' : relation A) :
  r ∪ r' ⊆ r' ∪ r.
Proof. Cegg solve eq. Qed.

Lemma test_unionK (r : relation A) :
  r ∪ r ⊆ r.
Proof. Cegg solve eq. Qed.

Lemma test_union_false_r (r : relation A) :
  r ∪ ∅₂ ⊆ r.
Proof. Cegg solve eq. Qed.

Lemma test_union_false_l (r : relation A) :
  ∅₂ ∪ r ⊆ r.
Proof. Cegg solve eq. Qed.

Lemma cr_seq (r r' : relation A) : 
  r^? ⨾ r' ⊆ r' ∪ r ⨾ r'.
Proof. Cegg solve eq. Qed.

Lemma ct_seq_swap (r r' : relation A) :
  (r ⨾ r')⁺ ⨾ r ⊆ r ⨾ (r' ⨾ r)⁺.
Proof. Cegg solve eq. Qed.

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

    -- Добавление seq_rtE_r почему то убивает тактику, видимо где то 
    образовывается цикл.

    -- Понять, почему вот это убивает тактику:
    Lemma test_incorrect_lambda (r : relation A) :
      (fun _ _ => True) ;; r ⊆ (fun _ _ => False).
    Proof.
      Fail Cegg solve eq.
    Abort.

    -- Бесконечно порождающие: seq_union_l, seq_union_r, леммы
       про ассциативность;
*)