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

Record Wf :=
  { 
    kek_in_lol : kek ⊆ lol ;
  }.


Implicit Type WF : Wf.

Lemma bbb WF (r : relation A) :
  kek^* ;; kek^? ⊆ lol^*.
Proof.
  Cegg solve.
  apply inclusion_rt_rt.
  apply WF.
Qed.


Cegg config.

(* Variable cond : A -> Prop.
Definition eqv_rel1 : relation A := fun x y => x = y /\ cond x.

Print eqv_rel1.

Print relation.

Locate "⦗ _ ⦘".

Check eqv_rel.
Check ⦗fun _ => True⦘ = eqv_rel.

Print rt_cr.
Print seq_id_r.

Check (fun A A => Prop).

Locate "/\".

Lemma acyclic_empty (r : relation A) : 
  acyclic (fun _ _ => False) = True.
Proof. 


Lemma comm_govn (n m k l : nat) :
  ((m + n) + k) + l = (k + (m + n)) + l.
Proof.
  rewrite -> PeanoNat.Nat.add_comm.
  rewrite (PeanoNat.Nat.add_comm (m + n) k).
Abort.

Lemma kek (a b c : nat) : 
  a + b = c -> c + a = b -> b + c = a -> ((a + b) + (c + a)) + (b + c) = c + b + a.
Proof.
  intros H1 H2 H3.
  (* rewrite PeanoNat.Nat.add_comm at 2. *)
  Kek.
  (* rewrite H1.
  rewrite H2.
  rewrite H3.
  reflexivity. *)
Abort. 

Lemma test_kek (r : relation A) :
  r ;; r ⊆ r^*.
Proof.
  Cegg solve.
Abort.
*)

End Tests.

(* 
                    Проблемы: 
    -- Проблемы с rewrite в нескольких местах
    -- Rewrite сработал не там где надо 
*)