Require Import Loader.
From hahn Require Import Hahn.

Section Example.

Variable A : Type.

Lemma test_with1 (r : relation A): 
  (r^?)^+ ;; ((r^?)^?)^+ ≡ (r^?)^+ ;; (r^?)^*.
Proof.
  Cegg solve eq. 
Qed.

Lemma test_with2 (r : relation A): 
  ((r^*)^?)^+ ;; ((r^?)^?)^+ ≡ (r^*)^* ;; (r^?)^*.
Proof.
  Cegg solve eq. 
Qed.

Lemma lol (r r' : relation A):
  ((((r^?)^+ ;; r^?) ;; (r^?)^+)^?)^+ ;; ((r^?)^?)^+ ≡ (((r^?)^+ ;; r^?) ;; r^*)^*.
Proof.
  (* Cegg solve eq. *)
  (* What type of (r^?). *)
  (* rewrite (ct_of_cr r) at 1. *)
  (* rewrite -> ct_of_cr at 1. *)

  (* rewrite ct_of_cr at 1. *)
  (* rewrite (ct_of_cr (((r^?)^+ ;; r^?) ;; (r^?)^+)) at 1. *)
  (* reflexivity. *)
Admitted.


Variable rf : A -> A -> Prop.
Variable mo : A -> A -> Prop.
Notation "'fr'" := (rf⁻¹ ;; mo).

Notation "'eco1'" := (rf ∪ mo ∪ fr)^+.
Notation "'eco2'" := (rf ∪ (mo ;; rf^?) ∪ (fr ;; rf^?)).

Record Wf :=
  { 
    mo_trans : mo ;; mo ⊆ mo ; 
    rf_mo : rf ;; mo ≡ ∅₂ ;
    rf_rf : rf ;; rf ≡ ∅₂ ;
    mo_rft : mo ;; rf⁻¹ ≡ ∅₂ ;
    mo_fr : mo ;; fr ≡ ∅₂ ; 
    fr_fr : fr ;; fr ≡ ∅₂ ;
  }.

Cegg config Wf.

Implicit Type WF : Wf.

Lemma kek WF (r : relation A):
  (fr ∪ mo) ;; (fr ∪ mo) ≡ fr ;; mo ∪ mo ;; mo.
Proof.
  rewrite -> seq_union_r.
  rewrite -> seq_union_l.
  rewrite -> fr_fr.
  rewrite -> mo_fr.
  rewrite -> union_false_l.
  rewrite -> union_false_l.
  rewrite -> seq_union_l.
  all: auto.

  (* Cegg solve eq. *)
Qed.

End Example.




