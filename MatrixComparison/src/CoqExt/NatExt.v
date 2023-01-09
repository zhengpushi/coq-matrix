(*
  purpose   : auxiliary library for nat.
  author    : ZhengPu Shi
  date      : 2021.05
*)

Require Export Nat Arith Lia.


(* ######################################################################### *)
(** * More properties for nat *)

(** a natural number must be odd or even *)
Lemma nat_split : forall (n : nat), exists (x : nat),
  n = 2 * x \/ n = 2 * x + 1.
Proof.
  induction n.
  - exists 0. auto.
  - destruct IHn. destruct H.
    + exists x. right. subst. lia.
    + exists (x+1). left. subst. lia.
Qed.

(** Two step induction principle for natural number *)
Theorem nat_ind2 : forall (P : nat -> Prop),
  (P 0) -> (P 1) -> (forall n, P n -> P (S (S n))) -> (forall n, P n).
Proof.
  intros. destruct (nat_split n). destruct H2; subst; induction x; auto.
  - replace (2 * S x) with (S (S (2 * x))); [apply H1; auto | lia].
  - replace (2 * S x + 1) with (S (S (2 * x + 1))); [apply H1; auto | lia].
Qed.

(** Connect induction principle between nat and list *)
Lemma ind_nat_list {A} : forall (P : list A -> Prop) ,
  (forall n l, length l = n -> P l) -> (forall l, P l).
Proof.
  intros. apply (H (length l)). auto.
Qed.



(* ######################################################################### *)
(** * Extension for nat from (Verified Quantum Computing). *)

  (* https://www.cs.umd.edu/~rrand/vqc/index.html *)
  
  (*******************************)
  (* Automation *)
  (*******************************)

  Lemma double_mult : forall (n : nat), (n + n = 2 * n).
  Proof. intros. lia. Qed.
  
  
Require Export Arith Lia Lra.
Require Import Setoid. (* R ==> R', Morphisms.respectful R R' *)
  Lemma pow_two_succ_l : forall x, 2^x * 2 = 2 ^ (x + 1).
  Proof. intros. rewrite Nat.mul_comm. rewrite <- Nat.pow_succ_r'. intuition. Qed.
  
  Lemma pow_two_succ_r : forall x, 2 * 2^x = 2 ^ (x + 1).
  Proof. intros. rewrite <- Nat.pow_succ_r'. intuition. Qed.
  
  Lemma double_pow : forall (n : nat), 2^n + 2^n = 2^(n+1). 
  Proof. intros. rewrite double_mult. rewrite pow_two_succ_r. reflexivity. Qed.
  
  Lemma pow_components : forall (a b m n : nat), a = b -> m = n -> a^m = b^n.
  Proof. intuition. Qed.

  Ltac unify_pows_two :=
    repeat match goal with
    (* NB: this first thing is potentially a bad idea, do not do with 2^1 *)
    | [ |- context[ 4%nat ]]                  => replace 4%nat with (2^2)%nat 
                                                 by reflexivity
    | [ |- context[ (0 + ?a)%nat]]            => rewrite Nat.add_0_l 
    | [ |- context[ (?a + 0)%nat]]            => rewrite Nat.add_0_r 
    | [ |- context[ (1 * ?a)%nat]]            => rewrite Nat.mul_1_l 
    | [ |- context[ (?a * 1)%nat]]            => rewrite Nat.mul_1_r 
    | [ |- context[ (2 * 2^?x)%nat]]          => rewrite <- Nat.pow_succ_r'
    | [ |- context[ (2^?x * 2)%nat]]          => rewrite pow_two_succ_l
    | [ |- context[ (2^?x + 2^?x)%nat]]       => rewrite double_pow 
    | [ |- context[ (2^?x * 2^?y)%nat]]       => rewrite <- Nat.pow_add_r 
    | [ |- context[ (?a + (?b + ?c))%nat ]]   => rewrite Nat.add_assoc 
    | [ |- (2^?x = 2^?y)%nat ]                => apply pow_components; try lia 
    end.

  (** Restoring Matrix dimensions *)
  Ltac is_nat_equality :=
    match goal with 
    | |- ?A = ?B => match type of A with
                  | nat => idtac
                  end
    end.

