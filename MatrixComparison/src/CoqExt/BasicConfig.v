(*
  purpose   : Basic configuration (Library, Notations, Warning, etc.)
  author    : ZhengPu Shi
  date      : 2022.06
  
  remark    :
  1. Basic libraries in whole project
  3. Reserved notations for consistence.
    https://coq.inria.fr/distrib/V8.13.2/refman/language/coq-library.html 
  3. Eliminate some warning.  
    https://coq.inria.fr/distrib/V8.13.2/refman/user-extensions/
    syntax-extensions.html?highlight=warning
  4. Customized tactics.
*)


(* ######################################################################### *)
(** * Basic libraries *) 

Require Export Coq.Classes.Morphisms.     (* respectful, ==> *)
Require Export Coq.Setoids.Setoid.        (*  *)
Require Export Coq.Classes.SetoidTactics. (* add_morphism_tactic *)
Require Export Coq.Relations.Relations.   (* equivalence *)
Require Export Coq.Bool.Bool.             (* reflect *)
Require Export Ring.                      (* ring *)
Require Export Field.                     (* field *)

Require Import Coq.Logic.Description. (* constructive_definite_description *)
Require Export Coq.Logic.Classical.
Require Export Coq.Logic.FunctionalExtensionality.


(* ######################################################################### *)
(** * Reserved Notations *)

(** Reserved Notations, to keep same precedence and associativity *)
Reserved Infix    "=="      (at level 70, no associativity).
Reserved Notation "a != b"  (at level 70, no associativity).
Reserved Infix    "=?"      (at level 70, no associativity).
Reserved Infix    "+"       (at level 50, left associativity).
Reserved Infix    "-"       (at level 50, left associativity).
Reserved Infix    "*"       (at level 40, left associativity).
Reserved Infix    "/"       (at level 40, left associativity).
Reserved Infix    "c*"      (at level 40, left associativity).
Reserved Infix    "*c"      (at level 40, left associativity).
Reserved Notation "- a"     (at level 35, right associativity).
Reserved Notation "/ a"     (at level 35, right associativity).
Reserved Notation "a 'ᵀ'"   (at level 35).
(* this level is consistent with Mathcomp.ssreflect.ssrnotations.v *)
Reserved Notation "v .[ i ]"
   (at level 2, left associativity, format "v .[ i ]").


(* ######################################################################### *)
(** * Eliminate Warning. *)

(* Export Set Warnings "-notation-overridden". *)


(* ######################################################################### *)
(** * Customized tactics *)

(** ** Tactics with a short name *)

Global Ltac gd k := generalize dependent k.

(* repeat split *)
Ltac ssplit := 
  repeat 
  match goal with
  | |- _ /\ _ => split
  end.



(* ######################################################################### *)
(** * Global notations *)

(* this level is consistent with coq.ssr.ssrbool.v *)
Notation "~~ b" := (negb b) (at level 35, right associativity) : bool_scope.


(* ######################################################################### *)
(** * Global coercions *)

(** bool to Prop *)
Definition is_true (b : bool) : Prop := b = true.
Coercion is_true : bool >-> Sortclass.

Goal true.
apply eq_refl. Qed.

Goal ~~false.
simpl. apply eq_refl. Qed.

Example eqnP (n m : nat) : reflect (n = m) (Nat.eqb n m).
Proof.
  gd m. induction n; intros [|m]; simpl; try constructor; auto.
  destruct IHn with m; subst; constructor; auto.
Qed.


(* ######################################################################### *)
(** * General propeties of algebraic structures *)

Section general_props.

  Context {A B : Type}.
  Variable fa ga : A -> A -> A.
  Infix "+" := fa.
  Infix "*" := ga.
  Variable fb : B -> B -> B.
  Infix "⊕" := fb (at level 50).

  Definition decidable := forall (a b : A), {a = b} + {a <> b}.

  Definition associative := forall a b c, a + (b + c) = (a + b) + c.

  Definition commutative := forall a b, a + b = b + a.
  
  Definition distributive_left := forall a b c, (a + b) * c = a * c + b * c.
  Definition distributive_right := forall a b c, a * (b + c) = a * b + a * c.
  
  Definition cancel_left := forall a b c, a + b = a + c -> b = c.
  Definition cancel_right := forall a b c, a + c = b + c -> a = b.

  Definition injective (phi : A -> B) := forall (a1 a2 : A),
    a1 <> a2 -> phi a1 <> phi a2.
  
  (** Second form of injective *)
  Definition injective_form2 (phi : A -> B) := forall (a1 a2 : A),
    phi a1 = phi a2 -> a1 = a2.
  
  (** These two forms are equal *) 
  Lemma injective_eq_injective_form2 (phi : A -> B) : 
    injective phi <-> injective_form2 phi.
  Proof.
    split; intros H1 a1 a2 H2.
    - pose (H1 a1 a2) as H3.
      apply imply_to_or in H3. destruct H3.
      + unfold not in H. apply NNPP in H. auto.
      + easy.
    - pose (H1 a1 a2) as H3.
      apply imply_to_or in H3. destruct H3; auto.
  Qed.
  
  Definition surjective (phi : A -> B) := forall (b : B),
    (exists (a : A), phi a = b).

  Definition bijective (phi : A -> B) := 
    injective phi /\ surjective phi.
  
  (** phi is a homomorphic mapping from <A,+> to <B,⊕> *)
  Definition homomorphic (phi : A -> B) : Prop :=
    forall (a b : A), phi (a + b) = (phi a) ⊕ (phi b).
  
  (** phi is a homomorphic and injective mapping *)
  Definition homo_inj (phi : A -> B) : Prop :=
    homomorphic phi /\ injective phi.
  
  (** phi is a homomorphic and surjective mapping *)
  Definition homo_surj (phi : A -> B) : Prop :=
    homomorphic phi /\ surjective phi.

End general_props.

(** If there exist a homomorphic and surjective mapping from <A,+> to <B,⊕>, 
  then we said <A,+> and <B,⊕> is homomorphism *)
Definition homomorphism {A B : Type} (fa : A -> A -> A) (fb : B -> B -> B) := 
  exists (phi : A -> B), homo_surj fa fb phi.

(** If there exist two homomorphic and surjective mapping from <A,+> to <B,⊕> 
  and from <A,*> to <B,⊗>, then we said <A,+,*> and <B,⊕,⊗> is homomorphism *)
Definition homomorphism2 {A B : Type} (fa ga : A -> A -> A) 
  (fb gb: B -> B -> B) := 
  exists (phi : A -> B), homo_surj fa fb phi /\ homo_surj ga gb phi.

(** If there exist a homomorphic and bijective mapping from <A,+> to <B,⊕>, 
  then we said <A,+> and <B,⊕> is isomorphism *)
Definition isomorphism {A B : Type} (fa : A -> A -> A) (fb : B -> B -> B) := 
  exists (phi : A -> B), homomorphic fa fb phi /\ bijective phi.

(** If there exist two homomorphic and bijective mapping from <A,+> to <B,⊕> 
  and from <A,*> to <B,⊗>, then we said <A,+,*> and <B,⊕,⊗> is isomorphism *)
Definition isomorphism2 {A B : Type} (fa ga : A -> A -> A) 
  (fb gb: B -> B -> B) := 
  exists (phi : A -> B), 
  homomorphic fa fb phi /\ homomorphic ga gb phi /\ bijective phi.

(* sig version. Type *)
Definition inversefun_of_bij {A B : Type} (phi : A -> B) (Hbij : bijective phi)
  : {psi : B -> A | 
    (forall a : A, psi (phi a) = a) /\
    (forall b : B, phi (psi b) = b)}.
Proof.
  destruct Hbij as [Hinj Hsurj].
  apply injective_eq_injective_form2 in Hinj.
  (* ref: https://stackoverflow.com/questions/62464821/
    how-to-make-an-inverse-function-in-coq
    TIPS: ex is Prop, sig is Type. this axiom construct a sig with ex. *)
  apply constructive_definite_description.
  assert (H : forall b, exists! a, phi a = b).
  { intros b.
    destruct (Hsurj b) as [a Ha]. exists a. split; auto.
    intros a' Ha'. apply Hinj. subst. auto. }
  exists (fun b => proj1_sig (constructive_definite_description _ (H b))).
  split. (* unique *)
  - split.
    + intros a. destruct (constructive_definite_description). simpl.
      apply Hinj. auto.
    + intros b. destruct (constructive_definite_description). simpl.
      auto.
  - intros g [H1 H2].
    apply functional_extensionality.
    intros b. destruct (constructive_definite_description). simpl.
    rewrite <- e. rewrite H1. auto.
Defined.

(* ex version. Prop *)
(* Definition inversefun_of_bij_Prop {A B : Type} (phi : A -> B) 
  (Hbij : bijective phi)
  : exists (psi : B -> A),
    (forall a : A, psi (phi a) = a) /\
    (forall b : B, phi (psi b) = b).
Proof.
  constructor.
  Check (exists g, (fun 
  eexists. split.
  - intros a. destruct Hbij as [Hinj Hsurj].
    destruct (Hsurj (phi a)). *)


(* ######################################################################### *)
(** * Usually used scopes *)

(** Scope for matrix type *)
Declare Scope mat_scope.
Delimit Scope mat_scope with M.
Open Scope M.

(** Scope for vector type *)
Declare Scope vec_scope.
Delimit Scope vec_scope with V.
Open Scope vec_scope.


