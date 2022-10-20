(*
  purpose   : Isomorphism Theory.
  author    : ZhengPu Shi
  date      : 2022.07
  
  ref:
  1. https://blog.csdn.net/grb819/article/details/111745405
*)

Require Export BasicConfig.

(** Part I : reflexive, symmetric, transitive *)

(** Isomorphism mapping is reflexive *)
Theorem isomorphism_refl : forall {A B} (fa : A -> A -> A) (fb : B -> B -> B), 
  isomorphism fa fb -> isomorphism fa fb.
Proof. intros. auto. Qed.

(** Isomorphism mapping is symmetric *)
Theorem isomorphism_sym : forall {A B} (fa : A -> A -> A) (fb : B -> B -> B), 
  isomorphism fa fb -> isomorphism fb fa.
Proof.
  intros. destruct H as [phi [Hhomo Hbij]].
  pose (proj1_sig (inversefun_of_bij phi Hbij)).
  Admitted.

Theorem isomorphism_trans : forall {A B C} (fa : A -> A -> A)
  (fb : B -> B -> B) (fc : C -> C -> C),
  isomorphism fa fb -> isomorphism fb fc -> isomorphism fa fc.
Proof.
  Admitted.

(** Part II : inheritance of commutative, associative, cancel *)

(** Note that, here is iff, it is strong than the case in homomorphism *)
Theorem isomor_keep_comm : forall {A B} (fa : A -> A -> A)
  (fb : B -> B -> B) (H1 : isomorphism fa fb),
  commutative fa <-> commutative fb.
Proof.
  Admitted.

Theorem isomor_keep_assoc : forall {A B} (fa : A -> A -> A)
  (fb : B -> B -> B) (H1 : isomorphism fa fb),
  associative fa <-> associative fb.
Proof.
  Admitted.

Theorem isomor_keep_cancel_left : forall {A B} (fa : A -> A -> A)
  (fb : B -> B -> B) (H1 : isomorphism fa fb),
  cancel_left fa <-> cancel_left fb.
Proof.
  Admitted.

Theorem isomor_keep_cancel_right : forall {A B} (fa : A -> A -> A)
  (fb : B -> B -> B) (H1 : isomorphism fa fb),
  cancel_right fa <-> cancel_right fb.
Proof.
  Admitted.

(** Part III : distributive law *)

Theorem isomor_keep_distr_left : forall {A B} (fa ga : A -> A -> A)
  (fb gb : B -> B -> B) (H1 : isomorphism2 fa ga fb gb),
  distributive_left fa ga <-> distributive_left fb gb.
Proof.
  Admitted.

Theorem isomor_keep_distr_right : forall {A B} (fa ga : A -> A -> A)
  (fb gb : B -> B -> B) (H1 : isomorphism2 fa ga fb gb),
  distributive_right fa ga <-> distributive_right fb gb.
Proof.
  Admitted.
