(*
 Copyright 2022 ZhengPu Shi
  This file is part of coq-matrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Signature of Vector Theory
  author    : ZhengPu Shi
  date      : 2022.06
  
  remark    :
  1. 《高等数学学习手册》徐小湛，p173
  2. Vector Calculus - Michael Corral
  3. https://github.com/coq/coq/blob/master/test-suite/success/Nsatz.v
     注意，这里有Coq库中定义的几何学形式化内容，包括点，平行，共线等。
  
*)

Require Export MatrixThySig.

(* ######################################################################### *)
(** * Signature of Vector theory *)

Module Type VectorThySig (F : FieldSig).
  
  (* ==================================== *)
  (** ** Matrix theory *)
  Declare Module MatrixThy : MatrixThySig F.
  Export MatrixThy.
  
  Open Scope X_scope.
  Open Scope mat_scope.
  Open Scope vec_scope.
  
  (* ==================================== *)
  (** ** Vector type *)
  Parameter vec : Type -> nat -> Type.
  
  (** 记号 *)
  Notation V n := (vec X n).
  
  (* ==================================== *)
  (** ** Vector equility *)
  Parameter veq_dec : forall {n} (v1 v2 : V n), {v1 = v2} + {v1 <> v2}.
  
  
  (* ==================================== *)
  (** ** Convert between tuples and vector *)
  Parameter t2v_2 : @T2 X -> V 2.
  Parameter t2v_3 : @T3 X -> V 3.
  Parameter t2v_4 : @T4 X -> V 4.
  
  Parameter v2t_2 : V 2 -> @T2 X.
  Parameter v2t_3 : V 3 -> @T3 X.
  Parameter v2t_4 : V 4 -> @T4 X.
  
  Parameter t2v_v2t_id_2 : forall (v : V 2), t2v_2 (v2t_2 v) = v.
  Parameter v2t_t2v_id_2 : forall (t : X * X), v2t_2 (t2v_2 t) = t.
  
  
  (* ==================================== *)
  (** ** Convert between list and vector *)
  Parameter l2v : forall {n} (l : list X), V n.
  Parameter v2l : forall {n}, V n -> list X.
  
  Parameter v2l_length : forall {n} (v : V n), length (v2l v) = n.
  
  Parameter v2l_l2v_id : forall {n} (l : list X),
    length l = n -> @v2l n (@l2v n l) = l.
  Parameter l2v_v2l_id : forall {n} (v : V n), 
    l2v (v2l v) = v.
  
  
  (* ==================================== *)
  (** ** Zero vector *)
  
  Parameter vec0 : forall n, V n.
  
  (** Assert that a vector is an zero vector. *)
  Parameter vzero : forall {n} (v : V n), Prop.

  (** Assert that a vector is an non-zero vector. *)
  Parameter vnonzero : forall {n} (v : V n), Prop.

  (** It is decidable that if a vector is zero vector. *)
  Parameter vzero_dec : forall {n} (v : V n), {vzero v} + {vnonzero v}.
  
  (** vec0 is equal to mat0 with column 1 *)
(*   Lemma vec0_eq_mat0 : forall n, vec0 n = mat0 n 1.
  Proof. lma. Qed. *)
  
  
  (* ==================================== *)
  (** ** algebra operations *)
  
  (** Mapping a vector *)
  Parameter vmap : forall {n} (v : V n) (f : X -> X), V n.
  
  (** Fold a vector *)
(*   Parameter vfold : forall {B : Type} {n} (v : V n) (f : X -> B) (b : B), B. *)
  
  (** Mapping two vectors *)
  Parameter vmap2 : forall {n} (v1 v2 : V n) (f : X -> X -> X), V n.
  
  (** Dot product of two vectors *)
  Parameter vdot : forall {n} (v1 v2 : V n), X.

  (** Addition of two vectors *)
  Parameter vadd : forall {n} (v1 v2 : V n), V n.
  Infix "+" := vadd : vec_scope.

  Parameter vadd_comm : forall {n} (v1 v2 : V n), (v1 + v2) = (v2 + v1).

  Parameter vadd_assoc : forall {n} (v1 v2 v3 : V n), 
    (v1 + v2) + v3 = v1 + (v2 + v3).

  Parameter vadd_0_l : forall {n} (v : V n), (vec0 n) + v = v.

  Parameter vadd_0_r : forall {n} (v : V n), v + (vec0 n) = v.

  (** Opposite of a vector *)
  Parameter vopp : forall {n} (v : V n), V n.
  Notation "- v" := (vopp v) : vec_scope.

  Parameter vadd_opp : forall {n} (v : V n), v + (- v) = vec0 n.
  
  Parameter vsub : forall {n} (v1 v2 : V n), V n.
  Infix "-" := vsub : vec_scope.

  (** Get element *)
  Parameter vnth : forall {n} (v : V n) (i : nat), X.

  (** Scalar multiplication *)
  Parameter vcmul : forall {n} (a : X) (v : V n), V n.
  Parameter vmulc : forall {n} (v : V n) (a : X), V n.
  
  Infix "c*" := vcmul : vec_scope.
  Infix "*c" := vmulc : vec_scope.
  
  Parameter vmulc_eq_vcmul : forall {n} a (v : V n), v *c a = a c* v.

  Parameter vcmul_assoc : forall {n} a b (v : V n), 
    a c* (b c* v) = (a * b) c* v.

  Parameter vcmul_perm : forall {n} a b (v : V n), 
    a c* (b c* v) = b c* (a c* v).

  Parameter vcmul_add_distr_l : forall {n} a b (v : V n), 
    (a + b) c* v = (a c* v) + (b c* v).

  Parameter vcmul_add_distr_r : forall {n} a (v1 v2 : V n), 
    a c* (v1 + v2) = (a c* v1) + (a c* v2).

  Parameter vcmul_1_l : forall {n} (v : V n), X1 c* v = v.

  Parameter vcmul_0_l : forall {n} (v : V n), X0 c* v = vec0 n.

  (** If two nonzero vectors has scalar multiplcation relation, 
    then the scalar coefficient must non-zero *)
  Parameter vec_eq_vcmul_imply_coef_neq0 : forall {n} (v1 v2 : V n) k,
    vnonzero v1 -> vnonzero v2 -> (v1 = k c* v2) -> k <> X0.
      
End VectorThySig.
