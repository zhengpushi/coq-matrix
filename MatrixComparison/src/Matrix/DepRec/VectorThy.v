(*
 Copyright 2022 ZhengPu Shi
  This file is part of coq-matrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Vector Theory based on Matrix of ListList
  author    : ZhengPu Shi
  date      : 2022.06
  
  remark    :
*)

Require Import VectorThySig.
Require Import DepRec.MatrixThy.

(* ######################################################################### *)
(** * Vector theory *)

Module VectorThy (F : FieldSig) <: VectorThySig F.
  
  (* ==================================== *)
  (** ** Matrix theory *)
  Module Export MatrixThy := MatrixThy F.

  
  (* ==================================== *)
  (** ** Vector type *)
  
(*   Declare Scope vec_scope.
  Delimit Scope vec_scope with V.
  Open Scope vec_scope. *)
  
  Definition vec X n := mat X n 1.
  Notation V n := (vec X n).
  
  
  (* ==================================== *)
  (** ** Vector equility *)
  Lemma veq_dec : forall {n} (v1 v2 : V n), {v1 = v2} + {not (v1 = v2)}.
  Proof. intros. apply meq_dec. Qed.
  
  
  (* ==================================== *)
  (** ** Convert between tuples and vector *)
  Definition t2v_2 t := let '(a,b) := t in @l2m 2 1 [[a];[b]].
  Definition t2v_3 t := let '(a,b,c) := t in @l2m 3 1 [[a];[b];[c]].
  Definition t2v_4 t := let '(a,b,c,d) := t in @l2m 4 1 [[a];[b];[c];[d]].
  
  Definition v2t_2 v := let d := @m2l 2 1 v in (
    hd X0 (hd [] d), 
    hd X0 (hd [] (tl d))
    ).
    
  Definition v2t_3 v := let d := @m2l 3 1 v in (
    hd X0 (hd [] d), 
    hd X0 (hd [] (tl d)), 
    hd X0 (hd [] (tl (tl d)))
    ).
    
  Definition v2t_4 v := let d := @m2l 4 1 v in (
    hd X0 (hd [] d), 
    hd X0 (hd [] (tl d)), 
    hd X0 (hd [] (tl (tl d))), 
    hd X0 (hd [] (tl (tl (tl d))))
    ).
  
  Lemma t2v_v2t_id_2 : forall (v : V 2), t2v_2 (v2t_2 v) = v.
  Proof.
    intros. unfold t2v_2,v2t_2.
    rewrite <- l2m_m2l_id. apply meq_iff. simpl.
    repeat (try f_equal; auto).
  Qed.
  
  Lemma v2t_t2v_id_2 : forall (t : X * X), v2t_2 (t2v_2 t) = t.
  Proof.
    intros. destruct t. simpl. unfold v2t_2. f_equal.
  Qed.
  
  
  (* ==================================== *)
  (** ** Convert between list and vector *)
  
  Definition v2l {n} (v : V n) : list X := hdc X0 (mat_data v).
  
  Definition l2v {n} (l : list X) : V n := l2m (cvt_row2col l).
  
  
  Lemma v2l_length : forall {n} (v : V n), length (v2l v) = n.
  Proof.
    intros. unfold v2l.
    rewrite hdc_length. destruct v. simpl. auto.
  Qed.
  
  Lemma v2l_l2v_id : forall {n} (l : list X),
    length l = n -> @v2l n (@l2v n l) = l.
  Proof.
    intros. unfold v2l,l2v. simpl. Admitted.
  
  Lemma l2v_v2l_id : forall {n} (v : V n), 
    l2v (v2l v) = v.
  Proof.
    intros. unfold v2l,l2v. simpl. Admitted.
  
  
  (* ==================================== *)
  (** ** Zero vector *)
  Definition vec0 {n} : V n := mat0 n 1.

  (** Assert that a vector is an zero vector. *)
  Definition vzero {n} (v : V n) : Prop := v = vec0.

  (** Assert that a vector is an non-zero vector. *)
  Definition vnonzero {n} (v : V n) : Prop := ~(vzero v).
  
  (** vec0 is equal to mat0 with column 1 *)
  Lemma vec0_eq_mat0 : forall n, vec0 = mat0 n 1.
  Proof. intros. apply meq_iff. auto. Qed.

  (** It is decidable that if a vector is zero vector. *)
  Lemma vzero_dec : forall {n} (v : V n), {vzero v} + {vnonzero v}.
  Proof. intros. apply meq_dec. Qed.
  
  
  (* ======================================================================= *)
  (** ** algebra operations *)
  
  (** 一个向量的映射 *)
  Definition vmap {n} (v : V n) f : V n := mmap f v.
  
  (** 一个向量的fold操作 *)
(*   Definition vfold : forall {B : Type} {n} (v : V n) (f : X -> B) (b : B), B. *)
  
  (** 两个向量的映射 *)
  Definition vmap2 {n} (v1 v2 : V n) f : V n := mmap2 f v1 v2.
  
  (* 两个向量的点积。这里用矩阵乘法来定义点积，而我们之前是用点积来定义乘法 *)
  Definition vdot {n : nat} (X : V n) (B : V n) :=
    scalar_of_mat (@mmul 1 n 1 (mtrans X) B).

  (** Addition of vector *)
  Definition vadd {n} (v1 v2 : V n) : V n := v1 + v2.
  Infix "+" := vadd : vec_scope.

  Lemma vadd_comm : forall {n} (v1 v2 : V n), v1 + v2 = v2 + v1.
  Proof. intros. apply madd_comm. Qed.

  Lemma vadd_assoc : forall {n} (v1 v2 v3 : V n), 
    (v1 + v2) + v3 = v1 + (v2 + v3).
  Proof. intros. apply madd_assoc. Qed.

  Lemma vadd_0_l : forall {n} (v : V n), vec0 + v =  v.
  Proof. intros. apply (@madd_0_l n 1). Qed.

  Lemma vadd_0_r : forall {n} (v : V n), v + vec0 = v.
  Proof. intros. apply (@madd_0_r n 1). Qed.

  (** Opposite of vector *)
  Definition vopp {n} (v : V n) : V n := -v.
  Notation "- v" := (vopp v) : vec_scope.

  Lemma vadd_opp : forall {n} (v : V n), v + (- v) = vec0.
  Proof. intros. apply (@madd_opp n 1). Qed.

  (** Substraction of vector *)
  Definition vsub {n} (v1 v2 : V n) : V n := v1 - v2.
  Infix "-" := vsub : vec_scope.

  (** Get element of vector *)
  Definition vnth {n} (v : V n) i : X := @mnth n 1 v i 0.
  
(*   Notation "v .[ i ]" := (vnth v i) (at level 30) : vec_scope. *)
  
(*   Definition scalar_of_mat (m : M 1 1) := mnth m 0 0. *)

  (** Scalar production *)
  Definition vcmul {n} a (v : V n) : V n := a c* v.
  Definition vmulc {n} (v : V n) a : V n := v *c a.

  Lemma vmulc_eq_vcmul : forall {n} a (v : V n), v *c a = a c* v.
  Proof. intros. rewrite mmulc_eq_mcmul. easy. Qed.

  Lemma vcmul_assoc : forall {n} a b (v : V n), 
    a c* (b c* v) = (a * b)%X c* v.
  Proof. intros. rewrite mcmul_assoc. easy. Qed.

  Lemma vcmul_perm : forall {n} a b (v : V n), 
    a c* (b c* v) = b c* (a c* v).
  Proof. intros. rewrite mcmul_perm. easy. Qed.

  Lemma vcmul_add_distr_l : forall {n} a b (v : V n), 
    (a + b)%X c* v = (a c* v) + (b c* v).
  Proof. intros. rewrite mcmul_add_distr_r. easy. Qed.

  Lemma vcmul_add_distr_r : forall {n} a (v1 v2 : V n), 
    a c* (v1 + v2) = (a c* v1) + (a c* v2).
  Proof. intros. unfold vadd. rewrite mcmul_add_distr_l. easy. Qed.

  Lemma vcmul_1_l : forall {n} (v : V n), X1 c* v = v.
  Proof. intros. rewrite mcmul_1_l. easy. Qed.

  Lemma vcmul_0_l : forall {n} (v : V n), X0 c* v = vec0.
  Proof. intros. rewrite mcmul_0_l. easy. Qed.

  (** 非零向量是k倍关系，则系数k不为0 *)
  Lemma vec_eq_vcmul_imply_coef_neq0 : forall {n} (v1 v2 : V n) k,
    vnonzero v1 -> vnonzero v2 -> v1 = k c* v2 -> k <> X0.
  Proof.
    intros. intro. subst. rewrite vcmul_0_l in H. destruct H. easy.
  Qed.
  
  
  (* ==================================== *)
  (** ** 2-dim vector operations *)

  (** 2维向量的“长度”，这里不是欧式距离，而是欧式距离的平方，为了方便计算 *)
  Definition vlen2 (v : V 2) : X :=
    let '(x,y) := v2t_2 v in
      (x * x + y * y)%X.
  
  
  (* ==================================== *)
  (** ** 3-dim vector operations *)

  (** 3维向量的“长度”，这里不是欧式距离，而是欧式距离的平方，为了方便计算 *)
  Definition vlen3 (v : V 3) : X :=
    let '(x,y,z) := v2t_3 v in
      (x * x + y * y + z * z)%X.
      
  (** V3的点积 *)
  Definition vdot3 (v0 v1 : V 3) : X :=
    let '(a0,b0,c0) := v2t_3 v0 in
    let '(a1,b1,c1) := v2t_3 v1 in
      (a0 * a1 + b0 * b1 + c0 * c1)%X.
  
End VectorThy.


(* ######################################################################### *)
(** * Vector on R *)
Module VectorR := VectorThy (FieldR.FieldDefR).


(* ######################################################################### *)
(** * Test of VectorR *)
Module VectorR_test.

  Import FieldR.
  Import VectorR.
  
  Open Scope mat_scope.
  
  Definition v1 := @l2v 3 [1;2;3].
  Definition v2 := @l2v 3 [4;5;6].
  Example vdot_ex1 : vdot v1 v2 = (4+10+18)%R.
  Proof. compute. ring. Qed.
  
End VectorR_test.

