(*
 Copyright 2022 ZhengPu Shi
  This file is part of coq-matrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix implemented with Fin Function
  author    : ZhengPu Shi
  date      : 2021.12
  
  remark    :
  1. reference:  
  https://math-comp.github.io/htmldoc_1_14_0/mathcomp.algebra.matrix.html#matrix
  2. change it to Functor version, which can support multiple Base Type.
  3. especially we want to use RingType as Base Type, because lots of operations 
    related to Base Type could be omitted. 
*)



(** The library all_algebra contain 'matrix' formalization *)
From mathcomp Require Import all_ssreflect all_algebra.

Require Export MatrixThySig.
(* Require Export ListListExt.
Require Export FieldTypeR.
Require Import MatrixSig. *)

(* Require Export Fin.
Require Export Arith.
Require Export Lia.
Require Export List.
Export ListNotations. *)


(* ######################################################################### *)
(** * Matrix theory *)
Module MatrixThy (F : FieldSig) <: MatrixThySig F.

  Module Export FieldThyInst := FieldThy F.

  Open Scope X_scope.
  Open Scope mat_scope.

  (** package X to ringType structure, to enable X be used as carrier type 
    of MathComp.matrix. 
    We must construct the required hierarchy one by one, otherwise, the later 
    structure will fail.
    For example, choiceType need a eqType canonical declaration, and so on *)
  Module Export X_carrier_of_matrix.
    
    (* eqType *)
    Section eqType.
      (** reflect (x1 = x2) (x1 =? x2) *)
      Let X_eqbP : Equality.axiom Xeqb.
      Proof.
        hnf. intros. destruct (Xeqdec x y) as [H|H]; auto.
        - apply Xeqb_true_iff in H. rewrite H. constructor.
          apply Xeqb_true_iff. auto.
        - apply Xeqb_false_iff in H. rewrite H. constructor.
          apply Xeqb_false_iff. auto.
      Qed.
    
      Let X_eqMixin := EqMixin X_eqbP.
      Canonical X_eqType := Eval hnf in EqType X X_eqMixin.
    End eqType.
    
    (* choiceType *)
    Section choiceType.
      Import Countable.

      Definition pickle (x:X) := 0%nat.
      Definition unpickle (n:nat) : option X := None.
      Definition pcancel : pcancel pickle unpickle. Admitted.
      Definition X_choiceType_mixin_of : mixin_of X :=
        Mixin pcancel.
      
      Let X_choiceMixin := ChoiceMixin X_choiceType_mixin_of.
      Canonical X_choiceType := ChoiceType X X_choiceMixin.
    End choiceType.
    
    (* zmodType *)
    Section zmodType.
      Import ssrfun.
      
      Let Xadd_assoc : associative Xadd. Proof. hnf;intros;ring. Qed.
      Let Xadd_comm : commutative Xadd. Proof. hnf;intros;ring. Qed.
      Let Xadd_left_id : left_id X0 Xadd. Proof. hnf;intros;ring. Qed.
      Let Xadd_left_inv : left_inverse X0 Xopp Xadd. Proof. hnf;intros;ring. Qed.
      
      Let X_zmodMixin := ZmodMixin Xadd_assoc Xadd_comm Xadd_left_id 
        Xadd_left_inv.
      Canonical X_zmodType := Eval hnf in ZmodType _ X_zmodMixin.
    End zmodType.
    
    (* ringType *)
    Section ringType.
      Import ssrfun.
      
      Let Xmul_assoc : associative Xmul. Proof. hnf;intros;ring. Qed.
      Let Xmul_left_id : left_id X1 Xmul. Proof. hnf;intros;ring. Qed.
      Let Xmul_right_id : right_id X1 Xmul. Proof. hnf;intros;ring. Qed.
      Let Xmul_left_distr : left_distributive Xmul Xadd.
      Proof. hnf;intros;ring. Qed.
      Let Xmul_right_distr : right_distributive Xmul Xadd.
      Proof. hnf;intros;ring. Qed.
      
      (* 1 != 0%R *)
      Let X_1_neq_0 : negb (eq_op X1 (GRing.zero X_zmodType)).
      Proof. cbv. assert (H:Xeqb X1 X0 = false); [|rewrite H; auto].
        apply Xeqb_false_iff. apply X1_neq_X0.
      Qed.
      
      Let X_ringMixin := RingMixin Xmul_assoc Xmul_left_id Xmul_right_id
        Xmul_left_distr Xmul_right_distr X_1_neq_0.
      Canonical X_ringType := Eval hnf in RingType _ X_ringMixin.
      
    End ringType.
    
  End X_carrier_of_matrix.
  
  

  (** Matrix type *)
  
  (* details about Mathcomp.matrix is complex *)
(*   Print matrix.       (* Inductive matrix := Matrix (_:finfun_of) *)
  Print finfun_of.    (* Inductive finfun_of := FinfunOf (_:finfun_on) *)
  Print finfun_on.    (* Inductive finfun_on := finfun_nil | finfun_cons *)
 *)  
  Definition mat X (r c : nat) := matrix X r c.
  Notation M r c := (@mat X r c).
  
(*   (** Equality of matrix, iff, equality of the matrix data *)
  Lemma meq_iff : forall (r c : nat) (m1 m2 : M r c), 
    mat_data m1 = mat_data m2 <-> m1 = m2.
  Proof.
    intros. apply meq_iff.
  Qed.
  
  (** Not equal, iff, the data is not equal *)
  Lemma meq_iff_not : forall (r c : nat) (m1 m2 : M r c), 
    mat_data m1 <> mat_data m2 <-> m1 <> m2.
  Proof.
    intros. apply meq_iff_not.
  Qed. *)
  (** The equality is decidable *)
  Lemma meq_dec : forall {r c} (m1 m2 : M r c), {m1 = m2} + {m1 <> m2}.
  Proof.
    intros. apply (@eq_comparable (matrix_eqType X_eqType r c)).
  Qed.

  (** Mathcomp issue: leq (S a) b <-> Nat.ltb a b *)
  (* leq 是Mathcomp定义的自然数比较，Nat.ltb是Coq标准库定义的 *)
  Fact mathcomp_leq_iff_ltb : forall a b : nat, leq (S a) b <-> Nat.ltb a b.
  Proof.
    intros.
    Admitted. (* 稍后再证，这个不是很难，只是很繁琐 *)
    (* 由于两个定义差异较大，不便于直接证明，可借助归纳定义的关系 le 来证明。
      将 Nat.ltb 转换到 le，使用 Nat.ltb_spec，
      将 leq 转换到 le，使用 leP.
    
    Nat.ltb_spec : forall x y : nat, BoolSpec (lt x y) (le y x) (Nat.ltb x y)
      当 lt x y 为真，Nat.ltb x y = true
      当 lt x y 为假，Nat.ltb x y = false
    leP: forall {m n : nat}, reflect (le m n) (leq m n)
      当 le m n 为真，leq m n = true
      当 le m n 为假，leq m n = false *)
(*     split; intros.
    { destruct (@leP a b). 2:{ 
    destruct (Nat.ltb_spec a b).
    { 
    destruct (@leP a b), (Nat.ltb_spec a b).
    {  a b). *)
    
  (** Get element of a matrix *)  
  Definition mnth' {r c} (m : M r c) (ri ci : nat) : X.
  Proof.
    destruct (ri <? r) eqn:H1, (ci <? c) eqn:H2.
    { apply mathcomp_leq_iff_ltb in H1,H2.  (* 类型转换 *)
      pose (ri' := @Ordinal r ri H1).
      pose (ci' := @Ordinal c ci H2).
      exact (m ri' ci'). }
    all: exact X0.  (* 所有其他情形都输出 X0 *)
  Defined.
  
  Definition mnth {r c} (m : M r c) (ri ci : nat) : X.
    destruct (ri < r) eqn:H1, (ci < c) eqn:H2.
    { exact (m (@Ordinal r ri H1) (@Ordinal c ci H2)). }
    all: exact X0.
  Defined.
  
  Lemma meq_iff_mnth : forall {r c : nat} (m1 m2 : M r c),
    m1 = m2 <-> 
    (forall ri ci (Hri : lt ri r) (Hci : lt ci c),
      mnth m1 ri ci = mnth m2 ri ci).
  Proof.
    intros. split; intros.
    { destruct (ri < r) eqn:H1, (ci < c) eqn:H2.
      { unfold mnth.
      Admitted.
  
  (** Create specific matrix *)
  Definition mk_mat_1_1 (a11 : X) : @M 1 1 := matrix_of_fun_def 
    (fun i j => match i,j with (* i : ordinal_finType 1 *)
      | Ordinal 0 _, Ordinal 0 _ => a11 
      | _,_ => X0 
      end).
  Definition mk_mat_3_1 (a1 a2 a3 : X) : @M 3 1 := matrix_of_fun_def 
    (fun i j => match i,j with
      | Ordinal 0 _, Ordinal 0 _ => a1 
      | Ordinal 1 _, Ordinal 0 _ => a2 
      | Ordinal 2 _, Ordinal 0 _ => a3 
      | _,_ => X0 
      end).
  Definition mk_mat_3_3 (a11 a12 a13 a21 a22 a23 a31 a32 a33 : X) : @M 3 3 
    := matrix_of_fun_def 
    (fun i j => match i,j with
      | Ordinal 0 _, Ordinal 0 _ => a11 
      | Ordinal 0 _, Ordinal 1 _ => a12 
      | Ordinal 0 _, Ordinal 2 _ => a13
      | Ordinal 1 _, Ordinal 0 _ => a21 
      | Ordinal 1 _, Ordinal 1 _ => a22 
      | Ordinal 1 _, Ordinal 2 _ => a23 
      | Ordinal 2 _, Ordinal 0 _ => a31 
      | Ordinal 2 _, Ordinal 1 _ => a32 
      | Ordinal 2 _, Ordinal 2 _ => a33 
      | _,_ => X0 
      end).
  Definition mk_mat_2_2 (a11 a12 a21 a22 : X) : @M 2 2 
    := matrix_of_fun_def 
    (fun i j => match i,j with
      | Ordinal 0 _, Ordinal 0 _ => a11 
      | Ordinal 0 _, Ordinal 1 _ => a12 
      | Ordinal 1 _, Ordinal 0 _ => a21 
      | Ordinal 1 _, Ordinal 1 _ => a22 
      | _,_ => X0 
      end).
  
  (** Zero matrix *)
  Definition mat0 r c : M r c
    := matrix_of_fun_def (fun i j => X0).
  
  (** X matrix is a nonzero matrix *)
  Definition matnonzero {r c} (m : M r c) : Prop := m <> mat0 r c.
  
  (** Unit matrix *)
  Definition mat1 n : M n n
    := matrix_of_fun_def (fun i j => if (i == j) then X1 else X0).
  
  (** Mapping of a matrix *)
  Definition mmap {r c} (f : X -> X) (m : M r c) : M r c
    := matrix_of_fun_def (fun i j => f (m i j)).
  
  (** Mapping of two matrices *)
  Definition mmap2 {r c} (f : X -> X -> X) (m1  m2 : M r c) : M r c
    := matrix_of_fun_def (fun i j => f (m1 i j) (m2 i j)).
  
  Lemma mmap2_comm : forall {r c} (f : X -> X -> X)
    (f_comm : forall a b : X, f a b = f b a) (m1 m2 : M r c), 
    mmap2 f m1 m2 = mmap2 f m2 m1.
  Proof.
    intros.
    Admitted.
  
  Lemma mmap2_assoc : forall {r c} (f : X -> X -> X)
    (f_assoc : forall a b c, f a (f b c) = f (f a b) c) (m1 m2 m3 : M r c), 
    mmap2 f (mmap2 f m1 m2) m3 = mmap2 f m1 (mmap2 f m2 m3).
  Proof.
    intros.
    Admitted.
  
  (** Addition of matrix *)
  Definition madd {r c} (m1 m2 : M r c)
    := matrix_of_fun_def (fun i j => Xadd (m1 i j) (m2 i j)).
  Global Notation "m1 + m2" := (madd m1 m2) : mat_scope.
  
  Lemma madd_comm : forall {r c} (m1 m2 : M r c), m1 + m2 = m2 + m1.
  Proof.
    Admitted.
  
  Lemma madd_assoc : forall {r c} (m1 m2 m3 : M r c),
    (m1 + m2) + m3 = m1 + (m2 + m3).
  Proof.
    Admitted.
  
  Lemma madd_0_l : forall {r c} (m : M r c), (mat0 r c) + m = m.
  Proof.
    Admitted.
  
  Lemma madd_0_r : forall {r c} (m : M r c), m + (mat0 r c) = m.
  Proof.
    Admitted.
  
  (** Opposite of matrix *)
  Definition mopp {r c} (m : M r c) : M r c
    := matrix_of_fun_def (fun i j => Xopp (m i j)).
  Global Notation "- m" := (mopp m) : mat_scope.
    
  Lemma mopp_opp : forall {r c} (m : M r c), - - m = m.
  Proof.
    Admitted.
  
  Lemma mopp_exchange : forall {r c} (m1 m2 : M r c), 
    -m1 = m2 <-> m1 = -m2.
  Proof.
    Admitted.
  
  Lemma mopp_mat0 : forall {r c}, - (mat0 r c) = mat0 r c.
  Proof.
    Admitted.
  
  Lemma madd_opp : forall {r c} (m : M r c), m + (-m) = mat0 r c.
  Proof.
    Admitted.
  
  Definition msub {r c} (m1 m2 : M r c)
    := matrix_of_fun_def (fun i j => Xadd (m1 i j) (Xopp (m2 i j))).
  Global Notation "m1 - m2" := (msub m1 m2) : mat_scope.
  
  Lemma msub_comm : forall {r c} (m1 m2 : M r c), m1 - m2 = - (m2 - m1).
  Proof.
    Admitted.
  
  Lemma msub_assoc : forall {r c} (m1 m2 m3 : M r c), 
    msub (msub m1 m2) m3 = msub m1 (madd m2 m3).
  Proof.
    Admitted.
    
  Lemma msub_0_l : forall {r c} (m : M r c), msub (mat0 r c) m = mopp m.
  Proof.
    Admitted.
  
  Lemma msub_0_r : forall {r c} (m : M r c), msub m (mat0 r c) = m.
  Proof.
    Admitted.
  
  Lemma msub_self : forall {r c} (m : M r c), msub m m = (mat0 r c).
  Proof.
    Admitted.
  
  (** 矩阵数乘 *)
  Definition mcmul {r c} (a : X) (m : M r c) : M r c
    := matrix_of_fun_def (fun i j => Xmul a (m i j)).
    
  Global Notation "a c* m" := (mcmul a m) : mat_scope.
  
  Definition mmulc {r c} (m : M r c) (a : X) : M r c
    := matrix_of_fun_def (fun i j => Xmul (m i j) a).
  
  Global Notation "m *c a" := (mmulc m a) : mat_scope.
  
  Lemma mmulc_eq_mcmul : forall {r c} (a : X) (m : M r c), 
    mmulc m a = mcmul a m.
  Proof.
    Admitted.

  Lemma mcmul_assoc : forall {r c} (a b : X) (m : M r c), 
    a c* (b c* m) = (a * b) c* m.
  Proof.
    Admitted.
  
  Lemma mcmul_perm : forall {r c} (a b : X) (m : M r c), 
    a c* (b c* m) = b c* (a c* m).
  Proof.
    Admitted.
  
  Lemma mcmul_add_distr_l : forall {r c} (a : X) (m1 m2 : M r c), 
    mcmul a (madd m1 m2) = madd (mcmul a m1) (mcmul a m2).
  Proof.
    Admitted.
  
  Lemma mcmul_add_distr_r : forall {r c} (a b : X) (m : M r c), 
    mcmul (Xadd a b) m = madd (mcmul a m) (mcmul b m).
  Proof.
    Admitted.
  
  (* 0 c* m = mat0 *)
  Lemma mcmul_0_l : forall {r c} (m : M r c), X0 c* m = mat0 r c.
  Proof.
    Admitted.
  
  (* 1 * m = m *)
  Lemma mcmul_1_l : forall {r c} (m : M r c), 
    mcmul X1 m = m.
  Proof.
    Admitted.
  
  (* (-a) * m = - (a * m) *)
  Lemma mcmul_neg : forall {r c} a (m : M r c), 
    (Xopp a) c* m = - (a c* m).
  Proof.
    Admitted.
  
  (* (-a) * (- m) = (a * m) *)
  Lemma mcmul_neg_mopp : forall {r c} a (m : M r c), 
    (Xopp a) c* (mopp m) = (a c* m).
  Proof.
    Admitted.

  (* a * m = m -> a = 1 \/ m = 0 *)
  Lemma mcmul_same_imply_coef1_or_mzero : forall {r c} a (m : M r c),
    a c* m = m -> (a = X1) \/ (m = mat0 r c).
  Proof.
    Abort.
  
  (* 某两个非零矩阵存在k倍关系，则系数k不为0 *)
  Lemma mat_eq_mcmul_implfy_coef_neq0 : forall {r c} (m1 m2 : M r c) k,
    matnonzero m1 -> matnonzero m2 -> (m1 = k c* m2) -> k <> X0.
  Proof.
    Abort.
  
  (* 非零矩阵乘以k倍为零矩阵，则k为0 *)
  Lemma mcmul_mnonzero_eq0_imply_k0 : forall {r c} (m : M r c) k,
    matnonzero m -> mat0 r c = k c* m -> k = X0.
  Proof.
    Abort.
    
  (** 矩阵转置 *)
  Definition mtrans {r c} (m : M r c): M c r := matrix_of_fun_def 
    (fun i j => m j i).
  
  Global Notation "m 'ᵀ'" := (mtrans m) : mat_scope.
  
  Lemma mtrans_trans : forall {r c} (m : M r c), mtrans (mtrans m) = m.
  Proof.
    Admitted.

  (** 矩阵乘法 *)
  Definition mmul {r c s} (m1 : M r c) (m2 : M c s) : M r s :=
    mulmx m1 m2.  (* @mulmx X_ringType r c s m1 m2 *)
  Global Notation "m1 * m2" := (mmul m1 m2) : mat_scope.
  
  Lemma mmul_add_distr_l : forall {r c X} (m1 : M r c) (m2 m3 : M c X),
    m1 * (m2 + m3) = m1 * m2 + m1 * m3.
  Proof.
    Admitted.
  
  Lemma mmul_add_distr_r : forall {r c s} (m1 m2 : M r c) (m3 : M c s),
    (m1 + m2) * m3 = (m1 * m3) + (m2 * m3).
  Proof.
    Admitted.
  
  Lemma mmul_assoc : forall {r c s X} (m1 : M r c) (m2 : M c s) 
    (m3 : M s X),
    (m1 * m2) * m3 = m1 * (m2 * m3).
  Proof. intros. apply Logic.eq_sym. apply mulmxA. Qed.
  
  Lemma mmul_0_l : forall {r c X} (m : M c X), (mat0 r c) * m = mat0 r X.
  Proof.
    Admitted.
  
  Lemma mmul_0_r : forall {r c X} (m : M r c), m * (mat0 c X) = mat0 r X.
  Proof.
    Admitted.
  
  Lemma mmul_1_l : forall {r c} (m : M r c), (mat1 r) * m = m.
  Proof.
    Admitted.
  
  Lemma mmul_1_r : forall {r c} (m : M r c), m * (mat1 c) = m.
  Proof.
    Admitted.
  
(*   (** Vector type *)
  Definition vecr n := M 1 n.
  Definition vecc n := M n 1.
  
  (** ** Construct a matrix with a vector and a a matrix *)
  
  (** Construct by row *)
  Definition mconsr {r c} (v : vecr c) (m : M r c) : M (S r) c.
  Proof.
    destruct v,m.
    refine (mk_mat ((hd [] mat_data) :: mat_data0) _ _).
    - simpl. f_equal. auto.
    - simpl. split; auto.
      destruct mat_data; simpl in *; try lia.
  Defined.
  
  (** Construct by column *)
  Definition mconsc {r c} (v : vecc r) (m : M r c) : M r (S c).
  Proof.
    destruct v as [v], m as [m].
    refine (mk_mat (consc (hdc X0 v) m) _ _).
    - apply consc_height; auto. rewrite hdc_length; auto.
    - apply consc_width; auto. rewrite hdc_length; subst; auto.
  Defined. *)
  
  (** list list 与 矩阵互转 *)
  
(*   (* 这里条件太强了，其他矩阵实现不一定能满足，因此重新做一份 *)
  Definition l2m_old {r c} (dl : list (list X)) (H1 : length dl = r)
    (H2 : width dl c) : M r c := mk_mat dl H1 H2. *)

  Definition l2m {r c} (dl : list (list X)) : M r c.
(*   Proof.
    destruct (ri <? r) eqn:H1, (ci <? c) eqn:H2.
    { apply mathcomp_leq_iff_ltb in H1,H2.  (* 类型转换 *)
      pose (ri' := @Ordinal r ri H1).
      pose (ci' := @Ordinal c ci H2).
      exact (m ri' ci'). }
    all: exact X0.  (* 所有其他情形都输出 X0 *)
  Defined.
    matrix_of_fun_def (fun i j =>
      match 
     dlnth Xmul (m i j) a). *)
     apply (matrix_of_fun_def (fun i j => X0)).
     Defined.
     
  (* 检查 finfun_on 的构造 *)
  Section check_finfun_on.
    Variable r c : nat.
    Let fin_r_c_T := prod_finType (ordinal_finType r) (ordinal_finType c).
    
    (* 复杂的形式 *)
(*     Check @finfun_on fin_r_c_T (fun _ : 'I_r * 'I_c => X)
      (@enum_mem fin_r_c_T
        (@mem ('I_r * 'I_c) (predPredType ('I_r * 'I_c))
          (@PredOfSimpl.coerce ('I_r * 'I_c) (pred_of_argType ('I_r * 'I_c))))).
    
    (* 简单的形式，受到类型推断的支持 *)
    Check finfun_on (fun _ : 'I_r * 'I_c => X)
      (enum_mem (mem (PredOfSimpl.coerce (pred_of_argType ('I_r * 'I_c))))). *)
  End check_finfun_on.
  
  (** 将 finfun_on 转换为简单的 list (list X) *)
  Definition finfun_on_to_dlist (r c : nat) (f : finfun_on 
    (fun _ : 'I_r * 'I_c => X) 
    (enum_mem (mem (PredOfSimpl.coerce (pred_of_argType ('I_r * 'I_c)))))
    ) : list (list X) :=
    match f with
    | finfun_nil => []
    | finfun_cons _ _ _ _ => []
    end.
    
  Definition m2l {r c} (m : M r c) : list (list X).
  Proof.
    destruct m. destruct f.
    apply (finfun_on_to_dlist r c f).
  Defined.
  
  Lemma m2l_length : forall {r c} (m : M r c), length (m2l m) = r.
  Proof.
    Admitted.
  Global Hint Resolve m2l_length : mat.
  
  Lemma m2l_width : forall {r c} (m : M r c), width (m2l m) c.
  Proof.
    Admitted.
  Global Hint Resolve m2l_width : mat.
  
  Lemma m2l_l2m_id : forall {r c} (dl : list (list X)) (H1 : length dl = r)
    (H2 : width dl c), @m2l r c (l2m dl) = dl.
  Proof.
    Admitted.
  
  Lemma l2m_m2l_id : forall {r c} (m : M r c), l2m (m2l m) = m. 
  Proof.
    Admitted.
  
  Lemma l2m_inj : forall {r c} (d1 d2 : list (list X)),
    length d1 = r -> width d1 c -> 
    length d2 = r -> width d2 c -> 
    d1 <> d2 -> @l2m r c d1 <> l2m d2.
  Proof.
    Admitted.
    
  Lemma l2m_surj : forall {r c} (m : M r c), 
    (exists d, l2m d = m).
  Proof.
    Admitted.
    
  Lemma m2l_inj : forall {r c} (m1 m2 : M r c),
    m1 <> m2 -> m2l m1 <> m2l m2.
  Proof.
    Admitted.
    
  Lemma m2l_surj : forall {r c} (d : list (list X)), 
    length d = r -> width d c -> 
    (exists m, @m2l r c m = d).
  Proof.
    Admitted.
    
  (** ** Other OPs and PROPs *)
  
  (** Convert between tuples and matrix *)
  
  (** 3x3元组 转换为 mat_3x3 *)
  Definition t2m_3x3 (t : @T_3x3 X) : M 3 3.
  Proof.
    destruct t as ((t1,t2),t3).
    destruct t1 as ((a11,a12),a13).
    destruct t2 as ((a21,a22),a23).
    destruct t3 as ((a31,a32),a33).
    exact (mk_mat_3_3 a11 a12 a13 a21 a22 a23 a31 a32 a33).
  Defined.
  
  (** mat_3x3 转换为 3x3元组 ((a11,a12,a13),(a21,a22,a23),(a31,a32,a33)) *)
  Definition m2t_3x3 (m : M 3 3) : @T_3x3 X :=
    ((mnth m 0 0, mnth m 0 1, mnth m 0 2), 
     (mnth m 1 0, mnth m 1 1, mnth m 1 2),
     (mnth m 2 0, mnth m 2 1, mnth m 2 2)).
(*      
  Definition m2t_3x3 (m : M 3 3) : @T_3x3 X.
    destruct m. rename mat_data into dl.
    remember (hd [] dl) as l1.
    remember (hd [] (tl dl)) as l2.
    remember (hd [] (tl (tl dl))) as l3.
    remember (hd X0 l1, hd X0 (tl l1), hd X0 (tl (tl l1))) as t1.
    remember (hd X0 l2, hd X0 (tl l2), hd X0 (tl (tl l2))) as t2.
    remember (hd X0 l3, hd X0 (tl l3), hd X0 (tl (tl l3))) as t3.
    exact (t1, t2, t3).
  Defined.
 *)  
  (** 3x3元组 转 3x3矩阵 再转 3x3元组，二者相等 *)
  Lemma m2t_t2m_id_3x3 : forall (x : @T_3x3 X), m2t_3x3 (t2m_3x3 x) = x.
(*     Proof.
    destruct x as ((t1,t2),t3).
    destruct t1 as ((a11,a12),a13).
    destruct t2 as ((a21,a22),a23).
    destruct t3 as ((a31,a32),a33).
    simpl. auto.
  Qed. *)
  Admitted.
  
  (** 3x3矩阵 转 3x3元组 再转 3x3矩阵，二者相等 *)
(*   Lemma t2m_m2t_id_3x3 (m : M 3 3) : t2m_3x3 (m2t_3x3 m) = m.
    Proof.
    unfold t2m_3x3, m2t_3x3. unfold mk_mat_3_3.
    intros ri ci Hi Hj.
    do 3 (destruct ri; [do 3 (destruct ci; auto); lia | idtac]). lia.
  Qed.
  Admitted. *)
  Lemma t2m_m2t_id_3x3 : forall (m : M 3 3),
    t2m_3x3 (m2t_3x3 m) = m.
  Proof.
    Admitted.
  
  
  (** 取出1x1矩阵的第 0,0 个元素 *)
  Definition scalar_of_mat (m : M 1 1) := mnth m 0 0.

  (** 3阶方阵的行列式 *)
  Definition det_of_mat_3_3 (m : M 3 3) : X :=
    let '((a11,a12,a13),(a21,a22,a23),(a31,a32,a33)) :=
      m2t_3x3 m in
    let b1 := (a11 * a22 * a33)%X in
    let b2 := (a12 * a23 * a31)%X in
    let b3 := (a13 * a21 * a32)%X in
    let c1 := (a11 * a23 * a32)%X in
    let c2 := (a12 * a21 * a33)%X in
    let c3 := (a13 * a22 * a31)%X in
    let b := (b1 + b2 + b3)%X in
    let c := (c1 + c2 + c3)%X in
      (b - c)%X.

  (** V3斜对称矩阵 *)
(*   Definition skew_sym_mat_of_v3 (v : V3) : M 3 3.
  Proof.
    destruct (v3_to_t3 v) as [[x y] z].
    refine (mk_mat_3_3 
      X0    (-z)    y
      z     X0     (-x)
      (-y)  x       X0)%A.
  Defined. *)
  
  (** V3叉乘，向量积 *)
(*   Definition v3cross (v1 v2 : V3) : vec 3 := (skew_sym_mat_of_v3 v1) × v2. *)
  
  (** 矩阵是否为SO3（李群，旋转群） *)
  Definition so3 (m : M 3 3) : Prop := 
    let so3_mul_unit : Prop := (m ᵀ) * m = mat1 3 in
    let so3_det : Prop := (det_of_mat_3_3 m) = X1 in
      so3_mul_unit /\ so3_det.
  
End MatrixThy.

