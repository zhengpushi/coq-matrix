(*
 Copyright 2022 ZhengPu Shi
  This file is part of coq-matrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Isomorphism theory on matrix.
  author    : ZhengPu Shi
  date      : 2022.07
*)

Require Export MatrixAll.

Require Export IsomorphismThy.

Require Import Lia.
Require Import List.

(** * DR 与 DP 关于 xx运算 同构 *)
Module Iso_DR_DP (E : FieldSig).
  
  (** Instantialize the functor to module *)
  Module Export MatrixAllInst := MatrixAll E.
  
  (* ====================================================== *)
  (** ** DR 与 DP 关于矩阵加法运算的同构 *)
  
  (** 示例：DR加法性质 iff DP加法性质 *)
  
  Example dr_dp_madd_comm : forall r c,
    commutative (@DR.madd r c) <-> commutative (@DP.madd r c).
  Proof.
    intros r c.
    apply isomor_keep_comm with (fa := @DR.madd r c).
    exists dr2dp. split. apply hom_madd_dr2dp. apply dr2dp_bij.
  Qed.
  
  Example dr_dp_madd_assoc : forall r c,
    associative (@DR.madd r c) <-> associative (@DP.madd r c).
  Proof.
    intros r c.
    apply isomor_keep_assoc with (fa := @DR.madd r c).
    exists dr2dp. split. apply hom_madd_dr2dp. apply dr2dp_bij.
  Qed.
  
  (** Matrix multiplication operation is closed at square matrix only. *)
  
  Example dr_dp_mmul_assoc : forall n,
    associative (@DR.mmul n n n) <-> associative (@DP.mmul n n n).
  Proof.
    Admitted.
  
  Example dr_dp_mmul_madd_distr_left : forall n,
    distributive_left (@DR.madd n n) (@DR.mmul n n n) <->
    distributive_left (@DP.madd n n) (@DP.mmul n n n).
  Proof.
    Admitted.
  
  Example dr_dp_madd_cancel_left : forall r c,
    cancel_left (@DR.madd r c) <-> cancel_left (@DP.madd r c).
  Proof.
    intros r c.
    apply isomor_keep_cancel_left with (fa := @DR.madd r c).
    exists dr2dp. split. apply hom_madd_dr2dp. apply dr2dp_bij.
  Qed.
  
  Example dr_dp_madd_cancel_right : forall r c,
    cancel_right (@DR.madd r c) <-> cancel_right (@DP.madd r c).
  Proof.
    intros r c.
    apply isomor_keep_cancel_right with (fa := @DR.madd r c).
    exists dr2dp. split. apply hom_madd_dr2dp. apply dr2dp_bij.
  Qed.
  
  
End Iso_DR_DP.


