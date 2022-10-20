(*
  purpose   : Homomorphism theory on matrix.
  author    : ZhengPu Shi
  date      : 2021.12
*)

Require Export MatrixAll.

Require Export HomomorphismThy.

Require Import Lia.
Require Import List.


(** * DR 与 DP 关于 xx运算 同态 *)
Module Homo_DR_DP (E : FieldSig).

  (** Instantialize the functor to module *)
  Module Export MatrixAllInst := MatrixAll E.
  
  (* ====================================================== *)
  (** ** DR 与 DP 关于矩阵加法运算的同构 *)
  
  (** 示例：用 DR 的加法性质，来证明 DP 的加法性质 *)
  
  Example mdp_madd_comm : forall r c,
    commutative (@DR.madd r c) -> commutative (@DP.madd r c).
  Proof.
    intros r c H.
    apply homo_keep_comm with (fa := @DR.madd r c).
    exists dr2dp. split. apply hom_madd_dr2dp. apply dr2dp_surj. apply H.
  Qed.
  
  Example mdp_madd_assoc : forall r c,
    associative (@DR.madd r c) -> associative (@DP.madd r c).
  Proof.
    intros r c H.
    apply homo_keep_assoc with (fa := @DR.madd r c).
    exists dr2dp. split. apply hom_madd_dr2dp. apply dr2dp_surj. apply H.
  Qed.
  
  (** 示例：用 DP 的加法性质，来证明 DR 的加法性质 *)
  
  (** dp2dr关于矩阵加法是同态映射: dp2dr (M1 + M2) = (dp2dr M1) + (dp2dr M2) *)
  
  Example dr_madd_comm : forall r c,
    commutative (@DP.madd r c) -> commutative (@DR.madd r c).
  Proof.
    intros r c H.
    apply homo_keep_comm with (fa := @DP.madd r c).
    exists dp2dr. split. apply hom_madd_dp2dr. apply dp2dr_surj. apply H.
  Qed.
  
End Homo_DR_DP.


