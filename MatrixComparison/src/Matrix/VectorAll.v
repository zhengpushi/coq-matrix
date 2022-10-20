(*
  purpose   : Entrance for access all vector.
  author    : ZhengPu Shi
  date      : 2021.12
*)

Require Export FieldStruct.

Require 
  DepPair.VectorThy
  DepList.VectorThy
  DepRec.VectorThy 
  NatFun.VectorThy
  .



(* ######################################################################### *)
(** * Collection of all vector implementations (Functor) *)
Module VectorAll (F : FieldSig).

  (* ======================================================================= *)
  (** ** Short name for visit any implementations *)
  Import DepPair.VectorThy.
  Module DP := VectorThy F.
  
  Import DepList.VectorThy.
  Module DL := VectorThy F.

  Import DepRec.VectorThy.
  Module DR := VectorThy F.
  
  Import NatFun.VectorThy.
  Module NF := VectorThy F.


  (* ======================================================================= *)
  (** ** Conversion between different implementations *)
  
  (** DR -- NF *)
  Definition dr2nf {n} (v : DR.V n) : NF.V n := NF.l2v (DR.v2l v).
  Definition nf2dr {n} (v : NF.V n) : DR.V n := DR.l2v (NF.v2l v).
  
  Lemma dr2nf_nf2dr_id : forall n (v : NF.V n), 
    dr2nf (nf2dr v) = v.
  Proof.
    intros. unfold dr2nf,nf2dr. rewrite DR.v2l_l2v_id.
    apply NF.l2v_v2l_id; auto. apply NF.v2l_length.
  Qed.
  
  Lemma nf2dr_dr2nf_id : forall n (v : DR.V n), 
    nf2dr (dr2nf v) = v.
  Proof.
    intros. unfold dr2nf,nf2dr. rewrite NF.v2l_l2v_id.
    apply DR.l2v_v2l_id. apply DR.v2l_length.
  Qed.

  (** VLL -- VDP *)
  Definition dr2dp {n} (v : DR.V n) : DP.V n := DP.l2v (DR.v2l v).
  Definition dp2dr {n} (v : DP.V n) : DR.V n := DR.l2v (DP.v2l v).
  
  Lemma dr2dp_dp2dr_id : forall n (v : DP.V n), 
    dr2dp (dp2dr v) = v.
  Proof.
    intros. unfold dr2dp,dp2dr. rewrite DR.v2l_l2v_id.
    apply DP.l2v_v2l_id; auto. apply DP.v2l_length.
  Qed.
  
  Lemma dp2dr_dr2dp_id : forall n (v : DR.V n), 
    dp2dr (dr2dp v) = v.
  Proof.
    intros. unfold dr2dp,dp2dr. rewrite DP.v2l_l2v_id.
    apply DR.l2v_v2l_id. apply DR.v2l_length.
  Qed.

  (** VLL -- VDL *)
  Definition dr2dl {n} (v : DR.V n) : DL.V n := DL.l2v (DR.v2l v).
  Definition dl2dr {n} (v : DL.V n) : DR.V n := DR.l2v (DL.v2l v).

  Lemma dr2dl_dl2dr_id : forall n (v : DL.V n), 
    dr2dl (dl2dr v) = v.
  Proof.
    intros. unfold dr2dl,dl2dr. rewrite DR.v2l_l2v_id.
    apply DL.l2v_v2l_id. apply DL.v2l_length.
  Qed.
  
  Lemma dl2dr_dr2dl_id : forall n (v : DR.V n), 
    dl2dr (dr2dl v) = v.
  Proof.
    intros. unfold dr2dl,dl2dr. rewrite DL.v2l_l2v_id.
    apply DR.l2v_v2l_id. apply DR.v2l_length.
  Qed.
  
  (** FUN -- VDP *)
  Definition nf2dp {n} (v : NF.V n) : DP.V n := DP.l2v (NF.v2l v).
  Definition dp2nf {n} (v : DP.V n) : NF.V n := NF.l2v (DP.v2l v).

  Lemma nf2dp_dp2nf_id : forall n (v : DP.V n), 
    nf2dp (dp2nf v) = v.
  Proof.
    intros. unfold nf2dp,dp2nf. rewrite NF.v2l_l2v_id.
    apply DP.l2v_v2l_id. apply DP.v2l_length.
  Qed.
  
  Lemma dp2nf_nf2dp_id : forall n (v : NF.V n), 
    dp2nf (nf2dp v) = v.
  Proof.
    intros. unfold dp2nf,nf2dp. rewrite DP.v2l_l2v_id.
    apply NF.l2v_v2l_id; auto. apply NF.v2l_length.
  Qed.

  (** FUN -- VDL *)
  Definition nf2dl {n} (v : NF.V n) : DL.V n := DL.l2v (NF.v2l v).
  Definition dl2nf {n} (v : DL.V n) : NF.V n := NF.l2v (DL.v2l v).
  
  Lemma nf2dl_dl2nf_id : forall n (v : DL.V n), 
    nf2dl (dl2nf v) = v.
  Proof.
    intros. unfold nf2dl,dl2nf. rewrite NF.v2l_l2v_id.
    apply DL.l2v_v2l_id. apply DL.v2l_length.
  Qed.
  
  Lemma dl2nf_nf2dl_id : forall n (v : NF.V n), 
    dl2nf (nf2dl v) = v.
  Proof.
    intros. unfold nf2dl,dl2nf. rewrite DL.v2l_l2v_id.
    apply NF.l2v_v2l_id; auto. apply NF.v2l_length.
  Qed.
  
  (** VDP -- VDL *)
  Definition dp2dl {n} (v : DP.V n) : DL.V n := DL.l2v (DP.v2l v).
  Definition dl2dp {n} (v : DL.V n) : DP.V n := DP.l2v (DL.v2l v).
  
  Lemma dp2dl_dl2dp_id : forall n (v : DL.V n), 
    dp2dl (dl2dp v) = v.
  Proof.
    intros. unfold dp2dl,dl2dp. rewrite DP.v2l_l2v_id.
    apply DL.l2v_v2l_id. apply DL.v2l_length.
  Qed.
  
  Lemma dl2dp_dp2dl_id : forall n (v : DP.V n), 
    dl2dp (dp2dl v) = v.
  Proof.
    intros. unfold dp2dl,dl2dp. rewrite DL.v2l_l2v_id.
    apply DP.l2v_v2l_id; auto. apply DP.v2l_length.
  Qed.
  
End VectorAll.


(* ######################################################################### *)
(** * Collection of all different implementations (Concrete Module) *)

(** Vector based on Qc *)
Module VectorAllQc := VectorAll FieldQc.FieldDefQc.

Module VectorQc_DR := VectorAllQc.DR.
Module VectorQc_DP := VectorAllQc.DP.
Module VectorQc_DL := VectorAllQc.DL.
Module VectorQc_NF := VectorAllQc.NF.

(** Vector based on R *)
Module VectorAllR := VectorAll FieldR.FieldDefR.

Module VectorR_DR := VectorAllR.DR.
Module VectorR_DP := VectorAllR.DP.
Module VectorR_DL := VectorAllR.DL.
Module VectorR_NF := VectorAllR.NF.


(* ######################################################################### *)
(** * Usage demo *)

(** test VLL *)
Module Usage_DR.
  
  Import VectorR_DR.
  Import RExt List ListNotations.
  Open Scope R.
  Open Scope mat_scope.

  Notation "0" := R0.
  Notation "1" := R1.
  
  Example v1 := @l2v 5 (map nat2R (seq 0 5)).
(*   Compute v2l v1.
  Compute vdot v1 v1.
 *)
End Usage_DR.

(** test FUN *)
Module Usage_NF.
  
  Import QcExt List ListNotations.
  Import VectorQc_NF.
  
  Open Scope Q.
  Open Scope Qc.
  Open Scope mat_scope.
  Coercion Q2Qc : Q >-> Qc.
  
  Example v1 := @l2v 5 (map nat2Qc (seq 0 5)).
(*   Compute v2l v1.
  Compute vdot v1 v1.
 *)  
  (** (i) <- i * 0.1 *)
  Example v2 : V 50 := mk_mat _ _ 
    (fun i j => (nat2Q i) * 0.1)%Qc.
(*   Compute v2l v2.
  Compute vdot v2 v2.
 *)
End Usage_NF.

(** test VDL *)
Module Usage_DL.
  
  Import QcExt List ListNotations.
  Import VectorQc_DL.
  
  Open Scope Q.
  Open Scope Qc.
  Open Scope mat_scope.
  
  Example v1 := @l2v 5 (map nat2Qc (seq 0 5)).
(*   Compute v2l v1.
  Compute vdot v1 v1. *)
  
End Usage_DL.

(** test VDP *)
Module Usage_DP.
  
  Import QcExt List ListNotations.
  Import VectorQc_DP.
  
  Open Scope Q.
  Open Scope Qc.
  Open Scope mat_scope.
  
  Example v1 := @l2v 5 (map nat2Qc (seq 0 5)).
(*   Compute v2l v1.
  Compute vdot v1 v1. *)
  
End Usage_DP.


(** Use different implementations same time, show conversion *)
Module Usage_Mixed.

  Import FieldQc.
  Import VectorAllQc.
  
  Import Coq.Vectors.Vector VectorNotations List ListNotations.
  Open Scope Q.
  Open Scope Qc.
  Coercion Q2Qc : Q >-> Qc.
  
  (* 这里 list Q 不能自动转换为 list Qc，有没有什么好办法？ *)
  Definition v1 : DR.V 5 := DR.l2v [Q2Qc 1; Q2Qc 2; Q2Qc 3; Q2Qc 4; Q2Qc 5].
(*   Compute dr2nf v1.
  Compute dr2dp v1.
  Compute dr2dl v1. *)
  
  Definition v2 : NF.V 5 := dr2nf v1.
(*   Compute nf2dr v2.
  Compute nf2dp v2.
  Compute nf2dl v2. *)
  
  Definition v3 : DP.V 5 := nf2dp v2.
(*   Compute dp2dr v3.
  Compute dp2nf v3.
  Compute dp2dl v3. *)
  
  Definition v4 : DL.V 5 := dr2dl v1.
(*   Compute dl2dr v4.
  Compute dl2nf v4.
  Compute dl2dp v4. *)
  
End Usage_Mixed.

