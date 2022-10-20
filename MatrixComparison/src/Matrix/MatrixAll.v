(*
  purpose   : Entrance for access all matrix.
  author    : ZhengPu Shi
  date      : 2021.12
*)

Require Export FieldStruct.

Require 
  DepPair.MatrixThy
  DepList.MatrixThy
  DepRec.MatrixThy 
  NatFun.MatrixThy
  FinFun.MatrixThy
  .

  
(* ######################################################################### *)
(** * Collection of all matrix implementations (Functor) *)
Module MatrixAll (F : FieldSig).

  (* ======================================================================= *)
  (** ** Short name for visit any implementations *)
  Import DepPair.MatrixThy.
  Module DP := MatrixThy F.
  
  Import DepList.MatrixThy.
  Module DL := MatrixThy F.
  
  Import DepRec.MatrixThy.
  Module DR := MatrixThy F.
  
  Import NatFun.MatrixThy.
  Module NF := MatrixThy F.
  
  Import FinFun.MatrixThy.
  Module FF := MatrixThy F.


  (* ======================================================================= *)
  (** ** Conversion between different implementations *)
  
  (** DR -- NF *)
  Definition dr2nf {r c} (m : DR.M r c) : NF.M r c := NF.l2m (DR.m2l m).
  Definition nf2dr {r c} (m : NF.M r c) : DR.M r c := DR.l2m (NF.m2l m).
  
  Lemma dr2nf_bij {r c} : bijective (@dr2nf r c).
  Proof.
    unfold dr2nf. unfold bijective,injective,surjective. split; intros.
    - apply NF.l2m_inj; auto with mat. apply DR.m2l_inj; auto.
    - exists (DR.l2m (NF.m2l b)).
      rewrite DR.m2l_l2m_id; auto with mat. apply NF.l2m_m2l_id.
  Qed.
  
  Corollary dr2nf_surj {r c} : surjective (@dr2nf r c).
  Proof. destruct (@dr2nf_bij r c); auto. Qed.
  
  Lemma nf2dr_bij {r c} : bijective (@nf2dr r c).
  Proof.
    unfold nf2dr. unfold bijective,injective,surjective. split; intros.
    - apply DR.l2m_inj; auto with mat. apply NF.m2l_inj; auto.
    - exists (NF.l2m (DR.m2l b)).
      rewrite NF.m2l_l2m_id; auto with mat. apply DR.l2m_m2l_id.
  Qed.
  
  Corollary nf2dr_surj {r c} : surjective (@nf2dr r c).
  Proof. destruct (@nf2dr_bij r c); auto. Qed.
  
  Lemma dr2nf_nf2dr_id : forall r c (m : NF.M r c), 
    dr2nf (nf2dr m) = m.
  Proof.
    intros. unfold dr2nf,nf2dr. rewrite DR.m2l_l2m_id.
    apply NF.l2m_m2l_id; auto. apply NF.m2l_length. apply NF.m2l_width.
  Qed.
  
  Lemma nf2dr_dr2nf_id : forall r c (m : DR.M r c), 
    nf2dr (dr2nf m) = m.
  Proof.
    intros. unfold dr2nf,nf2dr. rewrite NF.m2l_l2m_id.
    apply DR.l2m_m2l_id. apply DR.m2l_length. apply DR.m2l_width.
  Qed.
  
  Lemma hom_madd_dr2nf : forall r c, 
    homomorphic DR.madd NF.madd (@dr2nf r c).
  Proof.
    intros r c m1 m2. destruct m1 as [d1 H1 W1], m2 as [d2 H2 W2].
    unfold dr2nf. simpl.
    unfold matmap2dl. simpl.
    apply NF.meq_iff. intros i j Hi Hj. simpl.
    unfold dmap2. rewrite map2_nth.
    - rewrite map2_nth; auto.
      rewrite (width_imply_nth_length _ i c); auto. rewrite H1; auto.
      rewrite (width_imply_nth_length _ i c); auto. rewrite H2; auto.
    - subst; auto.
    - subst; auto. rewrite H2; auto.
  Qed.
  
  (** DR -- FF *)
  Definition dr2ff {r c} (m : DR.M r c) : FF.M r c := FF.l2m (DR.m2l m).
  Definition ff2dr {r c} (m : FF.M r c) : DR.M r c := DR.l2m (FF.m2l m).
  
  Lemma dr2ff_bij {r c} : bijective (@dr2ff r c).
  Proof.
    unfold dr2ff. unfold bijective,injective,surjective. split; intros.
    - apply FF.l2m_inj; auto with mat. apply DR.m2l_inj; auto.
    - exists (DR.l2m (FF.m2l b)).
      rewrite DR.m2l_l2m_id; auto with mat. apply FF.l2m_m2l_id.
  Qed.
  
  Corollary dr2ff_surj {r c} : surjective (@dr2ff r c).
  Proof. destruct (@dr2ff_bij r c); auto. Qed.
  
  Lemma ff2dr_bij {r c} : bijective (@ff2dr r c).
  Proof.
    unfold ff2dr. unfold bijective,injective,surjective. split; intros.
    - apply DR.l2m_inj; auto with mat. apply FF.m2l_inj; auto.
    - exists (FF.l2m (DR.m2l b)).
      rewrite FF.m2l_l2m_id; auto with mat. apply DR.l2m_m2l_id.
  Qed.
  
  Corollary ff2dr_surj {r c} : surjective (@ff2dr r c).
  Proof. destruct (@ff2dr_bij r c); auto. Qed.
  
  Lemma dr2ff_ff2dr_id : forall r c (m : FF.M r c), 
    dr2ff (ff2dr m) = m.
  Proof.
    intros. unfold dr2ff,ff2dr. rewrite DR.m2l_l2m_id.
    apply FF.l2m_m2l_id; auto. apply FF.m2l_length. apply FF.m2l_width.
  Qed.
  
  Lemma ff2dr_dr2ff_id : forall r c (m : DR.M r c), 
    ff2dr (dr2ff m) = m.
  Proof.
    intros. unfold dr2ff,ff2dr. rewrite FF.m2l_l2m_id.
    apply DR.l2m_m2l_id. apply DR.m2l_length. apply DR.m2l_width.
  Qed.
  
  Lemma hom_madd_dr2ff : forall r c, 
    homomorphic DR.madd FF.madd (@dr2ff r c).
  Proof.
    intros r c m1 m2. destruct m1 as [d1 H1 W1], m2 as [d2 H2 W2].
    unfold dr2ff. simpl.
    unfold matmap2dl. simpl.
(* (*     apply FF.meq_iff. intros i j Hi Hj. simpl. *)
    unfold dmap2. rewrite map2_nth.
    - rewrite map2_nth; auto.
      rewrite (width_imply_nth_length _ i c); auto. rewrite H1; auto.
      rewrite (width_imply_nth_length _ i c); auto. rewrite H2; auto.
    - subst; auto.
    - subst; auto. rewrite H2; auto.
  Qed.
 *)  
  Admitted.
  

  (** DR -- DP *)
  Definition dr2dp {r c} (m : DR.M r c) : DP.M r c := DP.l2m (DR.m2l m).
  Definition dp2dr {r c} (m : DP.M r c) : DR.M r c := DR.l2m (DP.m2l m).
  
  Lemma dr2dp_bij {r c} : bijective (@dr2dp r c).
  Proof.
    unfold dr2dp. unfold bijective,injective,surjective. split; intros.
    - apply DP.l2m_inj; auto with mat. apply DR.m2l_inj; auto.
    - exists (DR.l2m (DP.m2l b)).
      rewrite DR.m2l_l2m_id; auto with mat. apply DP.l2m_m2l_id.
  Qed.
  
  Corollary dr2dp_surj {r c} : surjective (@dr2dp r c).
  Proof. destruct (@dr2dp_bij r c); auto. Qed.
  
  Lemma dp2dr_bij {r c} : bijective (@dp2dr r c).
  Proof.
    unfold dp2dr. unfold bijective,injective,surjective. split; intros.
    - apply DR.l2m_inj; auto with mat. apply DP.m2l_inj; auto.
    - exists (DP.l2m (DR.m2l b)).
      rewrite DP.m2l_l2m_id; auto with mat. apply DR.l2m_m2l_id.
  Qed.
  
  Corollary dp2dr_surj {r c} : surjective (@dp2dr r c).
  Proof. destruct (@dp2dr_bij r c); auto. Qed.
  
  Lemma dr2dp_dp2dr_id : forall r c (m : DP.M r c), 
    dr2dp (dp2dr m) = m.
  Proof.
    intros. unfold dr2dp,dp2dr. rewrite DR.m2l_l2m_id.
    apply DP.l2m_m2l_id; auto. apply DP.m2l_length. apply DP.m2l_width.
  Qed.
  
  Lemma dp2dr_dr2dp_id : forall r c (m : DR.M r c), 
    dp2dr (dr2dp m) = m.
  Proof.
    intros. unfold dr2dp,dp2dr. rewrite DP.m2l_l2m_id.
    apply DR.l2m_m2l_id. apply DR.m2l_length. apply DR.m2l_width.
  Qed.
  
  Lemma hom_madd_dr2dp : forall r c, homomorphic DR.madd DP.madd (@dr2dp r c).
  Proof.
    intros r c m1 m2. destruct m1, m2.
    unfold dr2dp. simpl.
    unfold Matrix.matmap2dl. simpl.
    apply DP.l2m_madd_homo; auto.
  Qed.
  
  Lemma hom_madd_dp2dr : forall r c, homomorphic DP.madd DR.madd (@dp2dr r c).
  Proof.
    intros r c m1 m2.
    unfold dp2dr. apply DR.meq_iff. simpl.
    unfold DR.l2m, Matrix.matmap2dl. simpl.
    repeat rewrite Matrix.l2m_aux_eq;
    try apply DP.m2l_length;
    try apply DP.m2l_width.
    apply DP.m2l_madd_homo.
  Qed.
  
  Lemma hom_mmul_dr2dp : forall n, homomorphic DR.mmul DP.mmul (@dr2dp n n).
  Proof.
    intros n m1 m2. destruct m1 as [d1 H1 W1], m2 as [d2 H2 W2].
    unfold dr2dp. simpl.
    Admitted.
  
  Lemma hom_mmul_dp2dr : forall n, homomorphic DP.mmul DR.mmul (@dp2dr n n).
  Proof.
    intros n m1 m2.
(*      destruct m1 as [d1 H1 W1], m2 as [d2 H2 W2]. *)
(*     unfold dr2dp. simpl. *)
    Admitted.

  (** DR -- DL *)
  Definition dr2dl {r c} (m : DR.M r c) : DL.M r c := DL.l2m (DR.m2l m).
  Definition dl2dr {r c} (m : DL.M r c) : DR.M r c := DR.l2m (DL.m2l m).

  Lemma dr2dl_bij {r c} : bijective (@dr2dl r c).
  Proof.
    unfold dr2dl. unfold bijective,injective,surjective. split; intros.
    - apply DL.l2m_inj; auto with mat. apply DR.m2l_inj; auto.
    - exists (DR.l2m (DL.m2l b)).
      rewrite DR.m2l_l2m_id; auto with mat. apply DL.l2m_m2l_id.
  Qed.
  
  Corollary dr2dl_surj {r c} : surjective (@dr2dl r c).
  Proof. destruct (@dr2dl_bij r c); auto. Qed.
  
  Lemma dl2dr_bij {r c} : bijective (@dl2dr r c).
  Proof.
    unfold dl2dr. unfold bijective,injective,surjective. split; intros.
    - apply DR.l2m_inj; auto with mat. apply DL.m2l_inj; auto.
    - exists (DL.l2m (DR.m2l b)).
      rewrite DL.m2l_l2m_id; auto with mat. apply DR.l2m_m2l_id.
  Qed.
  
  Corollary dl2dr_surj {r c} : surjective (@dl2dr r c).
  Proof. destruct (@dl2dr_bij r c); auto. Qed.
  
  Lemma dr2dl_dl2dr_id : forall r c (m : DL.M r c), 
    dr2dl (dl2dr m) = m.
  Proof.
    intros. unfold dr2dl,dl2dr. rewrite DR.m2l_l2m_id.
    apply DL.l2m_m2l_id. apply DL.m2l_length. apply DL.m2l_width.
  Qed.
  
  Lemma dl2dr_dr2dl_id : forall r c (m : DR.M r c), 
    dl2dr (dr2dl m) = m.
  Proof.
    intros. unfold dr2dl,dl2dr. rewrite DL.m2l_l2m_id.
    apply DR.l2m_m2l_id. apply DR.m2l_length. apply DR.m2l_width.
  Qed.
  
  (** NF -- FF *)
  Definition nf2ff {r c} (m : NF.M r c) : FF.M r c := FF.l2m (NF.m2l m).
  Definition ff2nf {r c} (m : FF.M r c) : NF.M r c := NF.l2m (FF.m2l m).

  Lemma nf2ff_bij {r c} : bijective (@nf2ff r c).
  Proof.
    unfold nf2ff. unfold bijective,injective,surjective. split; intros.
    - apply FF.l2m_inj; auto with mat. apply NF.m2l_inj; auto.
    - exists (NF.l2m (FF.m2l b)).
      rewrite NF.m2l_l2m_id; auto with mat. apply FF.l2m_m2l_id.
  Qed.
  
  Corollary nf2ff_surj {r c} : surjective (@nf2ff r c).
  Proof. destruct (@nf2ff_bij r c); auto. Qed.
  
  Lemma ff2nf_bij {r c} : bijective (@ff2nf r c).
  Proof.
    unfold ff2nf. unfold bijective,injective,surjective. split; intros.
    - apply NF.l2m_inj; auto with mat. apply FF.m2l_inj; auto.
    - exists (FF.l2m (NF.m2l b)).
      rewrite FF.m2l_l2m_id; auto with mat. apply NF.l2m_m2l_id.
  Qed.
  
  Corollary ff2nf_surj {r c} : surjective (@ff2nf r c).
  Proof. destruct (@ff2nf_bij r c); auto. Qed.
  
  Lemma nf2ff_dp2nf_id : forall r c (m : FF.M r c), 
    nf2ff (ff2nf m) = m.
  Proof.
    intros. unfold nf2ff,ff2nf. rewrite NF.m2l_l2m_id.
    apply FF.l2m_m2l_id. apply FF.m2l_length. apply FF.m2l_width.
  Qed.
  
  Lemma ff2nf_nf2ff_id : forall r c (m : NF.M r c), 
    ff2nf (nf2ff m) = m.
  Proof.
    intros. unfold ff2nf,nf2ff. rewrite FF.m2l_l2m_id.
    apply NF.l2m_m2l_id; auto. apply NF.m2l_length. apply NF.m2l_width.
  Qed.
  
  (** NF -- DP *)
  Definition nf2dp {r c} (m : NF.M r c) : DP.M r c := DP.l2m (NF.m2l m).
  Definition dp2nf {r c} (m : DP.M r c) : NF.M r c := NF.l2m (DP.m2l m).

  Lemma nf2dp_bij {r c} : bijective (@nf2dp r c).
  Proof.
    unfold nf2dp. unfold bijective,injective,surjective. split; intros.
    - apply DP.l2m_inj; auto with mat. apply NF.m2l_inj; auto.
    - exists (NF.l2m (DP.m2l b)).
      rewrite NF.m2l_l2m_id; auto with mat. apply DP.l2m_m2l_id.
  Qed.
  
  Corollary nf2dp_surj {r c} : surjective (@nf2dp r c).
  Proof. destruct (@nf2dp_bij r c); auto. Qed.
  
  Lemma dp2nf_bij {r c} : bijective (@dp2nf r c).
  Proof.
    unfold dp2nf. unfold bijective,injective,surjective. split; intros.
    - apply NF.l2m_inj; auto with mat. apply DP.m2l_inj; auto.
    - exists (DP.l2m (NF.m2l b)).
      rewrite DP.m2l_l2m_id; auto with mat. apply NF.l2m_m2l_id.
  Qed.
  
  Corollary dp2nf_surj {r c} : surjective (@dp2nf r c).
  Proof. destruct (@dp2nf_bij r c); auto. Qed.
  
  Lemma nf2dp_dp2nf_id : forall r c (m : DP.M r c), 
    nf2dp (dp2nf m) = m.
  Proof.
    intros. unfold nf2dp,dp2nf. rewrite NF.m2l_l2m_id.
    apply DP.l2m_m2l_id. apply DP.m2l_length. apply DP.m2l_width.
  Qed.
  
  Lemma dp2nf_nf2dp_id : forall r c (m : NF.M r c), 
    dp2nf (nf2dp m) = m.
  Proof.
    intros. unfold dp2nf,nf2dp. rewrite DP.m2l_l2m_id.
    apply NF.l2m_m2l_id; auto. apply NF.m2l_length. apply NF.m2l_width.
  Qed.

  (** NF -- DL *)
  Definition nf2dl {r c} (m : NF.M r c) : DL.M r c := DL.l2m (NF.m2l m).
  Definition dl2nf {r c} (m : DL.M r c) : NF.M r c := NF.l2m (DL.m2l m).
  
  Lemma nf2dl_bij {r c} : bijective (@nf2dl r c).
  Proof.
    unfold nf2dl. unfold bijective,injective,surjective. split; intros.
    - apply DL.l2m_inj; auto with mat. apply NF.m2l_inj; auto.
    - exists (NF.l2m (DL.m2l b)).
      rewrite NF.m2l_l2m_id; auto with mat. apply DL.l2m_m2l_id.
  Qed.
  
  Corollary nf2dl_surj {r c} : surjective (@nf2dl r c).
  Proof. destruct (@nf2dl_bij r c); auto. Qed.
  
  Lemma dl2nf_bij {r c} : bijective (@dl2nf r c).
  Proof.
    unfold dl2nf. unfold bijective,injective,surjective. split; intros.
    - apply NF.l2m_inj; auto with mat. apply DL.m2l_inj; auto.
    - exists (DL.l2m (NF.m2l b)).
      rewrite DL.m2l_l2m_id; auto with mat. apply NF.l2m_m2l_id.
  Qed.
  
  Corollary dl2nf_surj {r c} : surjective (@dl2nf r c).
  Proof. destruct (@dl2nf_bij r c); auto. Qed.
  
  Lemma nf2dl_dl2nf_id : forall r c (m : DL.M r c), 
    nf2dl (dl2nf m) = m.
  Proof.
    intros. unfold nf2dl,dl2nf. rewrite NF.m2l_l2m_id.
    apply DL.l2m_m2l_id. apply DL.m2l_length. apply DL.m2l_width.
  Qed.
  
  Lemma dl2nf_nf2dl_id : forall r c (m : NF.M r c), 
    dl2nf (nf2dl m) = m.
  Proof.
    intros. unfold nf2dl,dl2nf. rewrite DL.m2l_l2m_id.
    apply NF.l2m_m2l_id; auto. apply NF.m2l_length. apply NF.m2l_width.
  Qed.
  
  (** FF -- DP *)
  Definition ff2dp {r c} (m : FF.M r c) : DP.M r c := DP.l2m (FF.m2l m).
  Definition dp2ff {r c} (m : DP.M r c) : FF.M r c := FF.l2m (DP.m2l m).

  Lemma ff2dp_bij {r c} : bijective (@ff2dp r c).
  Proof.
    unfold ff2dp. unfold bijective,injective,surjective. split; intros.
    - apply DP.l2m_inj; auto with mat. apply FF.m2l_inj; auto.
    - exists (FF.l2m (DP.m2l b)).
      rewrite FF.m2l_l2m_id; auto with mat. apply DP.l2m_m2l_id.
  Qed.
  
  Corollary ff2dp_surj {r c} : surjective (@ff2dp r c).
  Proof. destruct (@ff2dp_bij r c); auto. Qed.
  
  Lemma dp2ff_bij {r c} : bijective (@dp2ff r c).
  Proof.
    unfold dp2ff. unfold bijective,injective,surjective. split; intros.
    - apply FF.l2m_inj; auto with mat. apply DP.m2l_inj; auto.
    - exists (DP.l2m (FF.m2l b)).
      rewrite DP.m2l_l2m_id; auto with mat. apply FF.l2m_m2l_id.
  Qed.
  
  Corollary dp2ff_surj {r c} : surjective (@dp2ff r c).
  Proof. destruct (@dp2ff_bij r c); auto. Qed.
  
  Lemma ff2dp_dp2ff_id : forall r c (m : DP.M r c), 
    ff2dp (dp2ff m) = m.
  Proof.
    intros. unfold ff2dp,dp2ff. rewrite FF.m2l_l2m_id.
    apply DP.l2m_m2l_id. apply DP.m2l_length. apply DP.m2l_width.
  Qed.
  
  Lemma dp2ff_ff2dp_id : forall r c (m : FF.M r c), 
    dp2ff (ff2dp m) = m.
  Proof.
    intros. unfold dp2ff,ff2dp. rewrite DP.m2l_l2m_id.
    apply FF.l2m_m2l_id; auto. apply FF.m2l_length. apply FF.m2l_width.
  Qed.
  
  (** FF -- DL *)
  Definition ff2dl {r c} (m : FF.M r c) : DL.M r c := DL.l2m (FF.m2l m).
  Definition dl2ff {r c} (m : DL.M r c) : FF.M r c := FF.l2m (DL.m2l m).

  Lemma ff2dl_bij {r c} : bijective (@ff2dl r c).
  Proof.
    unfold ff2dl. unfold bijective,injective,surjective. split; intros.
    - apply DL.l2m_inj; auto with mat. apply FF.m2l_inj; auto.
    - exists (FF.l2m (DL.m2l b)).
      rewrite FF.m2l_l2m_id; auto with mat. apply DL.l2m_m2l_id.
  Qed.
  
  Corollary ff2dl_surj {r c} : surjective (@ff2dl r c).
  Proof. destruct (@ff2dl_bij r c); auto. Qed.
  
  Lemma dl2ff_bij {r c} : bijective (@dl2ff r c).
  Proof.
    unfold dl2ff. unfold bijective,injective,surjective. split; intros.
    - apply FF.l2m_inj; auto with mat. apply DL.m2l_inj; auto.
    - exists (DL.l2m (FF.m2l b)).
      rewrite DL.m2l_l2m_id; auto with mat. apply FF.l2m_m2l_id.
  Qed.
  
  Corollary dl2ff_surj {r c} : surjective (@dl2ff r c).
  Proof. destruct (@dl2ff_bij r c); auto. Qed.
  
  Lemma ff2dl_dl2ff_id : forall r c (m : DL.M r c), 
    ff2dl (dl2ff m) = m.
  Proof.
    intros. unfold ff2dl,dl2ff. rewrite FF.m2l_l2m_id.
    apply DL.l2m_m2l_id. apply DL.m2l_length. apply DL.m2l_width.
  Qed.
  
  Lemma dl2ff_ff2dl_id : forall r c (m : FF.M r c), 
    dl2ff (ff2dl m) = m.
  Proof.
    intros. unfold dl2ff,ff2dl. rewrite DL.m2l_l2m_id.
    apply FF.l2m_m2l_id; auto. apply FF.m2l_length. apply FF.m2l_width.
  Qed.
  
  (** DP -- DL *)
  Definition dp2dl {r c} (m : DP.M r c) : DL.M r c := DL.l2m (DP.m2l m).
  Definition dl2dp {r c} (m : DL.M r c) : DP.M r c := DP.l2m (DL.m2l m).
  
  Lemma dp2dl_bij {r c} : bijective (@dp2dl r c).
  Proof.
    unfold dp2dl. unfold bijective,injective,surjective. split; intros.
    - apply DL.l2m_inj; auto with mat. apply DP.m2l_inj; auto.
    - exists (DP.l2m (DL.m2l b)).
      rewrite DP.m2l_l2m_id; auto with mat. apply DL.l2m_m2l_id.
  Qed.
  
  Corollary dp2dl_surj {r c} : surjective (@dp2dl r c).
  Proof. destruct (@dp2dl_bij r c); auto. Qed.
  
  Lemma dl2dp_bij {r c} : bijective (@dl2dp r c).
  Proof.
    unfold dl2dp. unfold bijective,injective,surjective. split; intros.
    - apply DP.l2m_inj; auto with mat. apply DL.m2l_inj; auto.
    - exists (DL.l2m (DP.m2l b)).
      rewrite DL.m2l_l2m_id; auto with mat. apply DP.l2m_m2l_id.
  Qed.
  
  Corollary dl2dp_surj {r c} : surjective (@dl2dp r c).
  Proof. destruct (@dl2dp_bij r c); auto. Qed.
  
  Lemma dp2dl_dl2dp_id : forall r c (m : DL.M r c), 
    dp2dl (dl2dp m) = m.
  Proof.
    intros. unfold dp2dl,dl2dp. rewrite DP.m2l_l2m_id.
    apply DL.l2m_m2l_id. apply DL.m2l_length. apply DL.m2l_width.
  Qed.
  
  Lemma dl2dp_dp2dl_id : forall r c (m : DP.M r c), 
    dl2dp (dp2dl m) = m.
  Proof.
    intros. unfold dp2dl,dl2dp. rewrite DL.m2l_l2m_id.
    apply DP.l2m_m2l_id; auto. apply DP.m2l_length. apply DP.m2l_width.
  Qed.
  
End MatrixAll.


(* ######################################################################### *)
(** * Collection of all different implementations (Concrete Module) *)

(** Matrix based on Qc *)
Module MatrixAllQc := MatrixAll FieldQc.FieldDefQc.

Module MatrixQc_DR := MatrixAllQc.DR.
Module MatrixQc_DP := MatrixAllQc.DP.
Module MatrixQc_DL := MatrixAllQc.DL.
Module MatrixQc_NF := MatrixAllQc.NF.
Module MatrixQc_FF := MatrixAllQc.FF.

(** Matrix based on R *)
Module MatrixAllR := MatrixAll FieldR.FieldDefR.

Module MatrixR_DR := MatrixAllR.DR.
Module MatrixR_DP := MatrixAllR.DP.
Module MatrixR_DL := MatrixAllR.DL.
Module MatrixR_NF := MatrixAllR.NF.
Module MatrixR_FF := MatrixAllR.FF.


(* ######################################################################### *)
(** * Usage demo *)

(** test DR *)
Module Usage_DR.
  
  Import MatrixR_DR.
  Import RExt List ListNotations.
  Open Scope R.
  Open Scope mat_scope.

  Notation "0" := R0.
  Notation "1" := R1.
  
  Example m1 := mat1 5.
(*   Compute m2l m1. *)
(*   Compute m2l (m1 * m1)%M. *)
  
  Example ex1 : forall r c (m1 m2 : M r c), madd m1 m2 = madd m2 m1.
  Proof. intros. apply madd_comm. Qed.

End Usage_DR.

(** test NF *)
Module Usage_NF.
  
  Import QcExt List ListNotations.
  Import MatrixQc_NF.
  
  Open Scope Q. (* 要能解析 0.1 之类的输入，必须先打开该作用域 *)
  Open Scope Qc.
  Open Scope mat_scope.
  
  Example m1 := mat1 5.
(*   Compute m2l m1.
  Compute m2l (m1 * m1)%M. *)
  
  Coercion Q2Qc : Q >-> Qc.
  
  (** (i,j) <- i * 1.0 + j * 0.1 *)
  Example m2 : M 5 5 := @mk_mat Qc _ _ 
    (fun i j => (nat2Q i) + (nat2Q j) * 0.1)%Qc.
(*   Compute m2l m2.
  Compute m2l (m2 * m2)%M. (* todo: Check that why so many 0 *) *)
  
  Example ex1 : forall r c (m1 m2 : M r c), madd m1 m2 = madd m2 m1.
  Proof. intros. apply madd_comm. Qed.

End Usage_NF.

(** test FF *)
Module Usage_FF.
  
  Import QcExt List ListNotations.
  Import MatrixQc_FF.
  
  Open Scope Q. (* 要能解析 0.1 之类的输入，必须先打开该作用域 *)
  Open Scope Qc.
  Open Scope mat_scope.
  
  Example m1 := mat1 5.
(*   Compute m2l m1.
  Compute m2l (m1 * m1)%M. *)
  
  Coercion Q2Qc : Q >-> Qc.
  
  (** (i,j) <- i * 1.0 + j * 0.1 *)
(*   Example m2 : M 5 5 := @mk_mat Qc _ _ 
    (fun i j => (nat2Q i) + (nat2Q j) * 0.1)%Qc. *)
(*   Compute m2l m2.
  Compute m2l (m2 * m2)%M. (* todo: Check that why so many 0 *) *)
  
  Example ex1 : forall r c (m1 m2 : M r c), madd m1 m2 = madd m2 m1.
  Proof. intros. apply madd_comm. Qed.

End Usage_FF.

(** test DL *)
Module Usage_DL.
  
  Import QcExt List ListNotations.
  Import MatrixQc_DL.
  
  Open Scope Q.
  Open Scope Qc.
  Open Scope mat_scope.
  
  Example m1 := mat1 5.
(*   Compute m2l m1.
  Compute m2l (m1 * m1)%M. *)
  
End Usage_DL.

(** test DP *)
Module Usage_DP.
  
  Import QcExt List ListNotations.
  Import MatrixQc_DP.
  
  Open Scope Q.
  Open Scope Qc.
  Open Scope mat_scope.
  
  Example m1 := mat1 5.
(*   Compute m2l m1.
  Compute m2l (m1 * m1)%M. *)
  
End Usage_DP.


(** Use different implementations same time, show conversion *)
Module Usage_Mixed.

  Import FieldQc.
  Import MatrixAllQc.
  
  Import Coq.Vectors.Vector VectorNotations List ListNotations.
  Open Scope Q.
  Open Scope Qc.
  Coercion Q2Qc : Q >-> Qc.
  
  Definition m1 : DR.M 3 3 := DR.mk_mat_3_3 1 2 3 4 5 6 7 8 9.
(*   Compute dr2nf m1.
  Compute dr2dp m1.
  Compute dr2dl m1. *)
  
  Definition m2 : NF.M 3 3 := dr2nf m1.
(*   Compute nf2dr m2.
  Compute nf2dp m2.
  Compute nf2dl m2. *)
  
  Definition m3 : DP.M 3 3 := nf2dp m2.
(*   Compute dp2dr m3.
  Compute dp2nf m3.
  Compute dp2dl m3. *)
  
  Definition m4 : DL.M 3 3 := dr2dl m1.
(*   Compute dl2dr m4.
  Compute dl2nf m4.
  Compute dl2dp m4. *)
  
  Definition m5 : FF.M 3 3 := dl2ff m4.
  (* The evaluation on FF is crashed! *)
  
End Usage_Mixed.
