(*
  purpose   : Field algebra structure
  author    : ZhengPu Shi
  date      : 2021.05
*)

Require Export Ring Field.
Require QcExt RExt RAST.



(* ######################################################################### *)
(** * Field Signature, also mixed with a ring structure *)

(** New scope for field. "X" was chosen to prevent conflicts with other names *)
Declare Scope X_scope.
Delimit Scope X_scope with X.
Open Scope X_scope.

(** Signature for field *)
Module Type FieldSig.
  
  (** Carrier *)
  Parameter X : Type.
  
  (** Operations *)
  Parameter X0 X1 : X.
  Parameter Xadd Xmul : X -> X -> X.
  Parameter Xopp Xinv : X -> X.
  Parameter Xeqb : X -> X -> bool.
  
  (** Notations *)
  Notation "0" := X0 : X_scope.
  Notation "1" := X1 : X_scope.
  Infix "+" := Xadd : X_scope.
  Infix "*" := Xmul : X_scope.
  Notation "- a" := (Xopp a) : X_scope.
  Notation "/ a" := (Xinv a) : X_scope.
  Notation Xsub := (fun x y => x + -y).
  Notation Xdiv := (fun x y => x * /y).
  Infix "-" := Xsub : X_scope.
  Infix "/" := Xdiv : X_scope.
  Notation "a =? b" := (Xeqb a b) (at level 70) : X_scope.
  
  (** Bind something to the scope *)
  Bind Scope X_scope with X X0 X1 Xadd Xmul Xopp Xinv Xeqb.

  (** Properties *)

  (** Equality is decidable *)
  Parameter Xeqdec : forall (x y : X), {x = y} + {x <> y}.

  (** Reflection of Aeq and Aeqb *)
  Parameter Xeqb_true_iff : forall x y, (x =? y = true) <-> x = y.
  Parameter Xeqb_false_iff : forall x y, (x =? y = false) <-> (x <> y).
  
  (** 1 <> 0. *)
  Parameter X1_neq_X0 : X1 <> X0.
  
  (** Ring theory *)
  Parameter Ring_thy : ring_theory X0 X1 Xadd Xmul Xsub Xopp eq.
  Add Ring Ring_thy_inst : Ring_thy.

  (** Field Theory *)
  Parameter Field_thy: field_theory X0 X1 Xadd Xmul Xsub Xopp Xdiv Xinv eq.
  Add Field Field_thy_inst : Field_thy.

End FieldSig.



(* ######################################################################### *)
(** * Field theory *)

Module FieldThy (F : FieldSig).

  Export F.

  Open Scope X_scope.

  Lemma add_comm : forall a b, a + b = b + a.
  Proof. intros. ring. Qed.
  
  Lemma add_assoc : forall a b c, (a + b) + c = a + (b + c). 
  Proof. intros. ring. Qed.
  
  Lemma add_0_l : forall a, 0 + a = a.
  Proof. intros. ring. Qed.
  
  Lemma add_0_r : forall a, a + 0 = a.
  Proof. intros. ring. Qed.
  
  Lemma add_opp_l : forall a, -a + a = 0.
  Proof. intros. ring. Qed.
  
  Lemma add_opp_r : forall a, a - a = 0.
  Proof. intros. ring. Qed.
  
  Lemma opp_opp : forall a, - - a = a.
  Proof. intros. ring. Qed.
  
  Lemma add_cancel_l : forall a b1 b2, a + b1 = a + b2 -> b1 = b2.
  Proof.
    intros.
    rewrite <- (add_0_l b1).
    rewrite <- (add_0_l b2).   (* 0 + b1 = 0 + b2  *)
    rewrite <- (add_opp_l a).  (* -a + a + b1 = -a + a + b1 *)
    rewrite ?add_assoc.        (* -a + (a + b1) = -a + (a + b2) *)
    rewrite H. reflexivity.
  Qed.
  
  Lemma add_cancel_r : forall a1 a2 b, a1 + b = a2 + b -> a1 = a2.
  Proof.
    intros. rewrite <- (add_0_r a1). rewrite <- (add_0_r a2).
    rewrite <- (add_opp_r b). rewrite <- ?add_assoc. rewrite H. auto.
  Qed.
  
  Lemma mul_comm : forall a b, a * b = b * a.
  Proof. intros. ring. Qed.
  
  Lemma mul_assoc : forall a b c, (a * b) * c = a * (b * c). 
  Proof. intros. ring. Qed.
  
  Lemma mul_0_l : forall a, 0 * a = 0.
  Proof. intros. ring. Qed.
  
  Lemma mul_0_r : forall a, a * 0 = 0.
  Proof. intros. ring. Qed.
  
  Lemma mul_1_l : forall a, 1 * a = a.
  Proof. intros. ring. Qed.
  
  Lemma mul_1_r : forall a, a * 1 = a.
  Proof. intros. ring. Qed.
  
  Lemma mul_inv_l : forall a, a <> 0 -> /a * a = 1.
  Proof. intros. field. auto. Qed.
  
  Lemma mul_inv_r : forall a, a <> 0 -> a / a = 1.
  Proof. intros. field. auto. Qed.
  
  Lemma inv_inv : forall a, a <> 0 -> //a = a.
  Proof. intros. field. split; auto. apply X1_neq_X0. Qed.
  
  Lemma mul_cancel_l : forall a b1 b2, a <> 0 -> a * b1 = a * b2 -> b1 = b2.
  Proof.
    intros. rewrite <- (mul_1_l b1). rewrite <- (mul_1_l b2).
    rewrite <- (mul_inv_l a); auto. rewrite ?mul_assoc. f_equal. auto.
  Qed.
  
  Lemma mul_cancel_r : forall a1 a2 b, b <> 0 -> a1 * b = a2 * b -> a1 = a2.
  Proof.
    intros. rewrite <- (mul_1_r a1). rewrite <- (mul_1_r a2).
    rewrite <- (mul_inv_r b); auto. rewrite <- ?mul_assoc. f_equal. auto.
  Qed.
  
End FieldThy.



(* ######################################################################### *)
(** * Field on Qc *)

Module FieldQc.
  
  Export QcExt.
  Open Scope Qc_scope.
  
  Module Export FieldDefQc : FieldSig
    with Definition X := Qc
    with Definition X0 := 0
    with Definition X1 := 1
    with Definition Xadd := Qcplus
    with Definition Xopp := Qcopp
    with Definition Xmul := Qcmult
    with Definition Xinv := Qcinv
    with Definition Xeqb := Qceqb.
    
    Definition X := Qc.
    Definition X0 := 0.
    Definition X1 := 1.
    Definition Xadd := Qcplus.
    Definition Xopp := Qcopp.
    Definition Xmul := Qcmult.
    Definition Xinv := Qcinv.
    Definition Xeqb := Qceqb.
    Definition Xeqdec := Qceqdec.
    Definition Xeqb_true_iff := Qceqb_true_iff.
    Definition Xeqb_false_iff := Qceqb_false_iff.
    
    Lemma X1_neq_X0 : X1 <> X0.
    Proof. intro. discriminate. Qed.
    
    Lemma Ring_thy : ring_theory X0 X1 Xadd Xmul Qcminus Xopp eq.
    Proof.
      constructor; intros; try auto.
      apply Qcplus_0_l. apply Qcplus_comm. apply Qcplus_assoc.
      apply Qcmult_1_l. apply Qcmult_comm. apply Qcmult_assoc.
      apply Qcmult_plus_distr_l. apply Qcplus_opp_r.
    Qed.
    Add Ring Ring_thy_inst : Ring_thy.
    
    Lemma Field_thy : field_theory X0 X1 Xadd Xmul Qcminus Xopp Qcdiv 
      Xinv eq.
    Proof.
      constructor; try easy. apply Ring_thy.
      intros. rewrite Qcmult_comm,Qcmult_inv_r; auto.
    Qed.
    Add Field Field_thy_inst : Field_thy.

  End FieldDefQc.

End FieldQc.

(** Test *)
Section test.

  Import FieldQc.
(*   Open Scope X_scope. *)

  Goal forall a b c : X, (c<>0) -> (a + b) / c = a / c + b / c.
  Proof. intros. field. auto. Qed.

End test.



(* ######################################################################### *)
(** * Field on R *)

Module FieldR.
  
  Export RExt.
  Open Scope R_scope.

  Module Export FieldDefR : FieldSig
    with Definition X := R
    with Definition X0 := 0
    with Definition X1 := 1
    with Definition Xadd := Rplus
    with Definition Xopp := Ropp
    with Definition Xmul := Rmult
    with Definition Xinv := Rinv
    with Definition Xeqb := Reqb.
    
    Definition X := R.
    Definition X0 := 0.
    Definition X1 := 1.
    Definition Xadd := Rplus.
    Definition Xopp := Ropp.
    Definition Xmul := Rmult.
    Definition Xinv := Rinv.
    Definition Xeqb := Reqb.
    Definition Xeqdec := Req_EM_T.
    Definition Xeqb_true_iff := Reqb_true_iff.
    Definition Xeqb_false_iff := Reqb_false_iff.
    
    Lemma X1_neq_X0 : X1 <> X0.
    Proof. intro. auto with R. Qed.
    
    Lemma Ring_thy : ring_theory X0 X1 Xadd Xmul Rminus Xopp eq.
    Proof. constructor; intros; cbv; ring. Qed.
    Add Ring Ring_thy_inst : Ring_thy.
    
    Lemma Field_thy : field_theory X0 X1 Xadd Xmul Rminus Xopp Rdiv Xinv eq.
    Proof.
      constructor; try easy. apply Ring_thy. apply X1_neq_X0.
      intros; cbv; field; auto.
    Qed.
    Add Field Field_thy_inst : Field_thy.

  End FieldDefR.

End FieldR.

(** Test *)
Section test.

  Import FieldR.
(*   Open Scope X_scope. *)

  Goal forall a b c : X, (c<>0) -> (a + b) / c = a / c + b / c.
  Proof. intros. field. auto. Qed.

End test.


(* ######################################################################### *)
(** * Field on T *)

Module FieldT.
  
  Export RAST.
  Open Scope T_scope.
  
  Module Export FieldDefT : FieldSig
    with Definition X := T
    with Definition X0 := T0
    with Definition X1 := T1
    with Definition Xadd := Tadd
    with Definition Xopp := Topp
    with Definition Xmul := Tmul
    with Definition Xinv := Tinv
    with Definition Xeqb := Teqb.
    
    Axiom Teqb_true_iff : forall x y : T, (x =? y)%T = true <-> x = y.
    Axiom Teqb_false_iff : forall x y : T, (x =? y)%T = false <-> x <> y.
    
    Definition X := T.
    Definition X0 := T0.
    Definition X1 := T1.
    Definition Xadd := Tadd.
    Definition Xopp := Topp.
    Definition Xmul := Tmul.
    Definition Xinv := Tinv.
    Definition Xeqb := Teqb.
    Definition Xeqdec := Teqdec.
    Definition Xeqb_true_iff := Teqb_true_iff.
    Definition Xeqb_false_iff := Teqb_false_iff.
    
    Lemma X1_neq_X0 : X1 <> X0.
    Proof. intro. easy. Qed.
    
    Lemma Ring_thy : ring_theory X0 X1 Xadd Xmul Tsub Xopp eq.
    Proof. constructor; intros; cbv; ring. Qed.
    Add Ring Ring_thy_inst : Ring_thy.
    
    Lemma Field_thy : field_theory X0 X1 Xadd Xmul Tsub Xopp Tdiv Xinv eq.
    Proof.
      constructor; try easy. apply Ring_thy.
      intros; cbv; field; auto.
    Qed.
    Add Field Field_thy_inst : Field_thy.

  End FieldDefT.
  
  Module Export FieldThyT := FieldThy FieldDefT.

End FieldT.

(** Test *)
Section test.

  Import FieldT.
(*   Open Scope X_scope. *)

  Goal forall a b c : X, (c<>0) -> (a + b) / c = a / c + b / c.
  Proof. intros. field. auto. Qed.

End test.

