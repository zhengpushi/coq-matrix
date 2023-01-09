(*
 Copyright 2022 ZhengPu Shi
  This file is part of coq-matrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Homomorphism Theory.
  author    : ZhengPu Shi
  date      : 2021.12
  
  remark    :
  1. it is implemented with equivalence equality, not Leibniz equality.
  
  History   :
    2022.07.12  by Zhengpu SHI, remove equivalence relation, only use eq
*)

Require Export BasicConfig.

Section Homo.
  Variable A B : Type.
  Variable fa ga : A -> A -> A.
  Variable fb gb : B -> B -> B.
  Infix "+" := fa.
  Infix "*" := ga.
  Infix "⊕" := fb (at level 50).
  Infix "⊗" := gb (at level 40).
  
  (** If <A,+> and <B,⊕> is homomorphism, and + is commutative,
    then ⊕ is commutative too. *)
  Lemma homo_keep_comm : homomorphism fa fb -> 
    commutative fa -> commutative fb.
  Proof.
    intros [phi [Hhomo Hsurj]] H. intros a b.
    destruct (Hsurj a) as [a' Ha'].
    destruct (Hsurj b) as [b' Hb'].
    rewrite <- Ha', <- Hb'.
    repeat rewrite <- Hhomo. f_equal; auto.
  Qed.
  
  (** If <A,+> and <B,⊕> is homomorphism, and + is associative,
    then ⊕ is associative too. *)
  Lemma homo_keep_assoc : homomorphism fa fb -> 
    associative fa -> associative fb.
  Proof.
    intros [phi [Hhomo Hsurj]] H. intros a b c.
    destruct (Hsurj a) as [a' Ha'].
    destruct (Hsurj b) as [b' Hb'].
    destruct (Hsurj c) as [c' Hc'].
    rewrite <- Ha', <- Hb', <- Hc'.
    repeat rewrite <- Hhomo.
    rewrite H. auto.
  Qed.
  
  (** If <A,+,*>,<B,⊕,⊗> is homomorphism,
    and * is left distributive about + over A,
    then ⊗ is left distributive about ⊕ over B. *)
  Lemma homo_keep_distr_l : homomorphism2 fa ga fb gb -> 
    distributive_left fa ga -> distributive_left fb gb.
  Proof.
    intros [phi [[Hhomo Hsurj] [Hhomo' Hsurj']]] H. intros a b c.
    destruct (Hsurj a) as [a' Ha'].
    destruct (Hsurj b) as [b' Hb'].
    destruct (Hsurj c) as [c' Hc'].
    rewrite <- Ha', <- Hb', <- Hc'.
    rewrite <- ?Hhomo', <- ?Hhomo, <- ?Hhomo'.
    f_equal; auto.
  Qed.
  
  (** If <A,+,*>,<B,⊕,⊗> is homomorphism,
    and * is right distributive about + over A,
    then ⊗ is right distributive about ⊕ over B. *)
  Lemma homo_keep_distr_r : homomorphism2 fa ga fb gb -> 
    distributive_right fa ga -> distributive_right fb gb.
  Proof.
    intros [phi [[Hhomo Hsurj] [Hhomo' Hsurj']]] H. intros a b c.
    destruct (Hsurj a) as [a' Ha'].
    destruct (Hsurj b) as [b' Hb'].
    destruct (Hsurj c) as [c' Hc'].
    rewrite <- Ha', <- Hb', <- Hc'.
    rewrite <- ?Hhomo', <- ?Hhomo, <- ?Hhomo'.
    f_equal; auto.
  Qed.
  
End Homo.

Section Compose.
  
  (** Composition of homomorphism mapping is also homomorphism mapping *)
  Lemma homom_comp_imply_homo : forall A B C (fa : A -> A -> A) 
    (fb : B -> B -> B) (fc : C -> C -> C), 
    homomorphism fa fb -> homomorphism fb fc ->
    homomorphism fa fc.
  Proof.
    intros.
    destruct H as [phi [Hhomo Hsurj]], H0 as [psi [Hhomo' Hsurj']].
    exists (fun a => psi (phi a)). split.
    - intros a b. rewrite <- Hhomo'. f_equal. rewrite <- Hhomo. auto.
    - intros c.
      destruct (Hsurj' c) as [b Hb].
      destruct (Hsurj b) as [a Ha].
      exists a. subst. auto.
  Qed.
  
End Compose.
