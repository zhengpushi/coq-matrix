(*
  purpose   : matrix implmented with List List
  author    : ZhengPu Shi
  date      : 2021.05
*)

Require Export BasicConfig.

Require Export Lia.
Require Export ListListExt.

Open Scope mat_scope.

(** ** Definition of Matrix Type *)
Section mat_def.

  Variable A : Type.
  
  Record mat {r c : nat} : Type := mk_mat {
    mat_data : list (list A);
    mat_height : length mat_data = r;
    mat_width : width mat_data c
  }.

End mat_def.

Arguments mat {A}.
Arguments mk_mat {A r c}.
Arguments mat_data {A r c}.
Arguments mat_height {A r c}.
Arguments mat_width {A r c}.


(** ** matrix equality *)
Section mat_eq.

  Variable A : Type.
  
  (* 列表长度证明的无关性 *)
  Lemma hcond1_eq_hcond2 : forall (A : Type) (n : nat) 
    (l : list A) (p1 p2 : length l = n), p1 = p2.
  Proof.
    intros. apply UIP.
  Qed.
  
  (* 尽管证明不是唯一的，但证明是无关的 *)
  Lemma hcond1_eq_hcond2' : forall (A : Type) (n : nat) 
    (l : list A) (p1 p2 : length l = n), p1 = p2.
  Proof.
    intros. induction n; simpl in *.
    - apply UIP.
    - destruct l. simpl in *. lia.
      apply UIP.
  Qed.
  
(*   Print hcond1_eq_hcond2.
  Print hcond1_eq_hcond2'. *)

  (* 二维表宽度证明的无关性 *)
  Lemma wcond1_eq_wcond2 : forall (A : Type) (c : nat) 
    (dl : list (list A)) (p1 p2 : width dl c), p1 = p2.
  Proof.
    intros. 
(*     Fail apply UIP. (* 不是等式，UIP 无法使用 *) *)
    (* 展开width，并归纳 dl *)
    generalize dependent p2. 
    generalize dependent p1.
    induction dl; intros; simpl.
    - unfold width in *.
      destruct p2,p1. auto.
    - simpl in p1,p2. destruct p1,p2. rewrite (IHdl w w0).
      assert (e = e0). apply hcond1_eq_hcond2.
      rewrite H. auto.
  Qed.

  (** 二维表相等，则构造出的矩阵相等 *)
  Lemma m1_eq_m2 : forall (A : Type) (r c : nat)
    (dl1 dl2 : list (list A)) (e1 : dl1 = dl2)
    (hcond1 : length dl1 = r) (wcond1 : width dl1 c)
    (hcond2 : length dl2 = r) (wcond2 : width dl2 c),
    (mk_mat dl1 hcond1 wcond1) = 
    (mk_mat dl2 hcond2 wcond2).
  Proof.
    intros. subst.
    rewrite (UIP_refl nat (length dl2) hcond2).
    generalize dependent wcond2.
    generalize dependent wcond1.
    induction dl2; intros.
    - simpl in *.
      destruct wcond1, wcond2. auto.
    - destruct wcond1, wcond2.
      assert (e = e0). apply hcond1_eq_hcond2.
      assert (w = w0). apply wcond1_eq_wcond2.
      subst. auto.
  Qed.
  
  (* 矩阵相等，iff，内容相等 *)
  Lemma meq_iff : forall (A : Type) (r c : nat) (m1 m2 : @mat A r c), 
    mat_data m1 = mat_data m2 <-> m1 = m2.
  Proof.
    intros.
    destruct m1 as (dl1,hcond1,wcond1).
    destruct m2 as (dl2,hcond2,wcond2).
    simpl in *. split; intros.
    - subst. rewrite (UIP_refl nat (length dl2) hcond2).
      generalize dependent wcond2.
      generalize dependent wcond1.
      induction dl2; intros; simpl in *.
      + destruct wcond1,wcond2; auto.
      + destruct wcond1,wcond2.
        assert (w = w0). apply wcond1_eq_wcond2.
        assert (e = e0). apply hcond1_eq_hcond2.
        subst. auto.
    - injection H. auto.
  Qed.
  
  (*矩阵不相等，iff，内容不相等 *)
  Lemma meq_iff_not : forall (A : Type) (r c : nat) (m1 m2 : @mat A r c), 
    mat_data m1 <> mat_data m2 <-> m1 <> m2.
  Proof.
    intros. split; intros.
    - intro. apply meq_iff in H0. auto.
    - intro. apply meq_iff in H0. auto.
  Qed.
  
End mat_eq.


Arguments meq_iff {A r c}.


(** ** matrix with specific size *)

(** mat_1_1 *)
Section mat_1_1.
  
  Variable A : Type.
  Variable a : A.
  
  Let data := [[a]].
  Let cond_h : length data = 1. auto. Qed.  
  Let cond_w : width data 1. simpl. auto. Qed.
  
  Definition mk_mat_1_1 : @mat A 1 1 := mk_mat data cond_h cond_w.

End mat_1_1.

Arguments mk_mat_1_1 {A}.


(** mat_1_2 *)
Section mat_1_2.
  
  Variable A : Type.
  Variable a b : A.
  
  Let data : list (list A) := [[a; b]].
  Let cond_h : length data = 1. auto. Qed.  
  Let cond_w : width data 2. simpl. auto. Qed.
  
  Definition mk_mat_1_2' : @mat A 1 2 := mk_mat data cond_h cond_w.

End mat_1_2.


(** mat_0_c *)
Section mat_0_c.
  
  Variable A : Type.
  Variable c : nat.

  Let data : list (list A) := [].
  Let cond_h : length data = 0. auto. Qed.  
  Let cond_w : width data c. simpl. auto. Qed.
  
  Definition mk_mat_0_c : @mat A 0 c := mk_mat data cond_h cond_w.

End mat_0_c.

Arguments mk_mat_0_c {A}.


(** mat_1_c *)
Section mat_1_c.
  
  Variable A : Type.
  Variable l : list A.
  Variable c : nat.
  Variable H1 : length l = c.
  
  Let data : list (list A) := [l].
  Let cond_h : length data = 1. auto. Qed.  
  Let cond_w : width data c. simpl. auto. Qed.
  
  Definition mk_mat_1_c : @mat A 1 c := mk_mat data cond_h cond_w.

End mat_1_c.

Arguments mk_mat_1_c {A}.


(** mat_1_2, mat_1_3, ... *)
Definition mk_mat_1_2 {A} (a1 a2 : A) : mat 1 2 := 
  mk_mat_1_c [a1;a2] 2 eq_refl.

Definition mk_mat_1_3 {A} (a1 a2 a3 : A) : mat 1 3 := 
  mk_mat_1_c [a1;a2;a3] 3 eq_refl.

Definition mk_mat_1_4 {A} (a1 a2 a3 a4 : A) : mat 1 4 := 
  mk_mat_1_c [a1;a2;a3;a4] 4 eq_refl.


(** mat_r_0 *)
Section mat_r_0.
  
  Variable A : Type.
  Variable l : list A.
  Variable r : nat.
  Variable H1 : length l = r.
  
  Let data : list (list A) := @dnil A r.
  Let cond_h : length data = r. unfold data. simpl. rewrite dnil_height. auto. 
    Qed.
  Let cond_w : width data 0. unfold data. apply dnil_width. Qed.
  
  Definition mk_mat_r_0 : @mat A r 0 := mk_mat data cond_h cond_w.

End mat_r_0.

Arguments mk_mat_r_0 {A}.


(** mat_r_1 *)
Section mat_r_1.
  
  Variable A : Type.
  Variable l : list A.
  Variable r : nat.
  Variable H1 : length l = r.
  
  Let data : list (list A) := cvt_row2col l.
  Let cond_h : length data = r. unfold data. rewrite cvt_row2col_height. auto. 
    Qed.
  Let cond_w : width data 1. unfold data. apply cvt_row2col_width; auto. Qed.
  
  Definition mk_mat_r_1 : @mat A r 1 := mk_mat data cond_h cond_w.

End mat_r_1.

Arguments mk_mat_r_1 {A}.


(** mat_2_1, mat_3_1, ... *)
Definition mk_mat_2_1 {A} (a1 a2 : A) : mat 2 1 := 
  mk_mat_r_1 [a1;a2] 2 eq_refl.

Definition mk_mat_3_1 {A} (a1 a2 a3 : A) : mat 3 1 := 
  mk_mat_r_1 [a1;a2;a3] 3 eq_refl.

Definition mk_mat_4_1 {A} (a1 a2 a3 a4 : A) : mat 4 1 := 
  mk_mat_r_1 [a1;a2;a3;a4] 4 eq_refl.


(** mat_2_2 *)
Section mat_2_2.
  
  Variable A : Type.
  Variable a11 a12 a21 a22 : A.
  
  Let data : list (list A) := [[a11;a12];[a21;a22]].
  Let cond_h : length data = 2. auto. Qed.
  Let cond_w : width data 2. unfold data. simpl. tauto. Qed.
  
  Definition mk_mat_2_2 : @mat A 2 2 := mk_mat data cond_h cond_w.

End mat_2_2.

Arguments mk_mat_2_2 {A}.


(** mat_3_3 *)
Section mat_3_3.
  
  Variable A : Type.
  Variable a11 a12 a13 a21 a22 a23 a31 a32 a33 : A.
  
  Let data : list (list A) := [[a11;a12;a13];[a21;a22;a23];[a31;a32;a33]].
  Let cond_h : length data = 3. auto. Qed.
  Let cond_w : width data 3. unfold data. simpl. tauto. Qed.
  
  Definition mk_mat_3_3 : @mat A 3 3 := mk_mat data cond_h cond_w.

End mat_3_3.

Arguments mk_mat_3_3 {A}.


(** Get Matrix Element *)
Section mat_nth.

  Variable A : Type.
  Variable A0 : A.
  Variable r c : nat.
  Variable m : @mat A r c.
  Variable ri ci : nat.
  
  Definition mat_nth : A := nth ci (nth ri (mat_data m) []) A0.
  
End mat_nth.

Arguments mat_nth {A} A0 {r c}.

Section mat_nth_props.
  
  (* 两个矩阵相等，iff，能访问的每一个元素都相等 *)
  Lemma meq_iff_mnth : forall A A0 {r c : nat} (m1 m2 : @mat A r c),
    m1 = m2 <-> 
    (forall (ri ci : nat) (Hri : (ri < r)%nat) (Hci : (ci < c)%nat),
      mat_nth A0 m1 ri ci = mat_nth A0 m2 ri ci).
  Proof.
    intros. destruct m1,m2; simpl in *. split.
    - intros. f_equal. apply meq_iff; simpl. inversion H. auto.
    - intros. apply meq_iff; simpl.
      unfold mat_nth in *. simpl in *.
      rewrite (@dlist_eq_iff_nth_nth A A0 r c); auto.
  Qed.

End mat_nth_props.


(** ** Matrix map to a dlist *)
Section matmapdl.
  
  Variable A B : Type.
  Variable f : A -> B.
  
  Definition matmapdl {r c} (m : @mat A r c) : list (list B) :=
    dmap f (mat_data m).

  Lemma matmapdl_height : forall r c (m : @mat A r c), 
    length (matmapdl m) = r.
  Proof. 
    intros; simpl. unfold matmapdl. rewrite dmap_height.
    apply mat_height.
  Qed.

  Lemma matmapdl_width : forall r c (m : @mat A r c), 
    width (matmapdl m) c.
  Proof. 
    intros; simpl. unfold matmapdl. rewrite <- dmap_width.
    apply mat_width.
  Qed.

End matmapdl.

Arguments matmapdl {A B} f {r c}.
Arguments matmapdl_height {A B} f {r c}.
Arguments matmapdl_width {A B} f {r c}.


(** ** Matrix map2 to a dlist *)
Section matmap2dl.
  
  Variable A B C : Type.
  Variable f : A -> B -> C.
  
  Definition matmap2dl {r c} (m1 : @mat A r c) (m2 : @mat B r c) 
    : list (list C) :=
    dmap2 f (mat_data m1) (mat_data m2).

  Lemma matmap2dl_height : forall {r c} (m1 : @mat A r c) (m2 : @mat B r c),
    length (matmap2dl m1 m2) = r.
  Proof. 
    intros; simpl. unfold matmap2dl. rewrite dmap2_height;
    repeat rewrite mat_height; auto.
  Qed.

  Lemma matmap2dl_width : forall {r c} (m1 : @mat A r c) (m2 : @mat B r c),
    width (matmap2dl m1 m2) c.
  Proof. 
    intros; simpl. unfold matmap2dl. apply dmap2_width;
    apply mat_width.
  Qed.

End matmap2dl.

Arguments matmap2dl {A B C} f {r c}.
Arguments matmap2dl_height {A B C} f {r c}.
Arguments matmap2dl_width {A B C} f {r c}.


(* 
(** ** Matrix map2 to a dlist with same base type *)
Section matmap2dl_sametype.
  
  Variable A : Type.
  Variable A0 : A.
  Variable opp : A -> A.
  Variable sub : A -> A -> A.
  Variable sub_comm : forall a b, a - b = - (b - a).
  
  Lemma matmapdl_sub_comm : forall dl1 dl2 c, 
    length dl1 = length dl2 ->
    width dl1 c -> width dl2 c ->
    matmap2dl sub dl1 dl2 = dlmap opp (matmap2dl sub dl2 dl1).
  Proof.
    induction dl1,dl2; simpl; intros; auto. f_equal; auto.
    - apply list_sub_comm; auto.
    - destruct H0,H1. apply IHdl1 with (c:=c); auto.
  Qed.

End matmap2dl. *)


(** ** Matrix map *)
Section matmap.

  Variable A B : Type.
  Variable f : A -> B.
  
  Definition matmap {r c} (m : @mat A r c) : @mat B r c :=
    mk_mat (matmapdl f m) (matmapdl_height f m) (matmapdl_width f m).

End matmap.

Arguments matmap {A B} f {r c}.


(** ** Matrix map2 *)
Section matmap2.

  Variable A B C : Type.
  Variable f : A -> B -> C.
  
  Definition matmap2 {r c} (m1 : @mat A r c) (m2 : @mat B r c) 
    : @mat C r c :=
    mk_mat (matmap2dl f m1 m2) (matmap2dl_height f m1 m2) 
      (matmap2dl_width f m1 m2).
  
End matmap2.

Arguments matmap2 {A B C} f {r c}.


(** ** Matrix map2 with same base type *)
Section matmap2_sametype.

  Variable A : Type.
  Variable f : A -> A -> A.
  Infix "+" := f.
  Variable f_comm : forall a b, a + b = b + a.
  Variable f_assoc : forall a b c, (a + b) + c = a + (b + c).

  Lemma matmap2_comm : forall {r c} (m1 m2 : @mat A r c),
    matmap2 f m1 m2 = matmap2 f m2 m1.
  Proof.
    intros. apply meq_iff; simpl. unfold matmap2dl.
    apply dmap2_comm; auto.
  Qed.
  
  Lemma matmap2_assoc : forall {r c} (m1 m2 m3 : @mat A r c),
    matmap2 f (matmap2 f m1 m2) m3 = matmap2 f m1 (matmap2 f m2 m3).
  Proof.
    intros. apply meq_iff; simpl. unfold matmap2dl.
    apply dmap2_assoc; auto.
  Qed.
  
End matmap2_sametype.


(** ** zero matrix and unit matrix *)
Section matzero.
  
  Variable A : Type.
  Variable A0 A1 : A.
  
  Definition matzero {r c} := mk_mat (dlzero A0 r c)
    (dlzero_height A0) (dlzero_width A0).
  
  Definition matunit {n} := mk_mat (dlunit A0 A1 n)
    (dlunit_height A0 A1) (dlunit_width A0 A1).

End matzero.

Arguments matzero {A}.
Arguments matunit {A}.


(** ** matrix transpose *)
Section mat_trans.
  
  Variable A : Type.
  Variable A0 : A.
  Variable add : A -> A -> A.
  Infix "+" := add.
  Variable add_0_l : forall a, A0 + a = a.
  Variable add_comm : forall a b, a + b = b + a.
  
  Definition mat_trans {r c} (m : @mat A r c) : @mat A c r :=
    let dl := mat_data m in
      mk_mat (dltrans dl c) 
        (dltrans_height dl c (mat_width m))
        (dltrans_width dl r c (mat_height m) (mat_width m)).
  
  (** Transpose twice return back *)
  Lemma mat_trans_trans : forall {r c} (m : @mat A r c),
    mat_trans (mat_trans m) = m.
  Proof.
    intros. apply meq_iff. destruct m; simpl in *.
    rewrite dltrans_trans; auto.
  Qed.
  
End mat_trans.

Arguments mat_trans {A} {r c}.


(** ** matrix addition *)
Section matadd.
  
  Variable A : Type.
  Variable A0 : A.
  Variable add : A -> A -> A.
  Infix "+" := add.
  Variable add_0_l : forall a, A0 + a = a.
  Variable add_comm : forall a b, a + b = b + a.
  Variable add_assoc : forall a b c, (a + b) + c = a + (b + c).
  
  (** matadd *)
  Definition matadd {r c} (m1 m2 : @mat A r c) : @mat A r c :=
    matmap2 add m1 m2.
  Infix "+" := matadd : mat_scope.

  Open Scope mat_scope.
  
  Lemma matadd_comm : forall {r c} (m1 m2 : @mat A r c),
    m1 + m2 = m2 + m1.
  Proof.
    intros. apply meq_iff; simpl. unfold matmap2dl.
    apply dmap2_comm. auto.
  Qed.
  
  Lemma matadd_assoc : forall {r c} (m1 m2 m3 : @mat A r c),
    (m1 + m2) + m3 = m1 + (m2 + m3).
  Proof.
    intros. apply meq_iff; simpl. unfold matmap2dl.
    apply dmap2_assoc. auto.
  Qed.
  
  (** 0 + m = m *)
  Lemma matadd_zero_l : forall {r c} (m : @mat A r c),
    (matzero A0 r c) + m = m.
  Proof.
    intros. apply meq_iff; simpl. unfold matmap2dl.
    apply dladd_zero_l; auto. apply mat_height. apply mat_width.
  Qed.
  
  (** m + 0 = m *)
  Lemma matadd_zero_r : forall {r c} (m : @mat A r c),
    m + (matzero A0 r c) = m.
  Proof.
    intros. unfold matadd. rewrite matmap2_comm; auto. apply matadd_zero_l.
  Qed.

End matadd.

Arguments matadd {A} add {r c}.
Infix "+" := matadd : mat_scope.


(** ** matrix substraction and opposition *)
Section matsub_opp.
  
  Variable A : Type.
  Variable A0 : A.
  Variable opp : A -> A.
  Variable add : A -> A -> A.
  Infix "+" := add.
  Notation "- x" := (opp x).
  Notation sub := (fun x y : A => x + (-y)).
  Infix "-" := sub.
  Variable sub_comm : forall a b, a - b = - (b - a).
  Variable sub_assoc1 : forall a b c, (a - b) - c = (a - c) - b.
  Variable sub_assoc2 : forall a b c, (a - b) - c = a - (b + c).
  Variable sub_0_l : forall a, A0 - a = - a.
  Variable sub_0_r : forall a, a - A0 = a.
  Variable sub_self : forall a, a - a = A0.
  Variable opp_opp : forall a, - (- a) = a.
  
  Definition matopp {r c} (m : @mat A r c) : @mat A r c :=
    matmap opp m.
  
  Lemma matopp_matopp : forall {r c} (m : mat r c), matopp (matopp m) = m.
  Proof.
    intros. apply meq_iff; simpl. unfold matmapdl. unfold matopp.
    unfold matmap. simpl. unfold matmapdl. unfold dmap.
    rewrite map_map.
    replace (fun x => map opp (map opp x)) with (fun x : list A => x).
    rewrite map_id; auto.
    apply functional_extensionality. intros.
    rewrite map_map.
    replace (fun x => opp (opp x)) with (fun x : A => x).
    rewrite map_id; auto.
    apply functional_extensionality; auto.
  Qed.
    
  Definition matsub {r c} (m1 m2 : @mat A r c) : @mat A r c :=
    matmap2 sub m1 m2.
    
  Lemma matsub_comm : forall {r c} (m1 m2 : @mat A r c),
    matsub m1 m2 = matopp (matsub m2 m1).
  Proof.
    intros. apply meq_iff; simpl. unfold matmapdl,matmap2dl. simpl.
    unfold matmap2dl.
    apply dlsub_comm with (c:=c); try apply mat_width;
    repeat rewrite mat_height; auto.
  Qed.
  
  Lemma matsub_assoc2 : forall {r c} (m1 m2 m3 : @mat A r c),
    matmap2 sub (matmap2 sub m1 m2) m3 = 
    matmap2 sub m1 (matmap2 add m2 m3).
  Proof.
    intros. apply meq_iff; simpl.
    apply dlsub_assoc2 with (r:=r) (c:=c); try apply mat_width;
    repeat rewrite mat_height; auto.
  Qed.
  
  (** 0 - m = - m *)
  Lemma matsub_zero_l : forall {r c} (m : @mat A r c),
    matmap2 sub (matzero A0 r c) m = matmap opp m.
  Proof.
    intros. apply meq_iff; simpl. unfold matmap2dl.
    apply dlsub_zero_l; auto. apply mat_height. apply mat_width.
  Qed.
  
  (** m - 0 = m *)
  Lemma matsub_zero_r : forall {r c} (m : @mat A r c),
    matmap2 sub m (matzero A0 r c) = m.
  Proof.
    intros. apply meq_iff; simpl. unfold matmap2dl.
    apply dlsub_zero_r; auto. apply mat_height. apply mat_width.
  Qed.
  
  (** m - m = 0 *)
  Lemma matsub_self : forall {r c} (m : @mat A r c),
    matmap2 sub m m = (matzero A0 r c).
  Proof.
    intros. apply meq_iff; simpl. unfold matmap2dl.
    apply dlsub_self; auto. apply mat_height. apply mat_width.
  Qed.

End matsub_opp.

Arguments matsub {A} opp add {r c}.
Arguments matopp {A} opp {r c}.


(** ** matrix multiplication *)
Section matmul.
  
  Variable A : Type.
  Variable A0 : A.
  Variable add mul : A -> A -> A.
 
  Variable r c t : nat.
  Variable m1 : @mat A r c.
  Variable m2 : @mat A c t.
  
  Let data : list (list A) :=
      dldotdl A0 add mul (mat_data m1) (mat_data (mat_trans m2)).
  
  Let cond_h : length (data) = r.
  Proof.
    intros. unfold data. destruct m1,m2; simpl in *.
    rewrite dldotdl_height with (r1:=r) (r2:=t) (c:=c); auto.
    apply dltrans_height; auto. apply dltrans_width; auto.
  Qed.
  
  Let cond_w : width (data) t.
  Proof.
    intros. unfold data. destruct m1,m2; simpl in *.
    apply dldotdl_width with (r1:=r) (r2:=t) (c:=c); auto.
    apply dltrans_height; auto. apply dltrans_width; auto.
  Qed.
  
  (** matrix multiplication *)
  Definition matmul : @mat A r t := mk_mat data cond_h cond_w.
  
End matmul.

Arguments matmul {A} A0 add mul {r c t}.


(** ** Multiplication with a constant and a matrix *)
Section matcmul_matmulc.

  Variable A : Type.
  Variable A0 A1 : A.
  Variable add mul : A -> A -> A.
  Variable opp : A -> A.
  Infix "+" := add.
  Infix "*" := mul.
  Notation "- x" := (opp x).
  Variable mul_comm : forall a b, a * b = b * a.
  Variable mul_assoc : forall a b c, (a * b) * c = a * (b * c).
  Variable mul_add_distr_l : forall a b1 b2,
    a * (b1 + b2) = a * b1 + a * b2.
  Variable mul_add_distr_r : forall a1 a2 b,
    (a1 + a2) * b = a1 * b + a2 * b.
  Variable mul_1_l : forall a : A, A1 * a = a.
  Variable mul_neg : forall a b : A, (- a) * b = - (a * b).
  Variable mul_neg_neg : forall a b : A, (-a) * (-b) = a * b.
  Variable mul_0_l : forall a : A, A0 * a = A0.

  Variable r c : nat.
  
  Section matcmul.
    Variable a : A.
    Variable m : @mat A r c.
  
    Let data : list (list A) :=
      dmap (fun x => mul a x) (mat_data m).
    
    Let cond_h : length (data) = r.
    Proof.
      intros. unfold data. destruct m; simpl in *.
      rewrite dmap_height. auto.
    Qed.
    
    Let cond_w : width (data) c.
    Proof.
      intros. unfold data. destruct m; simpl in *.
      apply dmap_width. auto.
    Qed.
    
    (** a * M *)
    Definition matcmul : @mat A r c := mk_mat data cond_h cond_w.
  End matcmul.
  
  Section matmulc.
    Variable m : @mat A r c.
    Variable a : A.
    
    Let data : list (list A) :=
      dmap (fun x => mul x a) (mat_data m).
    
    Let cond_h : length (data) = r.
    Proof.
      intros. unfold data. destruct m; simpl in *.
      rewrite dmap_height. auto.
    Qed.
    
    Let cond_w : width (data) c.
    Proof.
      intros. unfold data. destruct m; simpl in *.
      apply dmap_width. auto.
    Qed.
    
    (** M * a *)
    Definition matmulc : @mat A r c := mk_mat data cond_h cond_w.
  End matmulc.
  
  (** a * M = M * a *)
  Lemma matmulc_eq_matcmul a m : matmulc m a = matcmul a m.
  Proof.
    destruct m. apply meq_iff. simpl. f_equal.
    apply functional_extensionality. auto.
  Qed.
  
  (** a * (b * M) = (a * b) * M *)
  Lemma matcmul_assoc1 : forall m a1 a2,
    matcmul a1 (matcmul a2 m) = matcmul (mul a1 a2) m.
  Proof.
    intros. destruct m as [dl]. apply meq_iff. simpl. unfold dmap.
    rewrite map_map. f_equal. apply functional_extensionality. intros.
    rewrite map_map. f_equal. apply functional_extensionality. auto.
  Qed.
  
  (** a * (b * M) = (a * b) * M *)
  Lemma matcmul_assoc2 : forall m a1 a2,
    matcmul a1 (matcmul a2 m) = matcmul a2 (matcmul a1 m).
  Proof.
  
    intros. destruct m as [dl]. apply meq_iff. simpl.
    remember (fun x : A => mul a1 x).
    remember (fun x : A => mul a2 x).
    unfold dmap.
    repeat rewrite map_map. f_equal. apply functional_extensionality. intros.
    repeat rewrite map_map. f_equal. apply functional_extensionality. intros.
    rewrite Heqa. rewrite Heqa0.
    repeat rewrite <- mul_assoc. f_equal. auto.
  Qed.
  
  (** a * (M1 + M2) = (a * M1) + (a * M2) *)
  Lemma matcmul_distr_l : forall a m1 m2,
    matcmul a (matadd add m1 m2) = matadd add (matcmul a m1) (matcmul a m2).
  Proof.
    intros. destruct m1 as [d1 d1H d1W], m2 as [d2 d2H d2W].
    apply meq_iff. simpl. unfold matmap2dl; simpl.
    rewrite dmap2_dmap_hom; auto.
  Qed.
  
  (** (a1 + a2) * M = (a1 * M) + (a2 * M) *)
  Lemma matcmul_distr_r : forall a1 a2 m,
    matcmul (add a1 a2) m = matadd add (matcmul a1 m) (matcmul a2 m).
  Proof.
    intros. destruct m as [dl dlH dlW]. apply meq_iff; simpl.
    unfold matmap2dl; simpl.
    gd c. gd r. gd a2. gd a1. clear c r. induction dl; intros; auto.
    repeat rewrite dlmap_cons. simpl in *. destruct dlW.
    rewrite IHdl with (r:=pred r) (c:=c); auto.
    - f_equal. remember (dmap (fun x : A => mul a1 x) dl) as dl1.
      rewrite map2_map_map with (g:=(fun x : A => mul (add a1 a2) x)).
      auto. auto.
    - subst. auto.
  Qed.
  
  (* 0 c* m = mat0 *)
  Lemma matcmul_0_l : forall (m : mat r c), matcmul A0 m = matzero A0 r c.
  Proof.
    intros. destruct m as [d1 d1H d1W]. unfold matzero.
    apply meq_iff. simpl.
    replace (fun x => mul A0 x) with (fun x : A => A0).
    apply dmap_to0_eq_dlzero; auto.
    apply functional_extensionality. intros. rewrite mul_0_l. auto.
  Qed.
  
  (* 1 c* m = m *)
  Lemma matcmul_1 : forall m, matcmul A1 m = m.
  Proof.
    intros. destruct m as [d1 d1H d1W].
    apply meq_iff. simpl. unfold dmap.
    replace (map (fun x : A => mul A1 x)) with (fun x : list A => x).
    rewrite map_id; auto.
    apply functional_extensionality. intros.
    replace (fun x : A => mul A1 x) with (fun x : A => x).
    rewrite map_id; auto.
    apply functional_extensionality. intros. rewrite mul_1_l. auto.
  Qed.
  
  (* (-a) * m = - (a * m) *)
  Lemma mcmul_neg : forall a (m : mat r c), 
    matcmul (opp a) m = matopp opp (matcmul a m).
  Proof.
    intros. destruct m as [d1 d1H d1W].
    apply meq_iff. simpl. unfold dmap. unfold matmapdl. unfold dmap. simpl.
    unfold dmap. rewrite map_map. f_equal.
    apply functional_extensionality. intros.
    rewrite map_map. f_equal.
    apply functional_extensionality. intros. auto.
  Qed.
  
  (* (-a) * (- m) = (a * m) *)
  Lemma mcmul_neg_mopp : forall a (m : mat r c), 
    matcmul (opp a) (matopp opp  m) = matcmul a m.
  Proof.
    intros. destruct m as [d1 d1H d1W].
    apply meq_iff. simpl. unfold dmap. unfold matmapdl. unfold dmap. simpl.
    unfold dmap. rewrite map_map. f_equal.
    apply functional_extensionality. intros.
    rewrite map_map. f_equal.
    apply functional_extensionality. intros. auto.
  Qed.
  
  (** (m <> 0 /\ k * m = 0) -> k = 0 *)
  Lemma mcmul_non0_eq_0_imply_k0 : forall k (m : mat r c),
    let m0 := matzero A0 r c in
      ((m <> m0) /\ (matcmul k m = m0)) -> k = A0.
  Proof.
    intros. unfold m0 in *. destruct H.
    destruct m. unfold matzero in *.
    apply meq_iff in H0. apply meq_iff_not in H. simpl in *.
    rename mat_data0 into dl.
    clear m0. gd c. gd r. gd dl.
    induction dl; intros.
    - simpl in *. subst. contradiction.
    - destruct r0.
      + simpl in *. lia.
      + simpl in *. destruct mat_width0.
        inversion H0. apply IHdl with (r:=r0) (c:=c0); auto.
        * unfold dlzero in *. simpl in H.
          assert (~((a = lzero A0 c0) /\ (dl = repeat (lzero A0 c0) r0))).
          { intro. destruct H3.
          assert ((a <> lzero A0 c0) \/ (dl <> repeat (lzero A0 c0) r0)).
          { 
(*           Search (not (_ /\ _)). *)
(*           Print Decidable.not_and. *)
          Abort.
  
End matcmul_matmulc.

Arguments matcmul {A} mul {r c}.
Arguments matmulc {A} mul {r c}.


(** ** matrix multiplication properties *)
Section matmul_props.
  
  Variable A : Type.
  Variable A0 A1 : A.
  Variable add mul : A -> A -> A.
  Infix "+" := add.
  Infix "*" := mul.
  Variable add_comm : forall a b, a + b = b + a.
  Variable mul_comm : forall a b, a * b = b * a.
  Variable add_assoc : forall a b c, (a + b) + c = a + (b + c).
  Variable mul_assoc : forall a b c, (a * b) * c = a * (b * c).
  Variable mul_add_distr_l : forall a b1 b2,
    a * (b1 + b2) = a * b1 + a * b2.
  Variable mul_add_distr_r : forall a1 a2 b,
    (a1 + a2) * b = a1 * b + a2 * b.
  Variable add_0_l : forall a, A0 + a = a.
  Variable mul_0_l : forall a, A0 * a = A0.
  Variable mul_1_l : forall a, A1 * a = a.
  
  Notation matadd := (matadd add).
  Notation matmul := (matmul A0 add mul).
  
  (** matrix muliplication left distributve over addition. 
    A * (B + C) = A * B + A * C *)
  Lemma matmul_add_distr_l : forall {r c t} (m1 : @mat A r c) 
    (m2 m3 : @mat A c t),
    matmul m1 (matadd m2 m3) = matadd (matmul m1 m2) (matmul m1 m3).
  Proof.
    intros. apply meq_iff. destruct m1,m2,m3; simpl in *.
    unfold matmul, matadd; simpl. unfold matmap2dl; simpl in *.
    rewrite dltrans_dmap2 with (r:=c) (c:=t); auto.
    rewrite dldotdl_dmap2_distr_r with (r:=r) (c:=c) (t:=t); auto;
    try apply dltrans_height; try apply dltrans_width; auto.
  Qed.
  
  (** matrix muliplication right distributve over addition. 
    (A + B) * C = A * C + B * C *)
  Lemma matmul_add_distr_r : forall {r c t} (m1 m2 : @mat A r c) 
    (m3 : @mat A c t),
    matmul (matadd m1 m2) m3 = matadd (matmul m1 m3) (matmul m2 m3).
  Proof.
    intros. apply meq_iff. destruct m1,m2,m3; simpl in *.
    unfold matmul, matadd; simpl. unfold matmap2dl; simpl in *.
    rewrite dldotdl_dmap2_distr_l with (r:=r) (c:=c) (t:=t); auto.
    rewrite dltrans_height; auto.
    apply dltrans_width; auto.
  Qed.
  
  (** matrix muliplication association. 
    (A * B) * C = A * (B * C) *)
  Lemma matmul_assoc : forall {r c t s} (m1 : @mat A r c) (m2 : @mat A c t)
    (m3 : @mat A t s),
    matmul (matmul m1 m2) m3 = matmul m1 (matmul m2 m3).
  Proof.
    intros. apply meq_iff. destruct m1,m2,m3; simpl in *.
    rewrite dldotdl_assoc with (r:=r) (c:=c) (t:=t) (s:=s); auto;
    try rewrite dltrans_height; try apply dltrans_width; auto.
  Qed.
  
  (** 0 * A = 0 *)
  Lemma matmul_0_l : forall {r c t} (m : @mat A c t),
    matmul (matzero A0 r c) m = matzero A0 r t.
  Proof.
    intros. apply meq_iff. destruct m; simpl in *.
    rewrite dldotdl_zero_l with (t:=t); auto.
    apply dltrans_height; auto. apply dltrans_width; auto.
  Qed.
  
  (** A * 0 = 0 *)
  Lemma matmul_0_r : forall {r c t} (m : @mat A r c),
    matmul m (matzero A0 c t) = matzero A0 r t.
  Proof.
    intros. apply meq_iff. destruct m; simpl in *.
    rewrite dltrans_zero. rewrite dldotdl_zero_r with (r:=r); auto.
  Qed.
  
  (** 1 * A = A *)
  Lemma matmul_1_l : forall {r c} (m : @mat A r c),
    matmul (matunit A0 A1 r) m = m.
  Proof.
    intros. apply meq_iff. destruct m; simpl in *.
    rewrite dldotdl_dlunit_l with (r:=c); auto;
    try apply dltrans_height; try apply dltrans_width; auto.
    apply dltrans_trans; auto.
  Qed.
  
  (** A * 1 = A *)
  Lemma matmul_1_r : forall {r c} (m : @mat A r c),
    matmul m (matunit A0 A1 c) = m.
  Proof.
    intros. apply meq_iff. destruct m; simpl in *.
    rewrite dltrans_dlunit.
    rewrite dldotdl_dlunit_r with (r:=r); auto;
    try apply dltrans_height; try apply dltrans_width; auto.
  Qed.

End matmul_props.

(** Matrix 1 1 to scalar *)
Section mat_1_1_to_scalar.
  
  Variable A : Type.
  Variable A0 : A.
  
  Definition mat_1_1_to_s (m : @mat A 1 1) : A.
  Proof.
    destruct m as [dl].
    refine (hd A0 (hd [] dl)).
  Defined.
  
End mat_1_1_to_scalar.

Arguments mat_1_1_to_s {A}.


(** Convert from list list to mat *)

Section l2m.
  Variable A : Type.
  Variable A0 : A.
  
  (* list to fixed-length list *)
  Fixpoint l2v_aux (l : list A) (n : nat) : list A :=
    match n with
    | 0 => []
    | S n' => (hd A0 l) :: (l2v_aux (tl l) n')
    end.
  
  Lemma l2v_aux_length : forall (l : list A) (n : nat),
    length (l2v_aux l n) = n.
  Proof.
    intros l n. gd l. induction n; intros; simpl; auto.
  Qed.
  
  Lemma l2v_aux_eq : forall (l : list A) (n : nat) 
    (H1 : length l = n), l2v_aux l n = l.
  Proof.
    intros l n. gd l. induction n; intros; simpl.
    - apply length_zero_iff_nil in H1; auto.
    - rewrite IHn.
      + (* hd A0 l :: tl l = l *)
        induction l; simpl in *. lia. auto.
      + destruct l; simpl in *. lia. auto.
  Qed.
  
  (* list list to fixed-shape list list *)
  Fixpoint l2m_aux (dl : list (list A)) (r c : nat) : list (list A)
    := match r with
    | 0 => []
    | S n' => (l2v_aux (hd nil dl) c) :: (l2m_aux (tl dl) n' c)
    end.
  
  Lemma l2m_aux_length : forall (dl : list (list A)) (r c : nat),
    length (l2m_aux dl r c) = r.
  Proof.
    intros dl r. gd dl. induction r; intros; simpl; auto.
  Qed.
  
  Lemma l2m_aux_width : forall (dl : list (list A)) (r c : nat),
    width (l2m_aux dl r c) c.
  Proof.
    intros dl r. gd dl. induction r; intros; simpl; auto. split; auto.
    apply l2v_aux_length.
  Qed.
  
  Lemma l2m_aux_eq : forall (dl : list (list A)) (r c : nat) 
    (H1 : length dl = r) (H2 : width dl c),
    l2m_aux dl r c = dl.
  Proof.
    intros dl r. gd dl. induction r; intros; simpl; auto.
    - apply length_zero_iff_nil in H1. auto.
    - rewrite IHr; auto.
      + rewrite l2v_aux_eq.
        destruct dl; simpl in *; auto. lia.
        destruct dl; simpl in *. lia. destruct H2; auto.
      + destruct dl; simpl in *; auto. lia.
      + destruct dl; simpl in *; auto. destruct H2; auto.
  Qed.

  Definition l2m (dl : list (list A)) (r c : nat) : mat r c :=
    mk_mat (l2m_aux dl r c) (l2m_aux_length dl r c) (l2m_aux_width dl r c).
    
  Lemma l2m_inj : forall {r c} (d1 d2 : list (list A)),
    length d1 = r -> width d1 c -> 
    length d2 = r -> width d2 c -> 
    d1 <> d2 -> l2m d1 r c <> l2m d2 r c.
  Proof.
    intros. apply meq_iff_not. simpl.
    rewrite ?l2m_aux_eq; auto.
  Qed.
  
  Lemma l2m_surj : forall {r c} (m : mat r c), 
    (exists d, l2m d r c = m).
  Proof.
    intros. exists (mat_data m). apply meq_iff. simpl.
    rewrite l2m_aux_eq; auto.
    apply mat_height. apply mat_width.
  Qed.
    
End l2m.

Arguments l2v_aux {A}.
Arguments l2m_aux {A}.
Arguments l2m_aux_length {A}.
Arguments l2m_aux_width {A}.
Arguments l2m {A}.



(* ######################################################################### *)
(** * Matrix Inverse *)
Section MatInv.

  
  (* ======================================================================= *)
  (** ** permutation *)
  Section Permutation.
    
  End Permutation.
  
  Variable A : Type.
  
(*   Check mat. *)


End MatInv.

