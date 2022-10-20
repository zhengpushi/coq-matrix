(*
  purpose   : Matrix implementation with List List
  author    : ZhengPu Shi
  date      : 2021.12
  
  remark    :
  1. Notation priority.
  
  m1 = m2      70
  m1 +  m2      50
  m1 -  m2      50
     - m        
  m1 ×  m2      40
  c  c* m       35
  m  *c m       35
     m ⊤        30
  
*)

Require Export MatrixThySig.
Require Export DepRec.Matrix.


(* ######################################################################### *)
(** * Matrix theory *)
Module MatrixThy (F : FieldSig) <: MatrixThySig F.

  Module Export FieldThyInst := FieldThy F.

  Open Scope X_scope.
  Open Scope mat_scope.
  
  (** Type of matrix *)
(*   Check mat. *)
  Definition mat X r c := @mat X r c.
  Notation M r c := (@mat X r c).
  
  (** Equality of matrix, iff, equality of the matrix data *)
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
  Qed.
  
  (** The equality is decidable *)
  Lemma meq_dec : forall {r c} (m1 m2 : M r c), {m1 = m2} + {m1 <> m2}.
  Proof.
    intros.
    destruct m1 as (dl1,h1,w1), m2 as (dl2,h2,w2).
    assert ({dl1 = dl2} + {dl1 <> dl2}).
    apply (@dlist_eq_dec X Xeqdec dl1 dl2); auto.
    destruct H.
    - subst. left. apply meq_iff. auto.
    - right. unfold not. intros. apply meq_iff in H. simpl in *. auto.
  Qed.

  (** Get element of a matrix *)  
  Definition mnth {r c} (m : M r c) (ri ci : nat) :=
    @mat_nth X X0 r c m ri ci.
  
  Lemma meq_iff_mnth : forall {r c : nat} (m1 m2 : M r c),
    m1 = m2 <-> 
    (forall ri ci (Hri : (ri < r)%nat) (Hci : (ci < c)%nat),
      mnth m1 ri ci = mnth m2 ri ci).
  Proof.
    intros. apply meq_iff_mnth.
  Qed.
  
  (** Create specific matrix *)
  Definition mk_mat_1_1 (a11 : X) : @M 1 1 
    := @mk_mat_1_1 X a11.
  Definition mk_mat_3_1 (a1 a2 a3 : X) : @M 3 1 
    := @mk_mat_3_1 X a1 a2 a3.
  Definition mk_mat_3_3 (a11 a12 a13 a21 a22 a23 a31 a32 a33 : X) : @M 3 3 
    := @mk_mat_3_3 X a11 a12 a13 a21 a22 a23 a31 a32 a33.
  Definition mk_mat_2_2 (a11 a12 a21 a22 : X) : @M 2 2 
    := @mk_mat_2_2 X a11 a12 a21 a22.
  
  (** Zero matrix *)
  Definition mat0 r c : M r c := matzero X0 r c.
  
  (** X matrix is a nonzero matrix *)
  Definition matnonzero {r c} (m : M r c) : Prop := m <> mat0 r c.
  
  (** Unit matrix *)
  Definition mat1 n : M n n := matunit X0 X1 n.
  
  (** Mapping of a matrix *)
  Definition mmap {r c} (f : X -> X) (m : M r c) : M r c :=
    @matmap X X f r c m.
  
  (** Mapping of two matrices *)
  Definition mmap2 {r c} (f : X -> X -> X) (m1  m2 : M r c) : M r c :=
    @matmap2 X X X f r c m1 m2.
  
  Lemma mmap2_comm : forall {r c} (f : X -> X -> X)
    (f_comm : forall a b : X, f a b = f b a) (m1 m2 : M r c), 
    mmap2 f m1 m2 = mmap2 f m2 m1.
  Proof.
    intros. apply @matmap2_comm. auto.
  Qed.
  
  Lemma mmap2_assoc : forall {r c} (f : X -> X -> X)
    (f_assoc : forall a b c, f a (f b c) = f (f a b) c) (m1 m2 m3 : M r c), 
    mmap2 f (mmap2 f m1 m2) m3 = mmap2 f m1 (mmap2 f m2 m3).
  Proof.
    intros. apply @matmap2_assoc. auto.
  Qed.
  
  (** Addition of matrix *)
  Definition madd {r c} := @matadd X Xadd r c.
  Global Notation "m1 + m2" := (madd m1 m2) : mat_scope.
  
  Lemma madd_comm : forall {r c} (m1 m2 : M r c), m1 + m2 = m2 + m1.
  Proof.
    apply @matadd_comm. intros. cbv. ring.
  Qed.
  
  Lemma madd_assoc : forall {r c} (m1 m2 m3 : M r c),
    (m1 + m2) + m3 = m1 + (m2 + m3).
  Proof. apply @matadd_assoc. intros;cbv; ring. Qed.
  
  Lemma madd_0_l : forall {r c} (m : M r c), (mat0 r c) + m = m.
  Proof. apply @matadd_zero_l. intros;cbv; ring. Qed.
  
  Lemma madd_0_r : forall {r c} (m : M r c), m + (mat0 r c) = m.
  Proof. apply @matadd_zero_r; intros;cbv; ring. Qed.
  
  (** Opposite of matrix *)
  Definition mopp {r c} (m : M r c) : M r c := @matopp X Xopp r c m.
  Global Notation "- m" := (mopp m) : mat_scope.
    
  Lemma mopp_opp : forall {r c} (m : M r c), - - m = m.
  Proof. apply @matopp_matopp. intros;cbv; ring. Qed.
  
  Lemma mopp_exchange : forall {r c} (m1 m2 : M r c), 
    -m1 = m2 <-> m1 = -m2.
  Proof.
    intros. split; intros.
    - rewrite <- H. rewrite mopp_opp. reflexivity.
    - rewrite -> H. rewrite mopp_opp. reflexivity.
  Qed.
  
  Lemma mopp_mat0 : forall {r c}, - (mat0 r c) = mat0 r c.
  Proof.
    intros. apply meq_iff. unfold mat0 in *. unfold matzero in *.
    simpl in *. unfold matmapdl. unfold dmap. unfold dlzero. simpl.
    induction r; intros; simpl; auto.
    f_equal; auto.
     (* map opp (lzero 0 c) = lzero 0 c *)
    clear. gd c. induction c; simpl; auto. f_equal; auto. cbv. ring.
  Qed.
  
  Lemma madd_opp : forall {r c} (m : M r c), m + (-m) = mat0 r c.
  Proof.
    intros. apply meq_iff. destruct m; simpl.
    unfold mopp. unfold matmap2dl. simpl.
    unfold matmapdl. simpl.
    rename mat_data into dl. gd c. gd r. induction dl; simpl; intros.
    - subst. compute. auto.
    - destruct r; try lia.
      inversion mat_height. destruct mat_width.
      rewrite (IHdl r H0 c); auto.
      unfold dlzero. simpl. subst. f_equal.
      rename a into l. clear.
      (* lmap2 add l (map opp l) = lzero 0 (length l) *)
      induction l; simpl; auto. rewrite IHl. f_equal. cbv; ring.
  Qed.
  
  Definition msub {r c} := @matsub X Xopp Xadd r c.
  Global Notation "m1 - m2" := (msub m1 m2) : mat_scope.
  
  Lemma msub_comm : forall {r c} (m1 m2 : M r c), m1 - m2 = - (m2 - m1).
  Proof. apply @matsub_comm. intros;cbv; ring. Qed.
  
  Lemma msub_assoc : forall {r c} (m1 m2 m3 : M r c), 
    msub (msub m1 m2) m3 = msub m1 (madd m2 m3).
  Proof. apply @matsub_assoc2. intros;cbv; ring. Qed.
    
  Lemma msub_0_l : forall {r c} (m : M r c), msub (mat0 r c) m = mopp m.
  Proof. apply @matsub_zero_l. intros;cbv; ring. Qed.
  
  Lemma msub_0_r : forall {r c} (m : M r c), msub m (mat0 r c) = m.
  Proof.
    apply @matsub_zero_r. intros; cbv; ring.
  Qed.
  
  Lemma msub_self : forall {r c} (m : M r c), msub m m = (mat0 r c).
  Proof.
    apply @matsub_self. intros; cbv; ring.
  Qed.
  
  (** 矩阵数乘 *)
  Definition mcmul {r c} (a : X) (m : M r c) : M r c :=
    @matcmul X Xmul r c a m.
  
  Global Notation "a c* m" := (mcmul a m) : mat_scope.
  
  Definition mmulc {r c} (m : M r c) (a : X) : M r c :=
    @matmulc X Xmul r c m a.
  
  Global Notation "m *c a" := (mmulc m a) : mat_scope.
  
  Lemma mmulc_eq_mcmul : forall {r c} (a : X) (m : M r c), 
    mmulc m a = mcmul a m.
  Proof.
    apply @matmulc_eq_matcmul. intros; compute; ring.
  Qed.

  Lemma mcmul_assoc : forall {r c} (a b : X) (m : M r c), 
    a c* (b c* m) = (a * b) c* m.
  Proof.
    intros. apply @matcmul_assoc1. intros; cbv; ring.
  Qed.
  
  Lemma mcmul_perm : forall {r c} (a b : X) (m : M r c), 
    a c* (b c* m) = b c* (a c* m).
  Proof.
    intros. apply @matcmul_assoc2; intros;cbv; ring.
  Qed.
  
  Lemma mcmul_add_distr_l : forall {r c} (a : X) (m1 m2 : M r c), 
    mcmul a (madd m1 m2) = madd (mcmul a m1) (mcmul a m2).
  Proof.
    apply @matcmul_distr_l. intros;cbv; ring.
  Qed.
  
  Lemma mcmul_add_distr_r : forall {r c} (a b : X) (m : M r c), 
    mcmul (Xadd a b) m = madd (mcmul a m) (mcmul b m).
  Proof.
    apply @matcmul_distr_r. intros;cbv; ring.
  Qed.
  
  (* 0 c* m = mat0 *)
  Lemma mcmul_0_l : forall {r c} (m : M r c), X0 c* m = mat0 r c.
  Proof.
    intros. apply matcmul_0_l. intros;cbv; ring.
  Qed.
  
  (* 1 * m = m *)
  Lemma mcmul_1_l : forall {r c} (m : M r c), 
    mcmul X1 m = m.
  Proof.
    apply matcmul_1. intros;cbv; ring.
  Qed.
  
  (* (-a) * m = - (a * m) *)
  Lemma mcmul_neg : forall {r c} a (m : M r c), 
    (Xopp a) c* m = - (a c* m).
  Proof.
    intros. apply mcmul_neg. intros;cbv; ring.
  Qed.
  
  (* (-a) * (- m) = (a * m) *)
  Lemma mcmul_neg_mopp : forall {r c} a (m : M r c), 
    (Xopp a) c* (mopp m) = (a c* m).
  Proof.
    intros. apply mcmul_neg_mopp. intros;cbv; ring.
  Qed.

  (* a * m = m -> a = 1 \/ m = 0 *)
  Lemma mcmul_same_imply_coef1_or_mzero : forall {r c} a (m : M r c),
    a c* m = m -> (a = X1) \/ (m = mat0 r c).
  Proof.
    intros. destruct m. unfold mcmul in H. unfold matcmul in H.
    unfold mat0. unfold matzero.
    inversion H. apply meq_iff in H. simpl in H. unfold dmap in H.
    (* a good view *)
    destruct (Xeqdec a X1).
    - left; auto.
    - assert (a = X1 \/ mat_data = dlzero X0 r c).
      + destruct (@dlcmul_fixpoint_imply_k1_or_dlzero X X0 X1 Xmul) 
        with (r:=r) (c:=c) (k:=a) (dl:=mat_data); auto; try (intros;cbv; ring).
        apply Xeqdec. intros. apply mul_cancel_r with r0; auto.
      + destruct H0; auto. right. apply meq_iff. simpl. auto.
  Qed.
  
  (* 某两个非零矩阵存在k倍关系，则系数k不为0 *)
  Lemma mat_eq_mcmul_implfy_coef_neq0 : forall {r c} (m1 m2 : M r c) k,
    matnonzero m1 -> matnonzero m2 -> (m1 = k c* m2) -> k <> X0.
  Proof.
    intros. intro. rewrite H2 in H1. rewrite mcmul_0_l in H1. apply H in H1.
    auto.
  Qed.
  
  (* 非零矩阵乘以k倍为零矩阵，则k为0 *)
  Lemma mcmul_mnonzero_eq0_imply_k0 : forall {r c} (m : M r c) k,
    matnonzero m -> mat0 r c = k c* m -> k = X0.
  Proof.
    intros. unfold matnonzero in H. destruct m. 
    apply meq_iff_not in H. apply meq_iff in H0. simpl in *.
    (* 已转到 list 上的操作 *)
    assert (dmap (fun x : X => k * x) mat_data =
      dmap (fun x : X => X0) mat_data).
    rewrite (@dmap_to0_eq_dlzero _ X0 r c mat_data).
    (* ?
    inversion H1.
    rewrite H1 in H0. r c).
    rewrite <- (dlmap_to0_eq_dlzero _ mat_data) in H0.
     ? destruct H. intro.
    Admitted. *)
    Abort.
    
  (** 矩阵转置 *)
  Definition mtrans {r c} (m : M r c): M c r :=
    @mat_trans X r c m.
  
  Global Notation "m 'ᵀ'" := (mtrans m) : mat_scope.
  
  Lemma mtrans_trans : forall {r c} (m : M r c), mtrans (mtrans m) = m.
  Proof.
    apply @mat_trans_trans.
  Qed.
  
  (** 矩阵乘法 *)
  Definition mmul {r c s} (m1 : M r c) (m2 : M c s) : M r s :=
    @matmul X X0 Xadd Xmul r c s m1 m2.
  
  Global Notation "m1 * m2" := (mmul m1 m2) : mat_scope.
  
  Lemma mmul_add_distr_l : forall {r c X} (m1 : M r c) (m2 m3 : M c X),
    m1 * (m2 + m3) = m1 * m2 + m1 * m3.
  Proof.
    apply @matmul_add_distr_l; intros;cbv; ring.
  Qed.
  
  Lemma mmul_add_distr_r : forall {r c s} (m1 m2 : M r c) (m3 : M c s),
    (m1 + m2) * m3 = (m1 * m3) + (m2 * m3).
  Proof.
    apply @matmul_add_distr_r; intros;cbv; ring.
  Qed.
  
  Lemma mmul_assoc : forall {r c s X} (m1 : M r c) (m2 : M c s) 
    (m3 : M s X),
    (m1 * m2) * m3 = m1 * (m2 * m3).
  Proof.
    apply @matmul_assoc; intros;cbv; ring.
  Qed.
  
  Lemma mmul_0_l : forall {r c X} (m : M c X), (mat0 r c) * m = mat0 r X.
  Proof.
    apply @matmul_0_l; intros;cbv; ring.
  Qed.
  
  Lemma mmul_0_r : forall {r c X} (m : M r c), m * (mat0 c X) = mat0 r X.
  Proof.
    apply @matmul_0_r; intros;cbv; ring.
  Qed.
  
  Lemma mmul_1_l : forall {r c} (m : M r c), (mat1 r) * m = m.
  Proof.
    apply @matmul_1_l; intros;cbv; ring.
  Qed.
  
  Lemma mmul_1_r : forall {r c} (m : M r c), m * (mat1 c) = m.
  Proof.
    apply @matmul_1_r; intros;cbv; ring.
  Qed.
  
  (** Vector type *)
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
  Defined.
(*   
  (** Equality of two forms of ConstructByRow *)
  Lemma mconsr_eq {r c} (v : @vec X c) (m : @M X r c) : mconsr v m = (v, m).
  Proof. unfold mconsr. auto. Qed.
  
  (** Construct a matrix by rows with the matrix which row number is 0 *)
  Lemma mconsr_mr0 : forall {n} (v : @vec X n) (m : @M X 0 n),
    mconsr v m = [v].
  Proof. intros. destruct m. unfold mconsr. auto. Qed.
  
  (** Construct a matrix by rows with the matrix which row column is 0 *)
  Lemma mconsr_mc0 : forall {n} (v : @vec X 0) (m : @M X n 0),
    mconsr v m = (tt, m).
  Proof. intros. destruct v. unfold mconsr. auto. Qed.
  
  (** Construct a matrix by columns with the matrix which row number is 0 *)
  Lemma mconsc_mr0 : forall {n} (v : @vec X 0) (m : @vec (@vec X n) 0),
    mconsc v m = tt.
  Proof. intros. destruct m. unfold mconsc. auto. Qed.
 *)  
  
  
  (** useful tactic for solving X = B for concrete X, B *)
 
  (* 列表相等，转换为元素相等 *)
  Ltac list_eq :=
    repeat match goal with
    | |- cons _ _ = _ => f_equal
    end.
  
  (* 处理 X = B *)
  Ltac lma :=
    compute;    (* 展开、化简 *)
    list_eq;    (* 列表相等 => 元素相等 *)
    ring        (* 多项式相等 *)
    .
  
  (** list list 与 矩阵互转 *)
  
  (* 这里条件太强了，其他矩阵实现不一定能满足，因此重新做一份 *)
  Definition l2m_old {r c} (dl : list (list X)) (H1 : length dl = r)
    (H2 : width dl c) : M r c := mk_mat dl H1 H2.

  Definition l2m {r c} (dl : list (list X)) : M r c :=
    Matrix.l2m X0 dl r c.
  
  Definition m2l {r c} (m : M r c) : list (list X) := mat_data m.
  
  Lemma m2l_length : forall {r c} (m : M r c), length (m2l m) = r.
  Proof.
    intros. unfold m2l. destruct m. auto.
  Defined.
  Global Hint Resolve m2l_length : mat.
  
  Lemma m2l_width : forall {r c} (m : M r c), width (m2l m) c.
  Proof.
    intros. unfold m2l. destruct m. auto.
  Defined.
  Global Hint Resolve m2l_width : mat.
  
  Lemma m2l_l2m_id : forall {r c} (dl : list (list X)) (H1 : length dl = r)
    (H2 : width dl c), @m2l r c (l2m dl) = dl.
  Proof.
    intros. unfold m2l,l2m. unfold Matrix.l2m. simpl.
    apply l2m_aux_eq; auto.
  Qed.
  
  Lemma l2m_m2l_id : forall {r c} (m : M r c), l2m (m2l m) = m. 
  Proof.
    intros. unfold m2l,l2m. unfold Matrix.l2m. destruct m.
    apply meq_iff; simpl. apply l2m_aux_eq; auto.
  Qed.
  
  Lemma l2m_inj : forall {r c} (d1 d2 : list (list X)),
    length d1 = r -> width d1 c -> 
    length d2 = r -> width d2 c -> 
    d1 <> d2 -> @l2m r c d1 <> l2m d2.
  Proof. apply l2m_inj. Qed.
  
  Lemma l2m_surj : forall {r c} (m : M r c), 
    (exists d, l2m d = m).
  Proof. apply l2m_surj. Qed.
    
  Lemma m2l_inj : forall {r c} (m1 m2 : M r c),
    m1 <> m2 -> m2l m1 <> m2l m2.
  Proof. intros. apply meq_iff_not in H. auto. Qed.
  
  Lemma m2l_surj : forall {r c} (d : list (list X)), 
    length d = r -> width d c -> 
    (exists m, @m2l r c m = d).
  Proof. intros. exists (mk_mat d H H0). simpl. auto. Qed.
  
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
  Definition m2t_3x3' (m : M 3 3) : @T_3x3 X :=
    ((mnth m 0 0, mnth m 0 1, mnth m 0 2), 
     (mnth m 1 0, mnth m 1 1, mnth m 1 2),
     (mnth m 2 0, mnth m 2 1, mnth m 2 2)).
     
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
    destruct m.
    destruct mat_data; simpl in *; try discriminate.
    destruct mat_data; simpl in *; try discriminate.
    destruct mat_data; simpl in *; try discriminate.
    destruct mat_data; simpl in *; try discriminate.
    destruct mat_width as (?,mat_width).
    destruct mat_width as (?,mat_width).
    destruct mat_width as (?,mat_width).
    destruct l as [| a11]; simpl in *; try discriminate.
    destruct l as [| a12]; simpl in *; try discriminate.
    destruct l as [| a13]; simpl in *; try discriminate.
    destruct l0 as [| a21]; simpl in *; try discriminate.
    destruct l0 as [| a22]; simpl in *; try discriminate.
    destruct l0 as [| a23]; simpl in *; try discriminate.
    destruct l1 as [| a31]; simpl in *; try discriminate.
    destruct l1 as [| a32]; simpl in *; try discriminate.
    destruct l1 as [| a33]; simpl in *; try discriminate.
    apply meq_iff. simpl.
    inversion e. inversion e0. inversion e1.
    apply length_zero_iff_nil in H0,H1,H2. subst. auto.
  Qed.
  
  
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

Import FieldR.
Module Import MatrixR := MatrixThy FieldDefR.

Section coordinate_transform_test.
  
  (* ref:
  https://en.wikipedia.org/wiki/Matrix_(mathematics)#Basic_operations
  *)
  
  Definition m1 := @l2m 2 3 [[1;3;1];[1;0;0]].
  Definition m2 := @l2m 2 3  [[0;0;5];[7;5;0]].
  Definition m3 := @l2m 2 3  [[1;3;6];[8;5;0]].
  Example madd_m1_m2_eq_m3 : m1 + m2 = m3.
  Proof. apply meq_iff. compute. repeat (f_equal; try ring). Qed.
  
  Definition m4 := @l2m 2 3 [[1;8;-3];[4;-2;5]].
  Definition m5 := @l2m 2 3 [[2;16;-6];[8;-4;10]].
  Example mscale_2_m4_eq_m5 : 2 c* m4 = m5.
  Proof. apply meq_iff. compute. repeat (f_equal; try ring). Qed.
  
  Definition m6 := @l2m 2 3 [[1;2;3];[0;-6;7]].
  Definition m7 := @l2m 3 2 [[1;0];[2;-6];[3;7]].
  Example mtrans_m6_eq_m7 : m6 ᵀ = m7.
  Proof. apply meq_iff. compute. repeat (f_equal; try ring). Qed.
  
  
  Variable θ ψ φ : R.
  Definition Rx (α : R) : M 3 3 := mk_mat_3_3
    1         0           0
    0         (cos α)     (sin α)
    0         (-sin α)%R    (cos α).

  Definition Ry (β : R) : M 3 3 := mk_mat_3_3
    (cos β)   0           (-sin β)%R
    0         1           0
    (sin β)   0           (cos β).

  Definition Rz (γ : R) : M 3 3 := mk_mat_3_3 
    (cos γ)   (sin γ)   0
    (-sin γ)%R  (cos γ)   0
    0         0         1.
    
  Definition R_b_e_direct : M 3 3 := (mk_mat_3_3
    (cos θ * cos ψ)
    (cos ψ * sin θ * sin φ - sin ψ * cos φ)
    (cos ψ * sin θ * cos φ + sin φ * sin ψ)
    
    (cos θ * sin ψ)
    (sin ψ * sin θ * sin φ + cos ψ * cos φ)
    (sin ψ * sin θ * cos φ - cos ψ * sin φ)
    
    (-sin θ)
    (sin φ * cos θ)
    (cos φ * cos θ))%X.
   
  Open Scope M.
  Opaque cos sin.
  
  Lemma Rx_Ry_Rz_eq_Rbe : (Rz ψ)ᵀ * (Ry θ)ᵀ * (Rx φ)ᵀ = R_b_e_direct.
  Proof.
    apply meq_iff. simpl. compute. do 6 (f_equal; try ring).
  Qed.
  
End coordinate_transform_test.

