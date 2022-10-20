(*
  purpose   : Implementation with Dependent Pair
  author    : ZhengPu Shi
  date      : 2021.12
*)

Require Export MatrixThySig.

Require Export DepPair.Matrix.


(* ######################################################################### *)
(** * Matrix theory *)
Module MatrixThy (F : FieldSig) <: MatrixThySig F.
  Export F.

  (* 作用域 *)
  Declare Scope mat_scope.
  Delimit Scope mat_scope with M.
  Open Scope mat_scope.
  
  (* 矩阵类型 *)
  Definition mat X r c := @mat X r c.
  Notation M r c := (mat X r c).

  Definition mnth {r c} (m : M r c) (ri ci : nat) :=
    @mnth X X0 r c m ri ci.
  
  Lemma meq_iff_mnth : forall {r c : nat} (m1 m2 : M r c),
    m1 = m2 <-> 
    (forall ri ci, ri < r -> ci < c -> mnth m1 ri ci = mnth m2 ri ci).
  Admitted.
    
  (* 矩阵相等 *)
  Lemma meq_dec : forall {r c} (m1 m2 : M r c), {m1 = m2} + {m1 <> m2}.
  Proof. intros. apply vec_eq_dec. apply vec_eq_dec. apply Xeqdec. Qed.

  (* 构造具体的矩阵 *)

  Definition mk_mat_1_1 (a11 : X) : @M 1 1 := [[a11]].

  Definition mk_mat_3_1 (a1 a2 a3 : X) : @M 3 1 := [[a1];[a2];[a3]].
  
  Definition mk_mat_3_3 (a11 a12 a13 a21 a22 a23 a31 a32 a33 : X) : @M 3 3 
    := [[a11;a12;a13];[a21;a22;a23];[a31;a32;a33]].

  (* 零矩阵和单位矩阵 *)
  Definition mat0 r c : M r c := @mat0 X X0 r c.
  Definition mat1 n : M n n := @mat1 X X0 X1 n.
  
  (* 矩阵映射 *)
  Definition mmap {r c} (f : X -> X) (m : M r c) : M r c :=
    @mmap X f r c m.
    
  Definition mmap2 {r c} (f : X -> X -> X) (m1  m2 : M r c) : M r c :=
    @mmap2 X f r c m1 m2.
 
  Lemma mmap2_comm : forall {r c} (f : X -> X -> X)
    (f_comm : forall a b : X, f a b = f b a) (m1 m2 : M r c), 
    mmap2 f m1 m2 = mmap2 f m2 m1.
  Proof.
    intros. apply @mmap2_comm. auto.
  Qed.
  
  Lemma mmap2_assoc : forall {r c} (f : X -> X -> X)
    (f_assoc : forall a b c, f a (f b c) = f (f a b) c) (m1 m2 m3 : M r c), 
    mmap2 f (mmap2 f m1 m2) m3 = mmap2 f m1 (mmap2 f m2 m3).
  Proof.
    intros. apply @mmap2_assoc. auto.
  Qed.
  
  (* 矩阵加法 *)
  Definition madd {r c} := @madd X Xadd r c.
  
  Global Notation "m1 + m2" := (madd m1 m2) : mat_scope.
  
  Lemma madd_comm : forall {r c} (m1 m2 : M r c), m1 + m2 = m2 + m1.
  Proof.
    apply @madd_comm. intros. ring.
  Qed.
  
  Lemma madd_assoc : forall {r c} (m1 m2 m3 : M r c), 
    (m1 + m2) + m3 = m1 + (m2 + m3).
  Proof.
    apply @madd_assoc. intros; ring.
  Qed.
  
  Lemma madd_0_l : forall {r c} (m : M r c), (mat0 r c) + m = m.
  Proof.
    apply @madd_0_l. intros; ring.
  Qed.
  
  Lemma madd_0_r : forall {r c} (m : M r c), m + (mat0 r c) = m.
  Proof.
    apply @madd_0_r; intros; ring.
  Qed.
  
  (* 矩阵减法 *)
  Definition mopp {r c} (m : M r c) : M r c :=
    @mopp X Xopp r c m.
  
  Global Notation "- m" := (mopp m) : mat_scope.
  
  Lemma mopp_opp : forall {r c} (m : M r c), - - m = m.
  Proof.
    apply @mopp_mopp. intros; ring.
  Qed.
  
  Definition msub {r c} (m1 m2 : M r c) : M r c :=
    @msub X Xopp Xadd r c m1 m2.
  
  Global Notation "m1 - m2" := (msub m1 m2) (at level 50, left associativity) 
    : mat_scope.
    
  Lemma msub_comm : forall {r c} (m1 m2 : M r c), m1 - m2 = - (m2 - m1).
  Proof.
    apply @msub_comm. all: intros; ring.
  Qed.
  
  Lemma msub_assoc : forall {r c} (m1 m2 m3 : M r c),
    (m1 - m2) - m3 = m1 - (m2 + m3).
  Proof.
    apply @msub_assoc. all: intros; ring.
  Qed.

  Lemma msub_0_l : forall {r c} (m : M r c), (mat0 r c) - m = - m.
  Proof.
    apply @msub_0_l. intros; ring.
  Qed.
  
  Lemma msub_0_r : forall {r c} (m : M r c), m - (mat0 r c) = m.
  Proof.
    apply (msub_0_r X0 Xopp); intros; ring.
  Qed.
  
  Lemma msub_self : forall {r c} (m : M r c), m - m = (mat0 r c).
  Proof.
    apply @msub_self. intros; ring.
  Qed.
  
  Lemma madd_opp : forall {r c} (m : M r c), m + (- m) = (mat0 r c).
  Proof. apply @msub_self. Qed.
  
  (* 矩阵数乘 *)
  Definition mcmul {r c} (a : X) (m : M r c) : M r c :=
    @mcmul X Xmul r c a m.
  
  Global Notation "a c* m" := (mcmul a m) : mat_scope.
  
  Definition mmulc {r c} (m : M r c) (a : X) : M r c :=
    @mmulc X Xmul r c m a.
  
  Global Notation "m *c a" := (mmulc m a) : mat_scope.
  
  Lemma mmulc_eq_mcmul : forall {r c} (a : X) (m : M r c), 
    m *c a = a c* m.
  Proof.
    apply mmulc_eq_mcmul; intros; ring.
  Qed.
  
  Lemma mcmul_assoc : forall {r c} (a b : X) (m : M r c), 
    a c* (b c* m) = (a * b) c* m.
  Proof.
    intros. apply mcmul_assoc1; intros; ring.
  Qed.
  
  Lemma mcmul_perm : forall {r c} (a b : X) (m : M r c), 
    a c* (b c* m) = b c* (a c* m).
  Proof.
    intros. apply mcmul_assoc2; intros; ring.
  Qed.
  
  Lemma mcmul_add_distr_l : forall {r c} (a : X) (m1 m2 : M r c), 
    a c* (m1 + m2) = a c* m1 + a c* m2.
  Proof.
    apply @mcmul_distr_l. intros; ring.
  Qed.
  
  Lemma mcmul_add_distr_r : forall {r c} (a b : X) (m : M r c), 
    (a + b)%X c* m = a c* m + b c* m.
  Proof.
    apply @mcmul_distr_r. intros; ring.
  Qed.
  
  Lemma mcmul_1_l : forall {r c} (m : M r c), 
    X1 c* m = m.
  Proof.
    apply mcmul_1_l. intros; ring.
  Qed.
  
  Lemma mcmul_0_l : forall {r c} (m : M r c), 
    mcmul X0 m = mat0 r c.
  Proof.
    apply mcmul_0_l. intros; ring.
  Qed.
  
  (* 矩阵转置 *)
  Definition mtrans {r c} (m : M r c): M c r :=
    @mtrans X r c m.
  
  Global Notation "m 'ᵀ'" := (mtrans m) : mat_scope.
  
  Lemma mtrans_trans : forall {r c} (m : M r c), mtrans (mtrans m) = m.
  Proof.
    apply @mtrans_trans.
  Qed.
  
  (* 矩阵乘法 *)
  Definition mmul {r c s} (m1 : M r c) (m2 : M c s) : M r s :=
    @mmul X X0 Xadd Xmul r c s m1 m2.
  
  Global Infix "*" := mmul : mat_scope.
  
  Lemma mmul_add_distr_l : forall {r c s} (m1 : M r c) (m2 m3 : M c s),
    m1 * (m2 + m3) = m1 * m2 + m1 * m3.
  Proof.
    apply @mmul_madd_distr_l; intros; cbv; ring.
  Qed.
  
  Lemma mmul_add_distr_r : forall {r c s} (m1 m2 : M r c) (m3 : M c s),
    (m1 + m2) * m3 = (m1 * m3) + (m2 * m3).
  Proof.
    apply @mmul_madd_distr_r; intros; cbv; ring.
  Qed.
  
  Lemma mmul_assoc : forall {r c s t} (m1 : M r c) (m2 : M c s) 
    (m3 : M s t),
    (m1 * m2) * m3 = m1 * (m2 * m3).
  Proof.
    apply @mmul_assoc; intros; cbv; ring.
  Qed.
  
  Lemma mmul_0_l : forall {r c s} (m : M c s), (mat0 r c) * m = mat0 r s.
  Proof.
    apply @mmul_0_l; intros; cbv; ring.
  Qed.
  
  Lemma mmul_0_r : forall {r c s} (m : M r c), m * (mat0 c s) = mat0 r s.
  Proof.
    apply @mmul_0_r; intros; cbv; ring.
  Qed.
  
  Lemma mmul_1_l : forall {r c} (m : M r c), (mat1 r) * m = m.
  Proof.
    apply @mmul_1_l; intros; ring.
  Qed.
  
  Lemma mmul_1_r : forall {r c} (m : M r c), m * (mat1 c) = m.
  Proof.
    apply @mmul_1_r; intros; ring.
  Qed.
  
  
  (** list list 与 矩阵 互转 *)
  
  (* 形式上简单，但内部结构复杂 *)
  Definition l2m_old {r c} (dl : list (list X)) : M r c :=
    mmake r c (fun x y => nth y (nth x dl []) X0).
  
  Definition l2m {r c} (dl : list (list X)) : M r c :=
    Matrix.l2m X0 dl r c.
  
  Definition m2l {r c} (m : M r c) : list (list X) :=
    Matrix.m2l m.
    
  Lemma m2l_length : forall {r c} (m : M r c), length (m2l m) = r.
  Proof.
    unfold m2l. induction r; intros; destruct m; simpl; auto.
  Qed.
  Global Hint Resolve m2l_length : mat.
  
  Lemma m2l_width : forall {r c} (m : M r c), width (m2l m) c.
  Proof.
    unfold m2l. induction r; intros; destruct m; simpl; auto. split; auto.
    apply v2l_length.
  Qed.
  Global Hint Resolve m2l_width : mat.
  
  Lemma m2l_l2m_id : forall {r c} (dl : list (list X)) (H1 : length dl = r)
    (H2 : width dl c), @m2l r c (l2m dl) = dl.
  Proof.
    intros. apply Matrix.m2l_l2m_id; auto.
  Qed.
  
  Lemma l2m_m2l_id : forall {r c} (m : M r c), l2m (m2l m) = m. 
  Proof.
    intros. apply Matrix.l2m_m2l_id; auto.
  Qed.
  
  Lemma l2m_inj : forall {r c} (d1 d2 : list (list X)),
    length d1 = r -> width d1 c -> 
    length d2 = r -> width d2 c -> 
    d1 <> d2 -> @l2m r c d1 <> l2m d2.
  Proof. Admitted.
  
  Lemma l2m_surj : forall {r c} (m : M r c), 
    (exists d, l2m d = m).
  Proof. Admitted.
    
  Lemma m2l_inj : forall {r c} (m1 m2 : M r c),
    m1 <> m2 -> m2l m1 <> m2l m2.
  Proof. Admitted.
  
  Lemma m2l_surj : forall {r c} (d : list (list X)), 
    length d = r -> width d c -> 
    (exists m, @m2l r c m = d).
  Proof. Admitted.
  
  (** l2v 关于 vadd 是同态映射 *)
  Lemma l2v_vadd_homo : forall (n : nat) (l1 l2 : list X)
    (H1 : length l1 = n) (H2 : length l2 = n),
    l2v X0 (map2 Xadd l1 l2) n = vadd Xadd (l2v X0 l1 n) (l2v X0 l2 n).
  Proof.
    induction n; intros.
    - rewrite length_zero_iff_nil in H1,H2; subst; auto.
    - destruct l1,l2; try easy.
      inversion H1. inversion H2. simpl. f_equal. subst.
      apply IHn; auto.
  Qed.
  
  (** v2l 关于 vadd 是同态映射 *)
  Lemma v2l_vadd_homo : forall (n : nat) (v1 v2 : vec n),
    v2l (vadd Xadd v1 v2) = map2 Xadd (v2l v1) (v2l v2).
  Proof.
    induction n; intros; destruct v1,v2; simpl; auto. f_equal; auto.
  Qed.

  (** l2m 关于 madd 是同态映射 *)
  Lemma l2m_madd_homo : forall (r c : nat) (dl1 dl2 : list (list X))
    (H1 : length dl1 = r) (W1 : width dl1 c) 
    (H2 : length dl2 = r) (W2 : width dl2 c),
    @l2m r c (dmap2 Xadd dl1 dl2) =
    madd (l2m dl1) (l2m dl2).
  Proof.
    induction r; intros.
    - rewrite length_zero_iff_nil in *. subst; auto.
    - destruct dl1,dl2; simpl in *; try easy.
      inversion H1. inversion H2. destruct W1,W2. f_equal.
      + apply l2v_vadd_homo; auto.
      + rewrite H0. apply IHr; auto.
  Qed.
  
  (** m2l 关于 madd 是同构映射 *)
  Lemma m2l_madd_homo : forall (r c : nat) (m1 m2 : M r c),
    m2l (madd m1 m2) = dmap2 Xadd (m2l m1) (m2l m2).
  Proof.
    induction r; intros; destruct m1,m2; simpl; auto. f_equal; auto.
    apply v2l_vadd_homo.
  Qed.
  
  
  (* ==================================== *)
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
  Definition m2t_3x3 (m : M 3 3) : @T_3x3 X.
    set (dl := m2l m).
    remember (hd [] dl) as l1.
    remember (hd [] (tl dl)) as l2.
    remember (hd [] (tl (tl dl))) as l3.
    remember (hd X0 l1, hd X0 (tl l1), hd X0 (tl (tl l1))) as t1.
    remember (hd X0 l2, hd X0 (tl l2), hd X0 (tl (tl l2))) as t2.
    remember (hd X0 l3, hd X0 (tl l3), hd X0 (tl (tl l3))) as t3.
    exact (t1, t2, t3).
  Defined.
  
  
  (** 取出1x1矩阵的第 0,0 个元素 *)
  Definition scalar_of_mat (m : M 1 1) := mnth m 0 0.
  
End MatrixThy.
