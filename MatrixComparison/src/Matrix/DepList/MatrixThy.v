(*
  purpose:    Matrix implemented with Inductive List
  author:     Zhengpu Shi
  date:       2021.12
  
  remark:
  1. use Coq.Vectors.Vector 
*)


Require Export MatrixThySig.

Require Export DepList.Matrix.


(* ######################################################################### *)
(** * Matrix theory *)
Module MatrixThy (F : FieldSig) <: MatrixThySig F.
  Export F.
  
  Open Scope X_scope.
  Open Scope mat_scope.
  
  (** 矩阵类型 *)
  Definition mat X r c := @mat X r c.
  Notation M r c := (mat X r c).
  
  (* 矩阵相等的可判定性 *)
  Lemma meq_dec : forall {r c} (m1 m2 : M r c), {m1 = m2} + {m1 <> m2}.
  Proof.
    apply meq_dec. apply Xeqdec.
  Qed.
  
  Definition mnth {r c} (m : M r c) (ri ci : nat) :=
    let fri := fin_gen r ri in
    let fci := fin_gen c ci in
      match fri, fci with
      | Some fri', Some fci' => mnth m fri' fci'
      | _, _ => X0
      end.
  
  Lemma meq_iff_mnth : forall {r c : nat} (m1 m2 : M r c),
    m1 = m2 <-> 
    (forall ri ci, ri < r -> ci < c -> mnth m1 ri ci = mnth m2 ri ci).
  Proof.
    intros. split; intros. subst; auto.
    apply meq_iff_nth. Admitted.

  (** 构造具体的矩阵 *)

  Definition mk_mat_1_1 (a11 : X) : @M 1 1 := [[a11]].
  Definition mk_mat_3_1 (a1 a2 a3 : X) : @M 3 1 
    := [[a1];[a2];[a3]].
  
  Definition mk_mat_3_3 (a11 a12 a13 a21 a22 a23 a31 a32 a33 : X) : @M 3 3 
    := [[a11;a12;a13];[a21;a22;a23];[a31;a32;a33]].
  
  (** 零矩阵和单位矩阵 *)
  Definition mat0 r c : M r c := @mat0 X X0 r c.
  Definition mat1 n : M n n := @mat1 X X0 X1 n.
  
  (** 矩阵映射 *)
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
    
  (** 矩阵加法 *)
  Definition madd {r c} := @madd X Xadd r c.
  Global Infix "+" := madd : mat_scope.
  
  Lemma madd_comm : forall {r c} (m1 m2 : M r c), m1 + m2 = m2 + m1.
  Proof.
    apply @madd_comm. intros. ring.
  Qed.
  
  Lemma madd_assoc : forall {r c} (m1 m2 m3 : M r c), 
    madd (madd m1 m2) m3 = madd m1 (madd m2 m3).
  Proof.
    apply @madd_assoc. intros; ring.
  Qed.
  
  Lemma madd_0_l : forall {r c} (m : M r c), madd (mat0 r c) m = m.
  Proof.
    apply @madd_0_l. intros; ring.
  Qed.
  
  Lemma madd_0_r : forall {r c} (m : M r c), madd m (mat0 r c) = m.
  Proof.
    apply @madd_0_r; intros; ring.
  Qed.
  
  (** 矩阵减法 *)
  Definition mopp {r c} (m : M r c) : M r c :=
    @mopp X Xopp r c m.
  Global Notation "- m" := (mopp m) : mat_scope.
  
  Lemma mopp_opp : forall {r c} (m : M r c), - - m = m.
  Proof.
    apply @mopp_mopp. intros; ring.
  Qed.
  
  Definition msub {r c} (m1 m2 : M r c) : M r c :=
    @msub X Xsub r c m1 m2.
  Global Infix "-" := msub : mat_scope.
  
  Lemma msub_comm : forall {r c} (m1 m2 : M r c), m1 - m2 = - (m2 - m1).
  Proof.
    apply @msub_comm. intros; ring.
  Qed.
  
  Lemma msub_assoc : forall {r c} (m1 m2 m3 : M r c), 
    (m1 - m2) - m3 = m1 - (m2 + m3).
  Proof.
    apply @msub_assoc. intros; ring.
  Qed.

  Lemma msub_0_l : forall {r c} (m : M r c), (mat0 r c) - m = - m.
  Proof.
    apply @msub_0_l. intros; ring.
  Qed.
  
  Lemma msub_0_r : forall {r c} (m : M r c), m - (mat0 r c) = m.
  Proof.
    apply @msub_0_r. intros; ring.
  Qed.
  
  Lemma msub_self : forall {r c} (m : M r c), m - m = (mat0 r c).
  Proof.
    apply @msub_self. intros; ring.
  Qed.
  
  Lemma madd_opp : forall {r c} (m : M r c), m + (- m) = (mat0 r c).
  Proof.
    apply @madd_mopp. intros; ring.
  Qed.
 
  (** 矩阵数乘 *)
  Definition mcmul {r c} (a : X) (m : M r c) : M r c :=
    @mcmul X Xmul r c a m.
  
  Definition mmulc {r c} (m : M r c) (a : X) : M r c :=
    @mmulc X Xmul r c m a.
  
  Global Notation "a c* m" := (mcmul a m) : mat_scope.
  Global Notation "m *c a" := (mmulc m a) : mat_scope.
    
  Lemma mmulc_eq_mcmul : forall {r c} (a : X) (m : M r c), 
    m *c a = a c* m.
  Proof.
    apply mmulc_eq_mcmul. intros; ring.
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
    mcmul (Xadd a b) m = madd (mcmul a m) (mcmul b m).
  Proof.
    apply @mcmul_distr_r. intros; ring.
  Qed.
  
  Lemma mcmul_1_l : forall {r c} (m : M r c), 
    mcmul X1 m = m.
  Proof.
    apply @mcmul_1_l. intros; ring.
  Qed.
  
  Lemma mcmul_0_l : forall {r c} (m : M r c), mcmul X0 m = mat0 r c.
  Proof.
    apply @mcmul_0_l; intros; cbv; ring.
  Qed.
    
  (** 矩阵转置 *)
  Definition mtrans {r c} (m : M r c): M c r :=
    @mtrans X r c m.
  
  Notation "m 'ᵀ'" := (mtrans m) : mat_scope.
  
  Lemma mtrans_trans : forall {r c} (m : M r c), mtrans (mtrans m) = m.
  Proof.
    apply @mtrans_trans.
  Qed.
  
  (** 矩阵乘法 *)
  Definition mmul {r c s} (m1 : M r c) (m2 : M c s) : M r s :=
    @mmul X X0 Xadd Xmul r c s m1 m2.
  
  Global Infix "*" := mmul : mat_scope.
  
  Lemma mmul_add_distr_l : forall {r c t} (m1 : M r c) (m2 m3 : M c t), 
    mmul m1 (madd m2 m3) = madd (mmul m1 m2) (mmul m1 m3).
  Proof.
    apply @mmul_madd_distr_l; intros; cbv; ring.
  Qed.
  
  Lemma mmul_add_distr_r : forall {r c s} (m1 m2 : M r c) (m3 : M c s), 
    mmul (madd m1 m2) m3 = madd (mmul m1 m3) (mmul m2 m3).
  Proof.
    apply @mmul_madd_distr_r; intros; cbv; ring.
  Qed.
  
  Lemma mmul_assoc : forall {r c s t} (m1 : M r c) (m2 : M c s) 
    (m3 : M s t), 
    mmul (mmul m1 m2) m3 = mmul m1 (mmul m2 m3).
  Proof.
    apply @mmul_assoc; intros; cbv; ring.
  Qed.
  
  Lemma mmul_0_l : forall {r c t} (m : M c t), mmul (mat0 r c) m = mat0 r t.
  Proof.
    apply @mmul_0_l; intros; cbv; ring.
  Qed.
  
  Lemma mmul_0_r : forall {r c t} (m : M r c), mmul m (mat0 c t) = mat0 r t.
  Proof.
    apply @mmul_0_r; intros; cbv; ring.
  Qed.
  
  Lemma mmul_1_l : forall {r c} (m : M r c), mmul (mat1 r) m = m.
  Proof.
    apply @mmul_1_l; intros; try ring. exact X0.
  Qed.
  
  Lemma mmul_1_r : forall {r c} (m : M r c), mmul m (mat1 c) = m.
  Proof.
    apply @mmul_1_r; intros; try ring. exact X0.
  Qed.
  
  
  (** list list 与 矩阵 互转 *)
  
  Definition l2m {r c} (dl : list (list X)) : M r c :=
    Matrix.l2m X0 dl r c.
  
  Definition m2l {r c} (m : M r c) : list (list X) :=
    Matrix.m2l m.
    
  Lemma m2l_length : forall {r c} (m : M r c), length (m2l m) = r.
  Proof.
    intros. induction m; simpl in *; auto.
  Qed.
  Global Hint Resolve m2l_length : mat.
  
  Lemma m2l_width : forall {r c} (m : M r c), width (m2l m) c.
  Proof.
    intros. unfold m2l. induction m; simpl; auto. split; auto.
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
    set (l1 := hd m).
    set (l2 := hd (tl m)).
    set (l3 := hd (tl (tl m))).
    set (t1 := (hd l1, hd (tl l1), hd (tl (tl l1)))).
    set (t2 := (hd l2, hd (tl l2), hd (tl (tl l2)))).
    set (t3 := (hd l3, hd (tl l3), hd (tl (tl l3)))).
    exact (t1, t2, t3).
  Defined.
  
  
  (** 取出1x1矩阵的第 0,0 个元素 *)
  Definition scalar_of_mat (m : M 1 1) := mnth m 0 0.
  
  (** get / set an element of a matrix *)
  Definition mget := @mget X.
  Definition mset := @mset X.

End MatrixThy.
