(*
  purpose   : Matrix implemented with Fin Function
  author    : ZhengPu Shi
  date      : 2021.12
  
  remark    :
  1. reference:  
  https://math-comp.github.io/htmldoc_1_14_0/mathcomp.algebra.matrix.html#matrix
  2. change it to Functor version, which can support multiple Base Type.
  3. especially we want to use RingType as Base Type, because lots of operations 
    related to Base Type could be omitted. 
*)



Require Export ListListExt.
Require Export FieldTypeR.
Require Import MatrixSig.

Require Export Fin.
Require Export Arith.
Require Export Lia.
Require Export List.
Export ListNotations.


Module MatrixImpl (E : RingType) <: MatrixSig.
  Export E.
  
  (* 作用域 *)
  Open Scope nat_scope.
  Open Scope A_scope.
  
  Declare Scope mat_scope.
  Delimit Scope mat_scope with M.
  Open Scope mat_scope.

  (** 基础类型 *)
  Definition A := E.A.
  Definition A1 := E.A1.
  Definition Aadd := E.Aadd.
  Definition Amul := E.Amul.


  (** 矩阵类型 *)
  
  (** We define a _matrix_ as a simple function from two fin
      (corresponding to a row and a column index) to a value. *)
  Definition mat (r c : nat) := Fin.t r -> Fin.t c -> E.A.
  
  Bind Scope mat_scope with mat.

  Notation Vector n := (mat n 1).
  Notation Square n := (mat n n).
  
  Module test_cvt_nat_fin.
(*     (* nat + Prop 转换为 Fin.t *)
    Print Fin.t.
    Search Fin.t.
    Check of_nat_lt.
    Example ex1 : 2 < 3.
    unfold lt. constructor. Defined. Print ex1.
    (* 生成一个 Fin.t 3 的元素。总共有 0,1,2 这三个序号的元素，这里指定的序号是 2 *)
    Compute @of_nat_lt 2 3 (le_n 3).
    
    (* Fin.t 转换为 nat + Prop *)
    Check @F1 3.
    Compute to_nat (@F1 3).
    Compute proj1_sig (to_nat (@F1 3)). *)
  End test_cvt_nat_fin.
  
  Check of_nat 3 2.
  
  Definition mnth {r c} (m : mat r c) (ri ci : nat) : E.A.
  Proof.
    destruct (lt_dec ri r), (lt_dec ci c).
    - exact (m (of_nat_lt l) (of_nat_lt l0)).
    - exact A0.
    - exact A0.
    - exact A0.
  Defined.
  
  (** 矩阵相等 *)
  Definition meq {r c} (m1 m2 : mat r c) : Prop := 
    forall ri ci, ri < r -> ci < c -> mnth m1 ri ci = mnth m2 ri ci.

  (* 矩阵相等 *)
  
  (** Note that the dimensions of the matrix aren'A being used here. In
      practice, a matrix is simply a function on any two nats. However,
      we will used these dimensions to define equality, as well as the
      multiplication and kronecker product operations to follow. *)

  (* If every element of corresponding elements of two matrices, then we called 
   they are mat_equiv. *)
  Definition meq {m n : nat} (A B : mat m n) : Prop := 
    forall i j, A i j = B i j.
  
  Declare Scope mat_scope.
  Delimit Scope mat_scope with M.
  Open Scope M.
  Global Notation "m1 == m2" := (meq m1 m2) (at level 70) : mat_scope.
  
  Lemma meq_equiv : forall {r c}, equivalence (mat r c) meq.
  Proof.
    intros. refine (Build_equivalence _ _ _ _ _); unfold meq.
    - intros m. intros. auto.
    - intros m1 m2 m3. intros. rewrite H; auto.
    - intros m1 m2. intros. rewrite H; auto.
  Qed.

  (* 需要手动注册给 Coq *)
  Add Parametric Relation (r c : nat) : (mat r c) meq
    reflexivity proved by (equiv_refl (mat r c) meq meq_equiv)
    symmetry proved by (equiv_sym (mat r c) meq meq_equiv)
    transitivity proved by (equiv_trans (mat r c) meq meq_equiv)
    as meq_rel.
    
  (** Convert between Lists and Vectors / Matrices *)
  
  (* 一些辅助定义和引理 *)
  Section aux.
    
    (* Fetch a row *)

    (* Aux function, cnt initial is 0 *)
    (* 取出第 ri 行的数据。
      1. 列元素个数为 c 个
      2. 列偏移量为 c_init，如果为0则正好，不为0，则超出部分的数据不保证正确
    *)
    ?
    Fixpoint mrow_aux {r c : nat} (ri : Fin.A r) (c_init : Fin.A c) (m : mat r c) 
      : list A := match c with
      | O => nil
      | S c' => m ri c_init :: (@mrow_aux r c' ri (FS c_init) m)
      end.
    
    Lemma eq4 : forall r c (m : mat r c) ri c_init,
      ri < r -> S c_init < c ->
      m ri c_init :: mrow_aux ri (S c_init) m = mrow_aux ri c_init m.
    Proof.
      intros r c. gd r. induction c; intros. lia.
      simpl. rewrite IHc; auto. auto.
      (* 同样的问题 *)
    Admitted.
    
    (* 列表多取出一个元素，不影响有效数据 *)
    Lemma eq1 : forall r c (m : mat r (S c)) ri ci c_init,
      ci + c_init < S c ->
      @nth A ci (@mrow_aux r (S c) ri c_init m) A0 =
      @nth A ci (@mrow_aux r c ri c_init m) A0.
    Proof.
      intros. simpl. unfold mrow_aux. destruct ci.
    Admitted.
    
    Lemma eq2 : forall r c (m : mat r c) ri ci c_init,
      ri < r -> ci + (S c_init) < c ->
      nth (S ci) (@mrow_aux r c ri c_init m) A0 = 
      nth ci (@mrow_aux r c ri (S c_init) m) A0.
    Proof.
      intros r c. gd r. induction c; intros. lia.
      rewrite eq1; try lia. rewrite eq1; auto. rewrite IHc; auto.
      (* 仍然无法证明 *)
    Admitted.

    (* 不越界时取出有效的数据 *)
    Lemma nth_mrow_aux : forall {r c} (m : mat r c) ri ci c_init,
      (ri < r) -> (ci + c_init < c) ->
      nth ci (mrow_aux ri c_init m) A0 = m ri (Nat.add ci c_init).
    Proof.
      (* 第一次证明，最后的不等式无法证明 *)
      intros r c. gd r. induction c; intros. lia. simpl.
      destruct ci; auto. simpl. rewrite IHc; auto. Restart.
      (* 第二次证明，先归纳 ci *)
      intros r c m ri ci. gd ri. gd m. gd c. gd r. induction ci; intros.
      - induction c. lia. auto.
      - replace (S ci + c_init)%nat with (ci + (S c_init))%nat; try lia.
        rewrite <- IHci with (r:=r) (c:=c); try lia.
        (* 转换到另一个问题，但也不能证明 *)
        apply eq2; auto. lia.
        Back 2.
        (* 尝试变换形式 *)
        replace (mrow_aux ri c_init m)
        with (m ri c_init :: mrow_aux ri (S c_init) m). simpl. ; auto.
        (* 转换到新问题 *)
        apply eq4; auto. lia.
    Qed.
    
      
    Definition mrow {r c : nat} (ri : nat) (m : mat r c) := 
      @mrow_aux r c ri 0 m.
    
    Lemma mrow_aux_length : forall {r c} ri c_init (m : mat r c), 
      length (mrow_aux ri c_init m) = c.
    Proof.
      intros r c. induction c; intros; simpl; auto.
    Qed.
      
    Lemma mrow_length : forall {r c} ri (m : mat r c), length (mrow ri m) = c.
    Proof.
      intros. apply mrow_aux_length.
    Qed.
    
    (* mat to list list *)
    Fixpoint m2l_aux {r c : nat} (cnt : nat) (m : mat r c) : list (list A) := 
      match r with
      | O => nil
      | S r' => mrow cnt m :: (@m2l_aux r' c (S cnt) m)
      end.
    
    Lemma m2l_aux_length : forall {r c} cnt (m : mat r c), 
      length (m2l_aux cnt m) = r.
    Proof.
      induction r; intros; simpl; auto.
    Qed.
    
    Lemma m2l_aux_width : forall {r c} cnt {m : mat r c}, 
      width (m2l_aux cnt m) c.
    Proof.
      induction r; intros; simpl; auto. split.
      - apply mrow_length.
      - (* a bit tricky. although it seems too hard, but notice that
        "mat r c" and "mat (S r) c" and "mat 4 3" are same type. *)
        destruct r; auto.
    Qed.
    
    (* m2l_aux and nth *)
    Lemma m2l_aux_nth_nth : forall {r c} (dl : list (list E.A))
      (H1 : length dl = r) (H2 : width dl c),
      @m2l_aux r c 0 (fun x y : nat => nth y (nth x dl []) 0) = dl.
    Proof.
      intros. gd dl. gd c.
      induction r; intros.
      - apply length_zero_iff_nil in H1. subst. simpl. auto.
      - simpl. destruct dl.
        + simpl in H1. lia.
        + f_equal.
          {  
      
    Admitted.
      
    
    Lemma nth_mrow : forall {r c} (m : mat r c) ri ci,
      (ri < r) -> (ci < c) ->
      nth ci (mrow ri m) A0 = m ri ci.
    Proof.
      intros. unfold mrow.
      induction r; intros; simpl. lia.
      destruct ri; simpl.
      2:{ 
(*        rewrite IHr.
      intros r c. gd r. induction c; intros. lia.
      destruct ci; simpl; auto.
 *)       
      Admitted.
    
    Lemma nth_nth_m2l_aux : forall {r c} (m : mat r c) (ri ci r_init : nat),
      (ri < r) -> (ci < c) -> (ri + r_init < r) ->
      nth ci (nth ri (m2l_aux r_init m) []) A0 = m (Nat.add ri r_init) ci.
    Proof.
      induction r; intros. lia.
      destruct ri; simpl. apply nth_mrow; auto.
      rewrite IHr; auto. lia.
      
(*        ?
      induction ri; simpl. apply nth_mrow; auto.
      rewrite IHr; auto. lia.
      
       IHri.
      simpl.
      intros. unfold m2l_aux.
      induction r; intros. lia. simpl.
      destruct ri; simpl.
      2:{ unfold m2l_aux.
      - (* apply nth_mrow; auto. *)
 *)      Admitted.
      
  End aux.
  
  (** MatrixSig 中关于“list list和Matrix互转” 的要求 *)
  
  (* 这个定义也有额外的好处，但签名有点奇怪，是否能够通用？先保留 *)
  Definition l2M (l : @list (list A)) : mat (length l) (length (hd [] l)) :=
    (fun x y => nth y (nth x l []) A0).
  
  Definition mlength {r c} (m : mat r c) := r.
  Definition mwidth {r c} (m : mat r c) := c.
  
  Definition l2m {r c} (dl : list (list E.A)) : mat r c := 
    fun x y => nth y (nth x dl []) A0.
  
  Lemma l2m_length : forall {r c} (dl : list (list A)),
    mlength (@l2m r c dl) = r.
  Proof.
    intros. unfold mlength. auto.
  Qed.
  
  Lemma l2m_width : forall {r c} (dl : list (list A)),
    mwidth (@l2m r c dl) = c.
  Proof.
    intros. unfold mwidth. auto.
  Qed.
  
  Definition m2l {r c} (m : mat r c) := m2l_aux 0 m.

  Lemma m2l_length : forall {r c} (m : mat r c), length (m2l m) = r.
  Proof.
    unfold m2l. intros; apply m2l_aux_length.
  Qed.
  
  Lemma m2l_width : forall {r c} (m : mat r c), width (m2l m) c.
  Proof.
    intros. apply m2l_aux_width.
  Qed.
  
  Lemma m2l_l2m_id : forall {r c} (dl : list (list E.A)),
    (length dl = r) -> (width dl c) -> m2l (@l2m r c dl) = dl.
  Proof.
    unfold m2l,l2m.
    destruct r.
    - intros. apply length_zero_iff_nil in H. subst. simpl. auto.
    - intros. rewrite m2l_aux_nth_nth; auto.
  Qed.
  
  Lemma l2m_m2l_id : forall {r c} (m : mat r c), 
    (mlength m = r) -> (mwidth m = c) -> meq (l2m (m2l m)) m. 
  Proof.
    intros. unfold m2l,l2m. unfold meq; intros.
    rewrite nth_nth_m2l_aux; auto. lia.
  Qed.
  
  (* Lists to Vectors *)
  
  Definition l2V (l : list A) : Vector (length l) :=
    (fun x y => nth x l A0).

  (** (mrow_aux m i c_init)[j] = m[i][j + c_init] *)
  Lemma mrow_aux_nth : forall {r c} ri ci c_init (m : mat r c) a,
    ri < r -> ci < c ->
    nth ci (mrow_aux ri c_init m) a = m ri (ci + c_init)%nat.
  Proof.
    intros r c. gd r.
    induction c.
    - intros. lia.
    - intros r ri ci. induction ci.
      + intros. simpl. auto.
      + intros. simpl. replace (S (ci + c_init)) with (ci + (S c_init))%nat.
        apply IHc; auto. lia. lia.
  Qed.
  
  (** (mrow m i)[j] = m[i][j] *)
  Lemma mrow_nth : forall {r c} ri ci (m : mat r c) a,
    ri < r -> ci < c ->
    nth ci (mrow ri m) a = m ri ci.
  Proof.
    intros. unfold mrow. rewrite mrow_aux_nth; auto.
  Qed.
  
  (* Fetch a column *)

  (* Aux function, cnt initial is 0 *)
  Fixpoint MCol_aux (r c : nat) (ci : nat) (cnt : nat) (m : mat r c) 
    : list A := match r with
    | O => nil
    | S r' => m cnt ci :: (MCol_aux r' c ci (S cnt) m)
    end.
  Definition MCol {r c : nat} (ci : nat) (m : mat r c) := MCol_aux r c ci 0 m.

  (** Vectors / Matrices to Lists *)
  
  (* Vector to List *)
  Definition V2l {n} (v : Vector n):= MCol 0 v.
  
  (* 构造具体的矩阵 *)
  Definition mat_1_1 (a11 : E.A) : mat 1 1.
  Proof.
    refine (l2m [[a11]]); auto.
  Defined.
  
  Definition mat_3_3 (a11 a12 a13 a21 a22 a23 a31 a32 a33 : A) : mat 3 3.
  Proof.
    refine (l2m [[a11;a12;a13]; [a21;a22;a23]; [a31;a32;a33]]); auto.
  Defined.
  
  (* 零矩阵和单位矩阵 *)
  
  (* Identity mat *)
  Definition mat1 (n : nat) : mat n n := 
    fun i j => if (i =? j)%nat then E.A1 else A0.

  (* Zero mat *)
  Definition mat0 (m n : nat) : mat m n := fun _ _ => A0. 
  
  
  (* 矩阵映射 *)
  Definition mmap {r c} (f : A -> A) (m : mat r c) : mat r c :=
    fun i j => f (m i j).
  
  Definition mmap2 {r c} (f : A -> A -> A) (m1 m2 : mat r c) : mat r c :=
    fun i j => f (m1 i j) (m2 i j).
  
  Lemma mmap2_comm : forall {r c} (f : A -> A -> A)
    (f_comm : forall a b : A, f a b = f b a) (m1 m2 : mat r c), 
    mmap2 f m1 m2 == mmap2 f m2 m1.
  Proof.
    intros r c f H1. intros m1 m2. intros i j Hi Hj.
    unfold mmap2. auto.
  Qed.
  
  Lemma mmap2_assoc : forall {r c} (f : A -> A -> A)
    (f_assoc : forall a b c, f a (f b c) = f (f a b) c) (m1 m2 m3 : mat r c), 
    mmap2 f (mmap2 f m1 m2) m3 == mmap2 f m1 (mmap2 f m2 m3).
  Proof.
    intros r c f H1. intros m1 m2 m3. intros i j Hi Hj.
    unfold mmap2. auto.
  Qed.
  
  
  (* 矩阵加法 *)
  Definition madd {m n : nat} (A B : mat m n) : mat m n 
    := fun i j => A i j + B i j.

  Infix "+" := madd (at level 50, left associativity) : matrix_scope.
  
  Lemma madd_comm : forall {m n} (A B : mat m n), A + B == (B + A)%M.
  Proof.
    intros m n A B i j Hi Hj.
    unfold madd. ring.
  Qed.
  
  Lemma madd_assoc : forall {m n} (A B C : mat m n), 
    (A + B) + C == (A + (B + C))%M.
  Proof.
    intros m n A B C i j Hi Hj. 
    unfold madd. ring.
  Qed.
  
  Lemma madd_0_l : forall {m n} (A : mat m n), mat0 m n + A == A. 
  Proof.
    intros m n A i j Hi Hj.
    unfold mat0, madd. ring.
  Qed.
  
  (* 加法与 meq 相容 *)
  Add Parametric Morphism (r c : nat) : madd
    with signature (@meq r c) ==> meq ==> meq as madd_mor.
  Proof.
    intros. unfold meq in *. intros. unfold madd. rewrite H,H0; auto.
  Qed.
  
  (* 加法与取出具体元素的关系 *)
  Lemma madd_ij : forall {r c} (m1 m2 : mat r c) ri ci,
    (m1 + m2) ri ci = ((m1 ri ci) + (m2 ri ci))%A.
  Proof.
    intros. auto.
  Qed.
  
  (* 加法与 mrow 的关系 *)
  
(*   Lemma mrow_aux_cntS : forall {r c} (m : mat r c) ri cnt,
    mrow_aux ri cnt m = (m ri cnt) :: mrow_aux ri (S cnt) m.
  Proof.
    intros. unfold mrow_aux. simpl.
    intros r c. gd r. induction c; intros; simpl; auto.
 *)  
  (* (m1 + m2)[0] = m1[0] + m2[0] *)
  Lemma mrow_aux_prop1 : forall {r c} (m1 m2 : mat r c),
    (0 < r) ->
    mrow_aux 0 0 (m1 + m2) = 
    ListAux.lmap2 E.Aadd (mrow_aux 0 0 m1) (mrow_aux 0 0 m2).
  Proof.
    intros r c. gd r. induction c.
    - intros. simpl. auto.
    - intros. simpl. f_equal.
      eapply nth_ext.
      + rewrite mrow_aux_length. 
        rewrite lmap2_length with (n := c); auto.
        apply mrow_aux_length.
        apply mrow_aux_length.
      + intros. 
        rewrite mrow_aux_length in H0.
        rewrite mrow_aux_nth; auto.
        rewrite lmap2_nth.
        repeat rewrite mrow_aux_nth; auto.
        rewrite mrow_aux_length; auto.
        rewrite mrow_aux_length; auto.
        Unshelve. exact A0. exact A0.
  Qed.
  
  (* 矩阵减法 *)
  Definition mopp {r c} (m : mat r c) : mat r c := fun i j => -m i j.
  
  Lemma mopp_mopp : forall {r c} (m : mat r c), mopp (mopp m) == m.
  Proof.
    intros r c A i j Hi Hj.
    unfold mopp. ring.
  Qed.
    
  Definition msub {r c} (m1 m2 : mat r c) : mat r c 
    := fun i j => m1 i j - m2 i j.
  
  Lemma msub_comm : forall {r c} (m1 m2 : mat r c), 
    msub m1 m2 == mopp (msub m2 m1).
  Proof.
    intros m n A B i j Hi Hj.
    unfold msub,mopp. ring.
  Qed.
  
  Lemma msub_assoc : forall {r c} (m1 m2 m3 : mat r c), 
    msub (msub m1 m2) m3 == msub m1 (madd m2 m3).
  Proof.
    intros m n A B C i j Hi Hj. 
    unfold msub,madd. ring.
  Qed.
    
  Lemma msub_0_l : forall {r c} (m : mat r c), msub (mat0 r c) m == mopp m.
  Proof.
    intros r c A i j Hi Hj.
    unfold msub,mopp,mat0. ring.
  Qed.
  
  Lemma msub_0_r : forall {r c} (m : mat r c), msub m (mat0 r c) == m.
  Proof.
    intros r c A i j Hi Hj.
    unfold msub,mopp,mat0. ring.
  Qed.
  
  Lemma msub_self : forall {r c} (m : mat r c), msub m m == (mat0 r c).
  Proof.
    intros r c A i j Hi Hj.
    unfold msub,mat0. ring.
  Qed.
  
  (* 矩阵数乘 *)
  Definition mcmul {r c} (a : A) (m : mat r c) : mat r c :=
    fun i j => (a * m i j)%A.
    
  Definition mmulc {r c} (m : mat r c) (a : A) : mat r c :=
    fun i j => (m i j * a)%A.

  Infix "c*" := mcmul (at level 40, left associativity) : matrix_scope.
  Infix "*c" := mmulc (at level 40, left associativity) : matrix_scope.
  
  Lemma mmulc_eq_mcmul : forall {r c} (a : A) (m : mat r c), 
    m *c a == a c* m.
  Proof.
    intros r c a A i j Hi Hj.
    unfold mcmul,mmulc. ring.
  Qed.
  
  Lemma mcmul_assoc1 : forall {r c} (a b : A) (m : mat r c), 
    a c* (b c* m) == (a * b) c* m.
  Proof.
    intros r c a b A i j Hi Hj.
    unfold mcmul,mmulc. ring.
  Qed.
  
  Lemma mcmul_assoc2 : forall {r c} (a b : A) (m : mat r c), 
    a c* (b c* m) == b c* (a c* m).
  Proof.
    intros r c a b A i j Hi Hj.
    unfold mcmul,mmulc. ring.
  Qed.
  
  Lemma mcmul_distr_l : forall {r c} (a : A) (m1 m2 : mat r c), 
    a c* (m1 + m2) == ((a c* m1) + (a c* m2))%M.
  Proof.
    intros r c a A B i j Hi Hj.
    unfold mcmul,mmulc,madd. ring.
  Qed.
  
  Lemma mcmul_distr_r : forall {r c} (a b : A) (m : mat r c), 
    (a + b)%A c* m == ((a c* m) + (b c* m))%M.
  Proof.
    intros r c a A B i j Hi Hj.
    unfold mcmul,mmulc,madd. ring.
  Qed.
  
  Lemma mcmul_1 : forall {r c} (m : mat r c), 
    mcmul E.A1 m == m.
  Proof.
    intros r c A i j Hi Hj.
    unfold mcmul,mmulc,madd. ring.
  Qed.
  
  (* 矩阵转置 *)
  Definition mtrans {r c} (m : mat r c): mat c r :=
    fun x y => m y x.
  
  Notation "A ⊤" := (mtrans A) (at level 0) : matrix_scope. 
  
  Lemma mtrans_trans : forall {r c} (m : mat r c), mtrans (mtrans m) == m.
  Proof.
    intros. unfold mtrans. intros i j Hi Hj. auto.
  Qed.
  
  (* 矩阵乘法 *)
  Definition mmul {r c A : nat} (A : mat r c) (B : mat c A) : mat r A := 
    fun x z => Tsum (fun y => A x y * B y z) c.
  
  Infix "×" := mmul (at level 40, left associativity) : matrix_scope.
  
  
  (** A useful tactic for solving A == B for concrete A, B *)

  Ltac solve_end :=
    match goal with
    | H : lt _ O |- _ => apply Nat.nlt_0_r in H; contradict H
    end.
                  
  Ltac by_cell := 
    intros;
    let i := fresh "i" in 
    let j := fresh "j" in 
    let Hi := fresh "Hi" in 
    let Hj := fresh "Hj" in 
    intros i j Hi Hj; try solve_end;
    repeat (destruct i as [|i]; simpl; [|apply lt_S_n in Hi]; try solve_end); clear Hi;
    repeat (destruct j as [|j]; simpl; [|apply lt_S_n in Hj]; try solve_end); clear Hj.

  Ltac lma := by_cell; compute; ring.
  
  Lemma mmul_madd_distr_l : forall {m n o : nat} (A : mat m n) (B C : mat n o), 
                             A × (B + C) == (A × B + A × C)%M.
  Proof.
    intros. intros i j _ _.
    unfold madd, mmul.
    rewrite <- Tsum_plus.
    apply Tsum_eq; intros. ring.
  Qed.
  
  Lemma mmul_madd_distr_r : forall {m n o : nat} (A B : mat m n) (C : mat n o), 
                           (A + B) × C == (A × C + B × C)%M.
  Proof. 
    intros. intros i j _ _.
    unfold madd, mmul.
    rewrite <- Tsum_plus.
    apply Tsum_eq; intros. ring.
  Qed.

  Lemma mmul_assoc : forall {m n o p : nat} (A : mat m n) (B : mat n o) 
    (C: mat o p), (A × B) × C == A × (B × C).
  Proof.
    intros m n o p A B C i j Hi Hj.
    unfold mmul.
    induction n.
    + simpl.
      clear B.  (* 丢掉一个前提。*)
      induction o. reflexivity.
      simpl. rewrite IHo. ring.
    + simpl. 
      rewrite <- IHn.
      rewrite Tsum_mult_l.
      rewrite <- Tsum_plus.
      apply Tsum_eq; intros. ring.
  Qed.

  Lemma mmul_0_l : forall {r c A} (m : mat c A), mmul (mat0 r c) m == mat0 r A.
  Proof.
    intros r c A m i j Hi Hj.
    unfold mmul,mat0. rewrite Tsum_0. ring. intros. ring.
  Qed.
  
  Lemma mmul_0_r : forall {r c A} (m : mat r c), mmul m (mat0 c A) == mat0 r A.
  Proof.
    intros r c A m i j Hi Hj.
    unfold mmul,mat0. rewrite Tsum_0. ring. intros. ring.
  Qed.
  
  Lemma mmul_1_l : forall {m n : nat} (A : mat m n), 
    mat1 m × A == A.
  Proof.
    intros m n A i j Hi Hj.
    unfold mmul.
    eapply Tsum_unique. apply Hi.
    unfold mat1. rewrite Nat.eqb_refl. ring.
    intros x Hx. unfold mat1.
    apply Nat.eqb_neq in Hx. rewrite Hx. ring.
  Qed.
  
  Lemma mmul_1_r : forall {m n : nat} (A : mat m n), 
    A × mat1 n == A.
  Proof.
    intros m n A i j Hi Hj.
    unfold mmul.
    eapply Tsum_unique. apply Hj.
    unfold mat1. rewrite Nat.eqb_refl. ring.
    intros x Hx. unfold mat1.
    apply Nat.eqb_neq in Hx. rewrite Nat.eqb_sym. rewrite Hx. ring.
  Qed.

End MatrixImpl.


(** Function版本的Matrix起始两个参数没有约束作用 *)

(* From FCS Require Import RingTypeZ.

Module FunctionMatrix_Dim_NoEffect.

  Module MZ := MatrixImpl RingTypeZ.
  Import MZ.

  Open Scope Z.
  
  Definition m1 : mat 3 3 := mat_3_3 1 2 3 4 5 6 7 8 9.

  (* 这里输入任何下标都可以 *)
  Check m1 : mat 3 5.
  
  Compute @m2l_aux 1 3 0 m1.
  Compute @m2l_aux 2 3 0 m1.
  
  (* 取出一行的辅助函数，第二个参数为列起始值，下标越界后不再保证正确 *)
  Compute mrow_aux 0 0 m1.
  Compute mrow_aux 0 1 m1.
  
  Compute mrow 1 m1.
  Compute mrow 3 m1.
  
End FunctionMatrix_Dim_NoEffect.
 *)
