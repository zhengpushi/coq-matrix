(*
  purpose   : Matrix implemented with Recursive Pair 
  author    : ZhengPu Shi
  date      : 2021.12
  
  remark    :
  1. the definition of vec inspired by Coquelicot.
  2. all definitions are polymorphism.
*)

Require Export ListListExt.

Require Export Arith.   (* minus_plus *)
Require Export Lia.
Require Export FunctionalExtensionality.
Require Export DepPair.Vector.


(** ** Definitions of matrix module, it is implemented as a Vector 2 *)
Section mat.
  
  Variable T : Type.
  
  Definition mat (r c : nat) : Type := @vec (@vec T c) r.
  
  Lemma mat_r0 (c : nat) (m : mat 0 c) : m = tt.
  Proof. destruct m. auto. Qed.
  
  Lemma mat_rS (r c : nat) (m : mat (S r) c) : {v & {m' | m = (v, m')}}.
  Proof. apply vec_S. Qed.
  
End mat.

Arguments mat {T}.
Arguments mat_r0 {T c}.
Arguments mat_rS {T r c}.

Example mat_ex1 : mat 2 3 := [[1;2;3];[4;5;6]].
Example mat_ex2 : mat 2 3 := [[7;8;9];[10;11;12]].
Example mat_ex3 : mat 3 2 := [[1;2];[3;4];[5;6]].


(** ** Construct a matrix with a function *)
Section mmake.
  
  Variable T : Type.

  Definition mmake (r c : nat) (f : nat -> nat -> T) : mat r c :=
    vmake r (fun ic => (vmake c (f ic))).
  
  Lemma mmake_row_S : forall {r c : nat} (f : nat -> nat -> T),
    mmake (S r) c f = (vmake c (f 0), mmake r c (fun i j => f (S i) j)).
  Proof.
    induction r; intros; simpl.
    - unfold mmake. rewrite vmake_S. auto.
    - rewrite IHr. unfold mmake. rewrite vmake_S. f_equal.
      rewrite vmake_S. auto.
  Qed.
  
End mmake.

Arguments mmake {T}.


(** ** Get (ir,rc) element of a matrix *)
Section mnth.
  
  Variable T : Type.
  Variable T0 : T.

  Definition mnth {r c} (m : mat r c) (ir ic : nat) : T := 
    vnth T0 ic (vnth (vrepeat c T0) ir m).
  
  Lemma mnth_mmake : forall {r c} f i j, i < r -> j < c -> 
    mnth (mmake r c f) i j = f i j.
  Proof.
    unfold mnth. unfold mmake. intros. remember (vrepeat c T0).
    rewrite vnth_vmake_valid; auto.
    rewrite vnth_vmake_valid; auto.
  Qed.

End mnth.

Arguments mnth {T} T0 {r c}.


(** ** Construct a matrix with same element *)
Section mrepeat.
  
  Variable T : Type.
  
  Definition mrepeat (r c : nat)  (def : T) : mat r c := 
    mmake r c (fun ir ic => def).

  Lemma mrepeat_r0 {c} def : mrepeat 0 c def = tt.
  Proof. compute. auto. Qed.

  Lemma mrepeat_rS {r c} def : mrepeat (S r) c def = 
    (vrepeat c def, mrepeat r c def).
  Proof.
    unfold mrepeat. unfold mmake. unfold vmake. simpl. f_equal. 
    - induction c; simpl; auto. f_equal. rewrite vmake_aux_S. apply IHc.
    - rewrite vmake_aux_S. auto.
  Qed.

  Lemma mrepeat_c0 {r} def : mrepeat r 0 def = vec0 tt r.
  Proof.
    induction r; simpl; auto.
    unfold mrepeat in *. unfold mmake in *. unfold vmake in *. simpl. f_equal.
    rewrite vmake_aux_S. auto.
  Qed.

  Lemma mat_c0 {r : nat} (m : @mat T r 0) : m = vec0 tt r.
  Proof. 
    induction r; destruct m; simpl; auto. destruct v. f_equal. apply IHr.
  Qed.
  
End mrepeat.

Arguments mrepeat {T}.
Arguments mrepeat_r0 {T c}.
Arguments mrepeat_rS {T r c}.
Arguments mrepeat_c0 {T r}.
Arguments mat_c0 {T r}.


(** ** Zero matrix *)
Section mat0.

  Variable T : Type.
  Variable T0 : T.
  
  Definition mat0 {r c} : @mat T r c := mmake r c (fun i j => T0).
  
  Lemma mat0_eq_vec0_vec0 {r c} : mat0 = vec0 (vec0 T0 c) r.
  Proof.
    unfold mat0. unfold mmake.
    rewrite vmake_zero_eq_vec0. rewrite vmake_zero_eq_vec0. auto.
  Qed.
    
  Lemma mat0_S : forall {r c}, 
    @mat0 (S r) c = ((vec0 T0 c, @mat0 r c) : mat (S r) c).
  Proof.
    intros. rewrite mat0_eq_vec0_vec0. simpl. f_equal.
    rewrite mat0_eq_vec0_vec0. auto.
  Qed.

End mat0.

Arguments mat0 {T} _ {r c}.


(** ** Mapping matrix to matrix *)
Section mmap.
  
  Variable T : Type.
  Variable f : T -> T.
  
  Fixpoint mmap {r c}  : mat r c -> mat r c :=
    match r with
    | O => fun (m : mat 0 _) => tt
    | S r' => fun (m : mat (S r') c) => (vmap f (fst m), mmap (snd m))
    end.

End mmap.

Arguments mmap {T} f {r c}.


(** ** Mapping two matrices to another matrix *)
Section mmap2.
  
  Variable T : Type.
  Variable f : T -> T -> T.
  Variable f_comm : forall a b, f a b = f b a.
  Variable f_assoc : forall a b c, f (f a b) c = f a (f b c). 

  Fixpoint mmap2 {r c}  : mat r c -> mat r c -> mat r c 
    := match r with
    | O => fun (m1 m2 : mat 0 _) => tt
    | S r' => fun (m1 m2 : mat (S r') c) => 
      (vmap2 f (fst m1) (fst m2), mmap2 (snd m1) (snd m2))
    end.

  Lemma mmap2_comm {r c} (m1 m2 : mat r c) : mmap2 m1 m2 = mmap2 m2 m1.
  Proof.
    induction r,c; intros; destruct m1,m2; auto; simpl; f_equal; auto.
    f_equal;auto. apply vmap2_comm. auto.
  Qed.

  Lemma mmap2_assoc {r c} (m1 m2 m3 : mat r c) :
    mmap2 (mmap2 m1 m2) m3 = mmap2 m1 (mmap2 m2 m3).
  Proof.
    induction r,c; intros; destruct m1,m2; auto; simpl; f_equal; auto.
    f_equal;auto. apply vmap2_assoc. auto.
  Qed.

End mmap2.

Arguments mmap2 {T} f {r c}.
Arguments mmap2_comm {T} f f_comm {r c}.
Arguments mmap2_assoc {T} f f_assoc {r c}.


(** ** Construct a matrix with a vector and a a matrix *)
Section mcons.

  Variable T : Type.
  
  (** Construct by row *)
  Definition mconsr {r c} (v : @vec T c) (m : @vec (@vec T c) r) 
    : @vec (@vec T c) (S r) :=
    (v, m).
    
  (** Construct by column *)
  Fixpoint mconsc {r c} : @vec T r -> @vec (@vec T c) r -> 
    @vec (@vec T (S c)) r :=
    match r with
    | O => fun (v : vec 0) (m : mat 0 c) => tt
    | S r' => fun (v : vec (S r')) (m : mat (S r') c) =>
        ((fst v, fst m), mconsc (snd v) (snd m))
    end.
  
  (** Equality of two forms of ConstructByRow *)
  Lemma mconsr_eq {r c} (v : @vec T c) (m : @mat T r c) : mconsr v m = (v, m).
  Proof. unfold mconsr. auto. Qed.
  
  (** Construct a matrix by rows with the matrix which row number is 0 *)
  Lemma mconsr_mr0 : forall {n} (v : @vec T n) (m : @mat T 0 n),
    mconsr v m = [v].
  Proof. intros. destruct m. unfold mconsr. auto. Qed.
  
  (** Construct a matrix by rows with the matrix which row column is 0 *)
  Lemma mconsr_mc0 : forall {n} (v : @vec T 0) (m : @mat T n 0),
    mconsr v m = (tt, m).
  Proof. intros. destruct v. unfold mconsr. auto. Qed.
  
  (** Construct a matrix by columns with the matrix which row number is 0 *)
  Lemma mconsc_mr0 : forall {n} (v : @vec T 0) (m : @vec (@vec T n) 0),
    mconsc v m = tt.
  Proof. intros. destruct m. unfold mconsc. auto. Qed.
  
  (** Note that, mconsc_mc0 is in another section below, it need v2cm *)
  
End mcons.

Arguments mconsr {T r c}.
Arguments mconsc {T r c}.
Arguments mconsr_eq {T r c}.
Arguments mconsr_mr0 {T n}.
Arguments mconsr_mc0 {T n}.
Arguments mconsc_mr0 {T n}.


(** ** Get head row, tail rows, head column and tail columns of a matrix *)
Section mhd_mtl.

  Variable T : Type.
  Variable T0 : T.
  
  (** Get head row of a matrix *)
  Definition mhdr {r c} (m : @mat T (S r) c) : vec c := fst m.
  
  (** Get tail rows of a matrix *)
  Definition mtlr {r c} (m : @mat T (S r) c) : @mat T r c := snd m.
    
  (** Get head column of a matrix *)
  Fixpoint mhdc {r c} :  @mat T r (S c) -> vec r :=
    match r with
    | O => fun (m : mat 0 (S c)) => tt
    | S r' => fun (m : mat (S r') (S c)) =>
      (fst (fst m), mhdc (snd m))
    end.
      
  (** Get tail columns of a matrix *)
  Fixpoint mtlc {r c} : @mat T r (S c) -> @mat T r c :=
    match r with
    | O => fun (m : mat 0 (S c)) => tt
    | S r' => fun (m : mat (S r') (S c)) =>
      (snd (fst m), mtlc (snd m))
    end.
    
  Lemma mhdr_mtlr {r c} (m : @mat T (S r) c) : m = (mhdr m, mtlr m).
  Proof. destruct m. simpl. auto. Qed.

  Lemma mhdc_mtlc {r c} (m : @mat T r (S c)) : m = mconsc (mhdc m) (mtlc m).
  Proof.
    induction r; destruct m; simpl; auto. destruct v; simpl. f_equal; auto.
  Qed.
  
  Lemma mhdc_repeat_repeat : forall {r c} a,
    mhdc (vrepeat r (vrepeat (S c) a)) = vrepeat r a.
  Proof.
    induction r; intros; simpl; auto. f_equal.
    rewrite <- (IHr c). f_equal.
  Qed.
  
  (** Head row of a matrix which constructed by rows *)
  Lemma mhdr_mconsr : forall {r c} (v : @vec T c) (m : @mat T r c),
    mhdr (mconsr v m) = v.
  Proof. induction r; intros; destruct m; simpl; auto. Qed.
  
  (** Tail rows of a matrix which constructed by rows *)
  Lemma mtlr_mconsr : forall {r c} (v : @vec T c) (m : @mat T r c),
    mtlr (mconsr v m) = m.
  Proof. induction r; intros; destruct m; simpl; auto. Qed.
  
  (** Head column of a matrix which constructed by columns *)
  Lemma mhdc_mconsc : forall {r c} (v : @vec T r) (m : @mat T r c),
    mhdc (mconsc v m) = v.
  Proof. induction r; intros; destruct m,v; simpl; auto. f_equal. auto. Qed.
  
  (** Tail columns of a matrix which constructed by columns *)
  Lemma mtlc_mconsc : forall {r c} (v : @vec T r) (m : @mat T r c),
    mtlc (mconsc v m) = m.
  Proof. induction r; intros; destruct m,v; simpl; auto. f_equal. auto. Qed.
  
  (** mhdr (mat0) = vec0 *)
  Lemma mhdr_mat0 : forall {r c}, mhdr (@mat0 T T0 (S r) c) = vec0 T0 c.
  Proof.
    intros. simpl. rewrite vmake_zero_eq_vec0. auto.
  Qed.
  
  (** mhdc (mat0) = vec0 *)
  Lemma mhdc_mat0 : forall {r c}, mhdc (@mat0 T T0 r (S c)) = vec0 T0 r.
  Proof.
    induction r; intros; simpl; auto. f_equal; auto.
    rewrite vmake_zero_eq_vec0. rewrite vmake_aux_S.
    rewrite vmake_aux_zero_eq_vec0.
(*     rewrite mat0_eq_vec0_vec0. (* why fail? *) *)
    rewrite <- (IHr c). f_equal.
    rewrite mat0_eq_vec0_vec0. auto.
  Qed.
  
  (** mtlr (mat0) = mat0 *)
  Lemma mtlr_mat0 : forall {r c}, mtlr (@mat0 T T0 (S r) c) = mat0 T0.
  Proof.
    intros. simpl. rewrite vmake_zero_eq_vec0.
    rewrite vmake_aux_S. rewrite vmake_aux_zero_eq_vec0.
    rewrite mat0_eq_vec0_vec0. auto.
  Qed.
  
  (** mtlc (mat0) = mat0 *)
  Lemma mtlc_mat0 : forall {r c}, mtlc (@mat0 T T0 r (S c)) = mat0 T0.
  Proof.
    induction r; intros; simpl; auto. f_equal; auto.
    repeat rewrite vmake_aux_S.
    repeat rewrite vmake_zero_eq_vec0. 
    repeat rewrite vmake_aux_zero_eq_vec0.
    replace (@mat0 T T0 (S r) c) with (vec0 T0 c, @mat0 T T0 r c).
    - f_equal; auto. rewrite <- (IHr c). f_equal.
      rewrite mat0_eq_vec0_vec0. auto.
    - rewrite mhdr_mtlr. f_equal.
      rewrite mhdr_mat0. auto. rewrite mtlr_mat0. auto.
  Qed.
    
End mhd_mtl.

Arguments mhdr {T r c}.
Arguments mtlr {T r c}.
Arguments mhdc {T r c}.
Arguments mtlc {T r c}.
Arguments mhdr_mtlr {T r c}.
Arguments mhdc_mtlc {T r c}.
Arguments mhdc_repeat_repeat {T r c}.
Arguments mhdr_mconsr {T r c}.
Arguments mtlr_mconsr {T r c}.
Arguments mhdc_mconsc {T r c}.
Arguments mtlc_mconsc {T r c}.


(** ** Unit matrix *)
Section mat1.
  
  Variable T : Type.
  Variable T0 T1 : T.
  
  Fixpoint mat1 n : mat n n :=
    match n with
    | O => let mat' : mat 0 0 := tt in mat'
    | S n' => 
      let row' : vec (S n') := (T1, vrepeat n' T0) in
      let mat' : mat n' n' := mat1 n' in
        mconsr row' (mconsc (vrepeat n' T0) mat')
    end.
  
  (* 一次实验，函数 vs 结构 *)
  (* 受 mat0 启发，另一种定义方式，说不定证明更加简洁 *)
  Definition mat1' n : mat n n := 
    mmake n n (fun ri ci => if ri =? ci then T1 else T0) .
  
  Lemma mat1_eq_mat1' : forall n, mat1 n = mat1' n.
  Proof.
  
    induction n.
    - simpl. unfold mat1'. unfold mmake. auto.
    - simpl. rewrite IHn.
      clear.
      (* a good start point, begin induction *)
      induction n.
      + simpl. auto.
      + simpl. (* ToDo: next time *) Abort.
  
(*     induction n.
    - simpl. unfold mat1'. unfold mmake. auto.
    - simpl. rewrite IHn.
      clear.
      (* a good start point *)
      unfold mat1' at 2.
      unfold mmake. unfold vmake. simpl.
      rewrite mconsr_eq. f_equal.
      + f_equal. rewrite vmake_aux_S. rewrite vmake_aux_zero_eq_vec0; auto.
      + Abort.
  
    induction n.
    - simpl. unfold mat1'. unfold mmake. auto.
    - simpl. rewrite IHn.
      clear.
      unfold mat1'.
      remember (fun ri ci : nat => if ri =? ci then T1 else T0) as f.
      unfold mmake. unfold vmake. simpl.
      rewrite mconsr_eq. f_equal.
      + f_equal. rewrite Heqf. auto. rewrite vmake_aux_S.
        rewrite <- vec0_eq_vrepeat0.
        replace (fun j : nat => f 0 (S j)) with (fun (_ : nat) => T0).
        * rewrite vmake_aux_zero_eq_vec0; auto.
        * apply functional_extensionality.
          intros. rewrite Heqf. auto.
      + rewrite vmake_aux_S.
        Abort. *)
End mat1.

Arguments mat1 {T}.
Arguments mat1' {T}.


(** ** Get row of a matrix as a vector *)
Section mrow.
  
  Variable T : Type.
  
  Definition mrow {r c} def ir (m : @mat T r c) : vec c :=
    vnth (vrepeat c def) ir m.

  Lemma mrow_0 {r c} def (m : @mat T (S r) c) : mrow def 0 m = mhdr m.
  Proof. destruct m. compute. auto. Qed.

  Lemma mrow_S {r c} def i (m : @mat T (S r) c) : 
    mrow def (S i) m = mrow def i (mtlr m).
  Proof. destruct m. simpl. unfold mrow. auto. Qed.

End mrow.

Arguments mrow {T r c}.
Arguments mrow_0 {T r c}.
Arguments mrow_S {T r c}.


(** ** Get column of a matrix as a vector *)
Section mcol.
  
  Variable T : Type.

  Fixpoint mcol {r c} def (ic : nat) : @mat T r c -> vec r :=
    match r with
    | O => fun (m : mat 0 _) => tt
    | S r' => fun (m : mat (S r') c) => 
      (vnth def ic (fst m), mcol def ic (snd m))
    end.

  Lemma mcol_0 {r c} def (m : @mat T r (S c)) : mcol def 0 m = mhdc m.
  Proof.
    induction r; destruct m; simpl; auto. f_equal; auto.
  Qed.

  Lemma mcol_S {r c} def i (m : @mat T r (S c)) : 
    mcol def (S i) m = mcol def i (mtlc m).
  Proof.
    induction r; destruct m; simpl; auto. f_equal; auto.
  Qed.

End mcol.

Arguments mcol {T r c}.
Arguments mcol_0 {T r c}.
Arguments mcol_S {T r c}.


(** Convert from a vector to a row matrix or column matrix, and convert the 
 matrix back to a vector *)
Section v2m_m2v.
  
  Variable T : Type.
  Variable T0 : T.
  
  (** Type Conversion *)
  Definition vv2m {r c} (vv : @vec (@vec T c) r) : @mat T r c := vv.
  Definition m2vv {r c} (m : @mat T r c) : @vec (@vec T c) r := m.
  
  Lemma vv2m_eq : forall {r c} (vv : @vec (@vec T c) r), vv = vv2m vv.
  Proof. intros. auto. Qed.
  Lemma m2vv_eq : forall {r c} (m : @mat T r c), m = m2vv m.
  Proof. intros. auto. Qed.
  Lemma m2vv_vv2m_id : forall {r c} (vv : @vec (@vec T c) r), 
    vv = m2vv (vv2m vv).
  Proof. intros. auto. Qed.
  Lemma vv2m_m2vv_id : forall {r c} (m : @mat T r c), m = vv2m (m2vv m).
  Proof. intros. auto. Qed.
  
  (** Convert a vector to a row matrix *)
  Definition v2rm {n} (v : @vec T n) : @mat T 1 n := [v].
  
  (** Convert a row matrix to a vector *)
  Definition rm2v {n} (m : @mat T 1 n) : @vec T n := fst m.

  (** Convert a vector to a column matrix *)
  Fixpoint v2cm {n} : @vec T n -> @mat T n 1 := match n with
  | O => fun (v : @vec T 0) => tt
  | S r' => fun (v : @vec T (S r')) => ([fst v], v2cm (snd v))
  end.

  (** Convert a column matrix to a vector *)
  Fixpoint cm2v {n} : @mat T n 1 -> @vec T n := match n with
  | O => fun (m : @mat T 0 1) => let v : @vec T 0 := tt in v
  | S r' => fun (m : @mat T (S r') 1) =>
    let v : @vec T (S r') :=
    (fst (fst m), cm2v (snd m)) in v
  end.
  
  Lemma v2rm_rm2v_id : forall {n} (m : @mat T 1 n), v2rm (rm2v m) = m.
  Proof. intros. induction n; destruct m; destruct v,m; simpl; auto. Qed.

  Lemma rm2v_v2rm_id : forall {n} (v : @vec T n), rm2v (v2rm v) = v.
  Proof. intros. induction n; destruct v; simpl; auto. Qed.

  Lemma v2cm_cm2v_id : forall {n} (m : @mat T n 1), v2cm (cm2v m) = m.
  Proof. 
    intros. induction n; destruct m; simpl; auto. destruct v. destruct v.
    simpl. f_equal. auto.
  Qed.
  
  Lemma cm2v_v2cm_id : forall {n} (v : @vec T n), cm2v (v2cm v) = v.
  Proof. intros. induction n; destruct v; simpl; auto. f_equal. auto. Qed.
  
  Lemma rm2v_eq_mhdr : forall {n} (m : @mat T 1 n), rm2v m = mhdr m.
  Proof. intros. auto. Qed.
  
  Lemma cm2v_eq_mhdc : forall {n} (m : @mat T n 1), cm2v m = mhdc m.
  Proof. intros. induction n; destruct m; simpl; auto. f_equal. auto. Qed.

  Lemma mat_r1_ex_v2rm : forall {n} (m : @mat T 1 n), {v | m = v2rm v}.
  Proof.
    induction n; intros; destruct m; destruct v,m.
    - exists tt. auto.
    - exists (t,v). auto.
  Qed.
  
  Lemma mat_c1_ex_v2cm : forall {n} (m : @mat T n 1), {v | m = v2cm v}.
  Proof.
    induction n; intros; destruct m.
    - exists tt. auto.
    - exists (cm2v ((v,m) : mat (S n) 1)). simpl. f_equal.
      + destruct v. simpl. destruct v. auto.
      + rewrite v2cm_cm2v_id. auto.
  Qed.
  
  (** Construct a matrix by columns with the matrix which row column is 0 *)
  Lemma mconsc_mc0 : forall {n} (v : @vec T n) (m : @mat T n 0),
    mconsc v m = v2cm v.
  Proof. 
    induction n; intros; destruct v,m; simpl; auto.
    destruct v0. f_equal. auto.
  Qed.
  
  (** v2cm (vec0) = mat0 *)
  Lemma v2cm_vec0_eq_mat0 : forall {n}, v2cm (@vec0 T T0 n) = @mat0 T T0 n 1.
  Proof.
    induction n; simpl; auto. 
    unfold mat0. unfold mmake. rewrite vmake_zero_eq_vec0. simpl.
    rewrite vmake_S. f_equal. 
    rewrite IHn. rewrite mat0_eq_vec0_vec0. f_equal.
  Qed.
  
  (** v2rm (vec0) = mat0 *)
  Lemma v2rm_vec0_eq_mat0 : forall {n}, v2rm (@vec0 T T0 n) = @mat0 T T0 1 n.
  Proof.
    intros. unfold v2rm. unfold mat0,mmake. rewrite vmake_zero_eq_vec0.
    rewrite vmake_zero_eq_vec0. simpl. auto.
  Qed.
  
End v2m_m2v.

Arguments v2rm {T n}.
Arguments rm2v {T n}.
Arguments v2cm {T n}.
Arguments cm2v {T n}.
Arguments v2rm_rm2v_id {T n}.
Arguments rm2v_v2rm_id {T n}.
Arguments v2cm_cm2v_id {T n}.
Arguments cm2v_v2cm_id {T n}.
Arguments rm2v_eq_mhdr {T n}.
Arguments cm2v_eq_mhdc {T n}.
Arguments mat_r1_ex_v2rm {T n}.
Arguments mat_c1_ex_v2cm {T n}.
Arguments mconsc_mc0 {T n}.


(** ** Append two matrix with same column number or row number *)
Section mapp.
  
  Variable T : Type.

  (** Append two matrix with same column number by row *)
  Definition mappr {r1 r2 c} (m1 : @mat T r1 c) (m2 : @mat T r2 c)
    : @mat T (r1 + r2) c := vapp m1 m2.

  (** Append two matrix with same row number by column *)
  Fixpoint mappc {r c1 c2} : @mat T r c1 -> @mat T r c2 -> @mat T r (c1 + c2) 
    := match r with
    | O => fun _ _ => tt
    | S r' => fun (m1 : mat (S r') c1) (m2 : mat (S r') c2) =>
      (vapp (fst m1) (fst m2), mappc (snd m1) (snd m2))
    end.

End mapp.

Arguments mappr {T r1 r2 c}.
Arguments mappc {T r c1 c2}.


(** ** Split a matrix to two parts by row or column *)
Section msplit.
  
  Variable T : Type.

  (** Split a matrix to two parts by row *)
  Definition msplitr r1 r2 {c} def (m: @mat T (r1+r2) c) 
    : (@mat T r1 c) * (@mat T (r1+r2-r1) c) :=
    (vfirstn (vrepeat c def) r1 m, vskipn r1 m).
    
  (** I can't write this lemma *)
(*   Lemma mappr_msplitr r1 r2 {c} def (m : @mat T (r1+r2) c) :
       mappr (msplitr r1 r2 def m) = m.
 *)  
  (** Convert Type as well, but too complicated!! *)
  Definition cvtMatShape r1 r2 {c} (m1 : @mat T (r1 + r2 - r1) c) 
    : @mat T r2 c.
  Proof.
    (* rewrite minus_plus in m1. *)
    rewrite Nat.add_comm in m1.
    rewrite Nat.add_sub in m1.
    exact m1.
  Defined.

  Definition msplitr' r1 r2 {c} def (m: @mat T (r1+r2) c) 
    : (@mat T r1 c) * (@mat T r2 c) :=
      (vfirstn (vrepeat c def) r1 m, cvtMatShape r1 r2 (vskipn r1 m)).
  
  Lemma mappr_msplitr' r1 r2 {c} def (m : @mat T (r1+r2) c) :
    let '(m1,m2) := msplitr' r1 r2 def m in
    let m' : @mat T (r1+r2) c := mappr m1 m2 in
      m' = m.
  Proof. 
    simpl. induction r1.
    - induction r2; destruct m; simpl.
      + unfold cvtMatShape. simpl (0+0-0). unfold eq_rect. Abort.
  
  (** Split a matrix to two parts by column *)
  Fixpoint msplitc {r} c1 c2 def : 
    (@mat T r (c1+c2)) -> (@mat T r c1) * (@mat T r (c1+c2-c1)) := 
    match r with
    | O => fun (_ : mat 0 (c1+c2)) => (tt, tt)
    | S r' => fun (m : mat (S r') (c1+c2)) =>
      let defV : vec (c1+c2) := vrepeat (c1+c2) def in
      let (m1, m2) := msplitc c1 c2 def (vtl m) in
        ((vfirstn def c1 (vhd defV m), m1), (vskipn c1 (vhd defV m), m2))
    end.
  
End msplit.

Arguments msplitr {T} r1 r2 {c}.
Arguments msplitr' {T} r1 r2 {c}.
Arguments msplitc {T} {r} c1 c2.


(** matrix addition. m1(r,c) + m2(r,c) = m(r,c) *)
Section madd.
  Variable T : Type.
  Variable T0 : T.
  Variable fadd fmul : T -> T -> T.
  Variable fadd_comm : forall a b, fadd a b = fadd b a.
  Variable fmul_comm : forall a b, fmul a b = fmul b a.
  Variable fadd_assoc : forall a b c, fadd (fadd a b) c = fadd a (fadd b c).
  Variable fmul_assoc : forall a b c, fmul (fmul a b) c = fmul a (fmul b c).
  Variable fmul_fadd_dist_l : forall a b c, 
    fmul a (fadd b c) = fadd (fmul a b) (fmul a c).
  Variable fmul_0_l : forall a, fmul T0 a = T0.
  Variable fadd_0_l : forall a, fadd T0 a = a.
  Variable fadd_0_r : forall a, fadd a T0 = a.
  
  Definition madd {r c} (m1 m2 : @mat T r c) : @mat T r c :=
    vmap2 (vadd fadd) m1 m2.
  
  Lemma madd_mconsc : forall {r c} (v1 v2 : @vec T r) 
    (m1 m2 : @vec (@vec T c) r),
    madd (mconsc v1 m1) (mconsc v2 m2) = mconsc (vadd fadd v1 v2) (madd m1 m2).
  Proof. induction r; intros; simpl; auto. f_equal. auto. Qed.
  
  Lemma madd_comm : forall {r c} (m1 m2 : @mat T r c),
     madd m1 m2 = madd m2 m1.
  Proof. intros. apply vmap2_comm. apply vadd_comm; auto. Qed.
  
  Lemma madd_assoc : forall {r c} (m1 m2 m3 : @mat T r c),
     madd (madd m1 m2) m3 = madd m1 (madd m2 m3).
  Proof. intros. apply vmap2_assoc. apply vadd_assoc; auto. Qed.
  
  Lemma madd_0_l : forall {r c} (m : @mat T r c),
    madd (mat0 T0) m = m.
  Proof.
    induction r; intros; destruct m; simpl; auto. f_equal; auto.
    - rewrite vmake_zero_eq_vec0. apply vadd_0_l. auto.
    - rewrite vmake_zero_eq_vec0. rewrite vmake_aux_S.
      rewrite vmake_aux_zero_eq_vec0. rewrite <- mat0_eq_vec0_vec0. auto.
  Qed.
  
  Lemma madd_0_r : forall {r c} (m : @mat T r c),
    madd m (mat0 T0) = m.
  Proof.
    intros. rewrite madd_comm. apply madd_0_l.
  Qed.
  
End madd.

Arguments madd {T} _ {r c}.


(** matrix substraction. m1(r,c) - m2(r,c) = m(r,c) *)
Section msub.

  Variable T : Type.
  Variable T0 : T.
  Variable fopp : T -> T.
  Variable fadd fmul : T -> T -> T.
  Definition fsub a b := fadd a (fopp b).
  Infix "+" := fadd.
  Infix "-" := fsub.
  Notation "- a" := (fopp a).
  
  Variable fopp_opp : forall a, - (- a) = a.
  Variable fadd_comm : forall a b, a + b = b + a.
  Variable fadd_assoc : forall a b c, (a + b) + c = a + (b + c).
  Variable fadd_0_l : forall t, T0 + t = t.
  Variable fadd_0_r : forall t, t + T0 = t.
  Variable fadd_opp : forall a, a + (-a) = T0.
  Variable fopp_add_dist : forall a b, -(a+b) = -a + -b.
  Variable fopp_0 : - T0 = T0.
  
  (* 矩阵减法 *)
  Definition mopp {r c} (m : mat r c) : mat r c := 
    vmap (vopp fopp) m.
  
  Definition msub {r c} (m1 m2 : @mat T r c) : @mat T r c :=
    madd fadd m1 (mopp m2).
(*     vmap2 (vsub fsub) m1 m2. *)
  
  Lemma mopp_mopp : forall {r c} (m : mat r c), mopp (mopp m) = m.
  Proof.
    induction r; intros; destruct m; simpl; auto. f_equal; auto.
    apply vopp_vopp. auto.
  Qed.
  
  Lemma msub_comm : forall {r c} (m1 m2 : @mat T r c),
     msub m1 m2 = mopp (msub m2 m1).
  Proof.
    unfold msub.
    induction r; intros; simpl; auto.
    destruct m1,m2; simpl. f_equal; auto.
    apply vsub_comm; auto.
  Qed.
  
  Lemma msub_assoc : forall {r c} (m1 m2 m3 : @mat T r c),
     msub (msub m1 m2) m3 = msub m1 (madd fadd m2 m3).
  Proof.
    unfold msub.
    induction r; intros; simpl; auto.
    destruct m1,m2,m3; simpl. f_equal; auto.
    apply vsub_assoc; auto.
  Qed.
    
  Lemma msub_0_l : forall {r c} (m : mat r c), msub (mat0 T0) m = mopp m.
  Proof.
    unfold msub.
    induction r; intros; destruct m; simpl; auto. f_equal.
    - rewrite vmake_zero_eq_vec0. apply vsub_v0_l. auto.
    - rewrite vmake_zero_eq_vec0. rewrite vmake_aux_S.
      rewrite vmake_aux_zero_eq_vec0. rewrite <- mat0_eq_vec0_vec0. auto.
  Qed.
  
  Lemma msub_0_r : forall {r c} (m : mat r c), msub m (mat0 T0) = m.
  Proof.
    intros. rewrite msub_comm. rewrite msub_0_l. apply mopp_mopp.
  Qed.
  
  Lemma msub_self : forall {r c} (m : mat r c), msub m m = (mat0 T0).
  Proof.
    unfold msub.
    induction r; intros; destruct m; simpl; auto.
    rewrite mat0_S. f_equal; auto. apply vsub_self. auto.
  Qed.

End msub.

Arguments mopp {T} _ {r c}.
Arguments msub {T} _ _ {r c}.
Arguments msub_0_r {T}.


(* constant multiplied to a matrix *)
Section mcmul_mmulc.

  Variable T : Type.
  Variable T0 T1 : T.
  Variable fadd : T -> T -> T.
  Variable fmul : T -> T -> T.
  Variable fmul_comm : forall a b, fmul a b = fmul b a.
  Variable fmul_assoc : forall a b c, fmul (fmul a b) c = fmul a (fmul b c).

  Variable fmul_add_distr_l : forall a b1 b2,
    fmul a (fadd b1 b2) = fadd (fmul a b1) (fmul a b2).
  Variable fmul_add_distr_r : forall a1 a2 b,
    fmul (fadd a1 a2) b = fadd (fmul a1 b) (fmul a2 b).
  Variable fmul_1_l : forall a, fmul T1 a = a.
  Variable fmul_0_l : forall a, fmul T0 a = T0.
  
  Definition mcmul {r c : nat} a m : mat r c := mmap (fun x => fmul a x) m.
  Definition mmulc {r c : nat} m a : mat r c := mmap (fun x => fmul x a) m.
 
  Lemma mmulc_eq_mcmul : forall {r c} (a : T) (m : mat r c), 
    mmulc m a = mcmul a m.
  Proof.
    induction r; intros; simpl; auto. f_equal; auto.
    apply vmap_eq. auto.
  Qed.
  
  Lemma mcmul_assoc1 : forall {r c} (a b : T) (m : mat r c), 
    mcmul a (mcmul b m) = mcmul (fmul a b) m.
  Proof.
    induction r; intros; simpl; auto. f_equal; auto.
    apply vmap_assoc1. auto.
  Qed.
  
  Lemma mcmul_assoc2 : forall {r c} (a b : T) (m : mat r c), 
    mcmul a (mcmul b m) = mcmul b (mcmul a m).
  Proof.
    induction r; intros; simpl; auto. f_equal; auto.
    apply vmap_assoc2. auto. intros. auto.
  Qed.
  
  Lemma mcmul_distr_l : forall {r c} (a : T) (m1 m2 : mat r c), 
    mcmul a (madd fadd m1 m2) = madd fadd (mcmul a m1) (mcmul a m2).
  Proof.
    induction r; intros; simpl; auto. f_equal; auto. 
    apply vmap_vadd_distr_l. auto.
  Qed.
  
  Lemma mcmul_distr_r : forall {r c} (a b : T) (m : mat r c), 
    mcmul (fadd a b) m = madd fadd (mcmul a m) (mcmul b m).
  Proof.
    induction r; intros; simpl; auto. f_equal; auto.
    apply vmap_vadd_distr_r. auto.
  Qed.
  
  Lemma mcmul_1_l : forall {r c} (m : mat r c), 
    mcmul T1 m = m.
  Proof.
    induction r; intros; simpl; auto. destruct m; auto. destruct m. simpl.
    f_equal; auto. apply vcmul_1_l. auto.
  Qed.
  
  Lemma mcmul_0_l : forall {r c} (m : mat r c), 
    mcmul T0 m = mat0 T0.
  Proof.
    induction r; intros; simpl; auto. destruct m; auto. simpl.
    rewrite IHr. unfold mat0.
    rewrite mmake_row_S. f_equal.
    rewrite vmake_zero_eq_vec0. clear m.
    induction c; auto. simpl. f_equal; auto.
  Qed.
  
End mcmul_mmulc.

Arguments mcmul {T} fmul {r c}.
Arguments mmulc {T} fmul {r c}.


(* Transpose a matrix *)
Section mtrans.
  
  Variable T : Type.
  Variable T0 T1 : T.
  Variable fadd : T -> T -> T.
  
  Fixpoint mtrans {r c} : @mat T r c -> mat c r :=
    match c with
    | O => fun (m : @mat T r 0) => tt
    | S c' => fun (m : @mat T r (S c')) => (mhdc m, mtrans (mtlc m))
    end.
  
  (** Head row of a transposed matrix equal to Head column *)
  Lemma mhdr_mtrans_eq_mhdc {r c} (m : @mat T r (S c)) :
    mhdr (mtrans m) = mhdc m.
  Proof. unfold mhdr. induction r; simpl; auto. Qed.
  
  (** Tail rows of a transposed matrix equal to transposed tail columns *)
  Lemma mtlr_mtrans_eq_mtrans_mtlc {r c} (m : @mat T r (S c)) :
    mtlr (mtrans m) = mtrans (mtlc m).
  Proof. unfold mtlr. induction r; destruct m; simpl; auto. Qed.
  
  (** Head column of a transposed matrix equal to Head row *)
  Lemma mhdc_mtrans_eq_mhdr {r c} (m : @mat T (S r) c) :
    mhdc (mtrans m) = mhdr m.
  Proof.
    unfold mhdr. destruct m. simpl. induction c; destruct v; simpl; auto.
    f_equal. rewrite IHc. auto.
  Qed.
  
  (** Tail columns of a transposed matrix equal to transposed tail rows *)
  Lemma mtlc_mtrans_eq_mtrans_mtlr {r c} (m : @mat T (S r) c) :
    mtlc (mtrans m) = mtrans (mtlr m).
  Proof.
    unfold mtlr. induction c; destruct m; simpl; auto.
    f_equal. rewrite IHc. simpl. auto.
  Qed.

  (** Transpose twice return back *)
  Lemma mtrans_trans {r c} (m : @mat T r c) : mtrans (mtrans m) = m.
  Proof.
    generalize dependent c.
    induction r; intros; destruct m; auto. simpl.
    rewrite mhdc_mtrans_eq_mhdr. rewrite mtlc_mtrans_eq_mtrans_mtlr.
    rewrite IHr. simpl. auto.
  Qed.
  
  (** Transpose a matrix composed by head column and tail columns, equal to 
    seperately transpose two part them append by row *)
  Lemma mtrans_hdc_tlc : forall {r c} (m : @mat T r (S c)),
    mtrans (mconsc (mhdc m) (mtlc m)) = 
    (mhdr (mtrans m), mtlr (mtrans m)).
  Proof.
    intros. destruct r; destruct m; simpl; auto. repeat f_equal;
    rewrite mhdc_mtlc; auto.
  Qed.

  (** Transpose a matrix composed by head row and tail rows, equal to 
    seperately transpose two part them append by column *)
  Lemma mtrans_hdr_tlr : forall {r c} (m : @mat T (S r) c),
    mtrans ((mhdr m, mtlr m) : @mat T (S r) c) = 
    mconsc (mhdc (mtrans m)) (mtlc (mtrans m)).
  Proof.
    intros. rewrite <- (mtrans_trans m). rewrite <- mtrans_hdc_tlc.
    repeat rewrite mtrans_trans. auto.
  Qed.
  
  (** Transpose a zero rows matrix *)
  Lemma mtrans_r0 {n} (m : @mat T 0 n) : mtrans m = vec0 tt n.
  Proof. induction n; simpl; auto; f_equal; auto. Qed.
  
  (** Transpose a zero columns matrix *)
  Lemma mtrans_c0 {n} (m : @mat T n 0) : mtrans m = (tt : @mat T 0 n).
  Proof. induction n; simpl; auto. Qed.
  
  (** Transpose a one row matrix *)
  Lemma mtrans_r1 : forall {n} (m : @mat T 1 n), mtrans m = v2cm (rm2v m).
  Proof. 
    induction n; intros; destruct m; simpl; auto. f_equal.
    destruct v; destruct m. simpl. rewrite IHn. f_equal.
  Qed.

  (** Transpose a one column matrix *)
  Lemma mtrans_c1 : forall {n} (m : @mat T n 1), mtrans m = v2rm (cm2v m).
  Proof. 
    destruct n; intros; destruct m; simpl; auto.
    destruct v; destruct v. simpl. unfold v2rm. f_equal. f_equal.
    rewrite cm2v_eq_mhdc. auto.
  Qed.

  (** Transpose a one column matrix created by a vector *) 
  Lemma mtrans_v2cm : forall {n} (v : @vec T n), mtrans (v2cm v) = v2rm v.
  Proof. 
    destruct n; intros; destruct v; simpl; auto. unfold v2rm. f_equal.
    f_equal. rewrite <- cm2v_eq_mhdc. rewrite cm2v_v2cm_id. auto.
  Qed.

  (** Transpose a one row matrix created by a vector *) 
  Lemma mtrans_v2rm : forall {n} (v : @vec T n), mtrans (v2rm v) = v2cm v.
  Proof. 
    destruct n; intros; destruct v; simpl; auto. f_equal.
    rewrite mtrans_r1. simpl. auto.
  Qed.
  
  (** Transpose a matrix which splited by row *)
  Lemma mtrans_split_r : forall {r c} (v : @vec T c) (m : @vec (@vec T c) r),
    mtrans ((v, m) : mat (S r) c) = mconsc v (mtrans m).
  Proof.
    induction c; intros; destruct v; simpl; auto. f_equal. rewrite IHc. auto.
  Qed.

  (** Transpose a matrix which splited by column *)
  Lemma mtrans_split_c : forall {r c} (v : @vec T r) (m : @vec (@vec T c) r),
    mtrans (mconsc v m) = (v, mtrans m).
  Proof.
    destruct r; intros; destruct m,v; simpl; auto.
    rewrite mhdc_mconsc. f_equal. f_equal. f_equal. apply mtlc_mconsc.
  Qed.
  
  (** (m1 + m2)^T = m1^T + m2^T *)
  Lemma mtrans_madd {r c} (m1 m2 : @mat T r c)
    : mtrans (madd fadd m1 m2) = madd fadd (mtrans m1) (mtrans m2).
  Proof.
    induction r.
    - destruct m1,m2. simpl. rewrite mtrans_r0. 
      induction c; simpl; f_equal; auto.
    - destruct m1 as [v1 m1], m2 as [v2 m2]. simpl.
      rewrite mtrans_split_r.
      unfold mat in *. repeat rewrite mtrans_split_r.
      rewrite madd_mconsc. f_equal. auto.
  Qed.
  
  (** mat0^T = mat0 *)
  Lemma mtrans_mat0 : forall {r c}, mtrans (@mat0 T T0 r c) = @mat0 T T0 c r.
  Proof.
    intros r c; generalize dependent r.
    induction c; intros; simpl.
    - rewrite mat_r0. auto.
    - replace (@mat0 T T0 (S c) r) with (vec0 T0 r, @mat0 T T0 c r).
      + f_equal; auto.
        * rewrite mhdc_mat0. auto.
        * rewrite mtlc_mat0. auto.
      + rewrite mhdr_mtlr. f_equal.
        rewrite mhdr_mat0; auto. rewrite mtlr_mat0; auto.
  Qed.
  
  (** mat1^T = mat1 *)
  Lemma mtrans_mat1 : forall {n}, mtrans (mat1 T0 T1 n) = mat1 T0 T1 n.
  Proof.
    induction n; simpl; auto.
    rewrite mhdc_mconsc. rewrite mtlc_mconsc.
    rewrite mconsr_eq. f_equal.
(*     Fail rewrite <- mtrans_split_c. *)
(*     Fail rewrite mtrans_split_r. *)
    rewrite <- mtrans_trans. rewrite mtrans_split_c. f_equal. f_equal. auto.
  Qed.
  
End mtrans.

Arguments mtrans {T r c}.
Arguments mhdr_mtrans_eq_mhdc {T r c}.
Arguments mtlr_mtrans_eq_mtrans_mtlc {T r c}.
Arguments mhdc_mtrans_eq_mhdr {T r c}.
Arguments mtlc_mtrans_eq_mtrans_mtlr {T r c}.
Arguments mtrans_trans {T r c}.
Arguments mtrans_hdc_tlc {T r c}.
Arguments mtrans_hdr_tlr {T r c}.
Arguments mtrans_r0 {T n}.
Arguments mtrans_c0 {T n}.
Arguments mtrans_r1 {T n}.
Arguments mtrans_c1 {T n}.
Arguments mtrans_v2cm {T n}.
Arguments mtrans_v2rm {T n}.
Arguments mtrans_split_r {T r c}.
Arguments mtrans_split_c {T r c}.
Arguments mtrans_madd {T} _ {r c}.


(** Inner product a vector and a matrix. v(c) *' m(r,c) = v(r) *)
Section vdotm.
  Variable T : Type.
  Variable T0 T1 : T.
  Variable fadd fmul : T -> T -> T.
  Variable fadd_comm : forall a b, fadd a b = fadd b a.
  Variable fadd_assoc : forall a b c, fadd (fadd a b) c = fadd a (fadd b c).
  Variable fadd_0_l : forall a, fadd T0 a = a.
  Variable fadd_0_r : forall a, fadd a T0 = a.
  Variable fmul_comm : forall a b, fmul a b = fmul b a.
  Variable fmul_assoc : forall a b c, fmul (fmul a b) c = fmul a (fmul b c).
  Variable fmul_0_l : forall a, fmul T0 a = T0.
  Variable fmul_0_r : forall a, fmul a T0 = T0.
  Variable fmul_1_r : forall a, fmul a T1 = a.
  Variable fmul_fadd_dist_l : forall a b c, 
    fmul a (fadd b c) = fadd (fmul a b) (fmul a c).  
  Variable fmul_fadd_dist_r : forall a b c, 
    fmul (fadd a b) c = fadd (fmul a c) (fmul b c).  
    
  Notation vdot := (vdot T0 fadd fmul).
  Notation vadd := (vadd fadd).
  Notation vcmul := (vcmul fmul).
  
  Fixpoint vdotm {r c} (v : @vec T c) : @mat T r c -> @vec T r :=
    match r with 
    | O => fun (m : mat 0 _) => tt
    | S r' => fun (m : mat (S r') c) => 
      (vdot v (fst m), vdotm v (snd m))
    end.
  
  Lemma vdotm_c0 : forall {n} (v : vec 0) (m : mat n 0), 
    vdotm v m = (vec0 T0 n).
  Proof.
    induction n; intros; destruct v; simpl; auto. f_equal.
    destruct m. simpl. auto.
  Qed.
  
  Lemma vdotm_r0 : forall {n} (v : vec n) (m : mat 0 n), vdotm v m = tt.
  Proof. induction n; intros; destruct v,m; simpl; auto. Qed.

  Lemma vdotm_v0 : forall {r c} (m : mat r c), vdotm (vec0 T0 c) m = vec0 T0 r.
  Proof.
    induction r; intros; destruct m; simpl; auto. rewrite IHr. f_equal.
    rewrite vdot_0_l; auto.
  Qed.
  
  Lemma vdotm_split : forall {r c} (v : vec c) (m : mat (S r) c),
    vdotm v m = (vdot v (mhdr m), vdotm v (mtlr m)).
  Proof. induction r; intros; simpl. f_equal. f_equal. Qed.
  
  Lemma vdotm_cons : forall {r c} a (v : vec c) (m : mat r (S c)),
    @vdotm r (S c) (a, v) m = 
    vadd (vcmul a (mhdc m)) (vdotm v (mtlc m)).
  Proof.
    induction r; intros; destruct m; simpl; auto. f_equal. rewrite IHr.
    f_equal.
  Qed.
  
  Lemma vdotm_vcmul : forall {r c} a (v : vec c) (m : mat r c),
    vdotm (vcmul a v) m = vcmul a (vdotm v m).
  Proof.
    induction r; intros; destruct m; simpl; auto.
    unfold vcmul. f_equal.
    - rewrite <- vdot_vcmul_l; auto.
    - unfold vcmul in IHr. rewrite <- IHr. auto.
  Qed.
  
  Lemma vdotm_vadd : forall {r c} (v1 v2 : vec c) (m : mat r c),
    vdotm (vadd v1 v2) m = vadd (vdotm v1 m) (vdotm v2 m).
  Proof.
    induction r; intros; destruct m; simpl; auto. f_equal; auto.
    rewrite vdot_vadd_r; auto.
  Qed.
  
  Lemma vdotm_madd_distr_l : forall {r c} (v : vec r) (m1 m2 : mat c r),
    vdotm v (madd fadd m1 m2) = vadd (vdotm v m1) (vdotm v m2).
  Proof.
    intros r c. generalize dependent r.
    induction c; intros; destruct m1,m2; simpl; auto. f_equal; auto.
    apply vdot_vadd_l; auto.
  Qed.
  
  Lemma vdotm_madd_distr_r : forall {r c} (v1 v2 : vec r) (m : mat c r),
    vdotm (vadd v1 v2) m = vadd (vdotm v1 m) (vdotm v2 m).
  Proof.
    intros r c. generalize dependent r.
    induction c; intros; destruct m; simpl; auto. f_equal; auto.
    apply vdot_vadd_r; auto.
  Qed.
  
  (** 0 . m = 0 *)
  Lemma vdotm_0_l : forall {r c} (m : @mat T r c),
    vdotm (vec0 T0 c) m = vec0 T0 r.
  Proof.
    induction r; intros; simpl; auto. f_equal; auto.
    apply vdot_0_l; auto.
  Qed.
  
  (** v . 0 = 0 *)
  Lemma vdotm_0_r : forall {r c} (v : vec c), 
    vdotm v (mat0 T0) = vec0 T0 r.
  Proof.
    induction r; intros; simpl; auto. f_equal; auto.
    - rewrite vmake_zero_eq_vec0. apply vdot_0_r; auto.
    - rewrite vmake_zero_eq_vec0. rewrite vmake_aux_S.
      rewrite vmake_aux_zero_eq_vec0.
      rewrite <- mat0_eq_vec0_vec0. apply IHr.
  Qed.
  
  (** v . 1 = v *)
  Lemma vdotm_1_r : forall {n} (v : vec n), 
    vdotm v (mat1 T0 T1 n) = v.
  Proof.
    induction n; intros; destruct v; simpl; auto. f_equal; auto.
    - rewrite vdot_S. rewrite vdot_0_r; auto.
      rewrite fmul_1_r. auto.
    - rewrite vdotm_cons. rewrite mtlc_mconsc. rewrite mhdc_mconsc.
      rewrite IHn. rewrite <- vec0_eq_vrepeat0.
      rewrite vcmul_0_r; auto. rewrite vadd_0_l; auto.
  Qed.
  
End vdotm.

Arguments vdotm {T} T0 fadd fmul {r c}.
Arguments vdotm_c0 {T} T0 fadd fmul {n}.
Arguments vdotm_r0 {T} T0 fadd fmul {n}.
Arguments vdotm_0_l {T} T0 fadd fmul fadd_0_r fmul_0_l {r c}.
Arguments vdotm_0_r {T} T0 fadd fmul fadd_0_r fmul_comm fmul_0_l {r c}.
Arguments vdotm_split {T} T0 fadd fmul {r c}.
Arguments vdotm_cons {T} T0 fadd fmul {r c}.
Arguments vdotm_vcmul {T} T0 fadd fmul fmul_comm fmul_assoc fmul_0_l 
  fmul_fadd_dist_l {r c}.
Arguments vdotm_vadd {T} T0 fadd fmul fadd_comm fadd_assoc 
  fadd_0_r fmul_comm fmul_fadd_dist_l {r c}.


(** Inner product two matrix. m(r1,c) *' (m(r2,c) = m(r1,r2) *)
Section mdot.
  Variable T : Type.
  Variable T0 T1 : T.
  Variable fadd fmul : T -> T -> T.
  Variable fadd_comm : forall a b, fadd a b = fadd b a.
  Variable fmul_comm : forall a b, fmul a b = fmul b a.
  Variable fadd_assoc : forall a b c, fadd (fadd a b) c = fadd a (fadd b c).
  Variable fmul_assoc : forall a b c, fmul (fmul a b) c = fmul a (fmul b c).
  Variable fmul_fadd_dist_l : forall a b c, 
    fmul a (fadd b c) = fadd (fmul a b) (fmul a c).  
  Variable fmul_0_l : forall a, fmul T0 a = T0.
  Variable fadd_0_l : forall a, fadd T0 a = a.
  Variable fadd_0_r : forall a, fadd a T0 = a.

  Notation vdotm := (vdotm T0 fadd fmul).
  Notation vdot := (vdot T0 fadd fmul).
  Notation vadd := (vadd fadd).
  Notation vcmul := (vcmul fmul).
  
  Fixpoint mdot {r c t} : (@mat T r c) -> (@mat T t c) -> (@mat T r t) :=
    match r with
    | O => fun (m1 : mat 0 _) m2 => tt
    | S r' => fun (m1 : mat (S r') _) m2 => 
      (vdotm (fst m1) m2, mdot (snd m1) m2)
    end.

  Lemma vdotm_comm_mdot : forall {r c} (v : vec c) (m : @mat T r c),
    vdotm v m = cm2v (mdot m (v2rm v)).
  Proof.
    induction r; intros; destruct m; simpl; auto. f_equal; auto.
    apply vdot_comm; auto.
  Qed.
  
  Lemma mhdc_mdot_eq_vdotm {r c t} (v : vec c) (m1 : mat r c) (m2 : mat t c) 
    : mhdc (@mdot t c (S r) m2 (v, m1)) = vdotm v m2.
  Proof.
    induction t; destruct m2; simpl; auto. f_equal; auto.
    apply vdot_comm. auto.
  Qed.
  
  (* mtlc (mdot m1 m2) = mdot m1 (mtlr m2). *)
  Lemma mtlc_mdot : forall {r c t} (m1 : mat r c) (m2 : mat (S t) c),
    mtlc (mdot m1 m2) = mdot m1 (mtlr m2).
  Proof. 
    induction r; intros; destruct m1; simpl; auto. f_equal. apply IHr. 
  Qed.

  Lemma mdot_split_l {r c t} (v : vec c) (m1 : mat r c) (m2 : mat t c) :
    @mdot (S r) c t (v, m1) m2 =
    mconsr (vdotm v m2) (mdot m1 m2).
  Proof. induction r; destruct m1; simpl; auto. Qed.
  
  Lemma mdot_split_r {r c t} (v : vec c) (m1 : mat r c) (m2 : mat t c) :
    @mdot r c (S t) m1 (v, m2) = 
    mconsc (cm2v (mdot m1 (v2rm v))) (mdot m1 m2).
  Proof. induction r; destruct m1; simpl; auto. f_equal. auto. Qed.

  Lemma mdot_comm : forall {r c t} (m1 : @mat T r c) (m2 : @mat T t c),
    mdot m1 m2 = mtrans (mdot m2 m1).
  Proof.
    induction r; intros; destruct m1; simpl; auto. f_equal.
    - rewrite mhdc_mdot_eq_vdotm. auto.
    - rewrite IHr. f_equal. rewrite mtlc_mdot. f_equal.
  Qed.
  
  Lemma mdot_tt : forall {r c} (m1 : mat r 0) (m2 : mat c 0),
    mdot m1 m2 = vrepeat r (vec0 T0 c).
  Proof.
    induction r; intros; destruct m1; simpl; auto. rewrite IHr; f_equal.
    destruct v. rewrite vdotm_c0. auto.
  Qed.
  
  (** Head row for a mdot of (v,M1) and M2, equal to v dot M2 *)
  Lemma mhdr_mdot : forall {r c t} (v : vec c) (m1 : mat r c) (m2 : mat t c),
    mhdr (mdot ((v, m1) : mat (S r) c) m2) = vdotm v m2.
  Proof.
    induction r; intros; destruct m1; simpl; auto.
  Qed.
  
  (** Head column for a mdot of M1 and (v,M2), equal to v dot M1 *)
  Lemma mhdc_mdot : forall {r c t} (m1 : mat r c) (v : vec c) (m2 : mat t c),
    mhdc (mdot m1 ((v, m2) : mat (S t) c)) = vdotm v m1.
  Proof.
    induction r; intros; destruct m1; simpl; auto. f_equal; auto.
    apply vdot_comm; auto.
  Qed.
  
  Lemma vdotm_assoc : forall {r c t} (v : vec r) (m2 : mat c r) (m3 : mat t c),
    vdotm (vdotm v m2) m3 = vdotm v (mdot m3 (mtrans m2)).
  Proof.
    induction r; intros; destruct v; simpl.
    - repeat rewrite vdotm_v0; auto.
    - rewrite vdotm_cons. rewrite vdotm_vadd; auto.
      rewrite vdotm_cons. f_equal.
      + rewrite vdotm_vcmul; auto. f_equal. rewrite mhdc_mdot. auto.
      + rewrite mtlc_mdot. simpl. auto.
  Qed.

  Lemma mdot_assoc :  forall {r c t s} (m1 : @mat T r c) (m2 : @mat T t c)
    (m3 : @mat T s t), mdot (mdot m1 m2) m3 = mdot m1 (mdot m3 (mtrans m2)).
  Proof.
    induction r; intros; destruct m1; simpl; auto. f_equal; auto.
    apply vdotm_assoc.
  Qed.
  
  Lemma mdot_madd_distr_l : forall {r c t} (m1 : @mat T r c) 
    (m2 m3 : @mat T t c),
    mdot m1 (madd fadd m2 m3) = madd fadd (mdot m1 m2) (mdot m1 m3).
  Proof.
    induction r; intros; destruct m1; simpl; auto. f_equal; auto.
    apply vdotm_madd_distr_l; auto.
  Qed.
  
  Lemma mdot_madd_distr_r : forall {r c t} (m1 m2 : @mat T r c) 
    (m3 : @mat T t c),
    mdot (madd fadd m1 m2) m3 = madd fadd (mdot m1 m3) (mdot m2 m3).
  Proof.
    induction r; intros; destruct m1; simpl; auto. f_equal; auto.
    apply vdotm_madd_distr_r; auto.
  Qed.
  
  Lemma mdot_0_r : forall {r c t} (m : @mat T r c),
    mdot m (@mat0 T T0 t c) = mat0 T0.
  Proof.
    induction r; intros; destruct m; simpl.
    - rewrite mat_r0; auto.
    - replace (@mat0 T T0 (S r) t) with (vec0 T0 t, @mat0 T T0 r t).
      + f_equal; auto. apply vdotm_0_r; auto.
      + rewrite mat0_S. auto. 
  Qed.
  
  Lemma mdot_0_l : forall {r c t} (m : @mat T t c),
    mdot (@mat0 T T0 r c) m = mat0 T0.
  Proof.
    intros. rewrite mdot_comm. rewrite mdot_0_r.
    rewrite mtrans_mat0. auto.
  Qed.
  (* 
  Lemma mdot_1_l : forall {r c} (m : @mat T r c),
    mdot (mat1 T0 T1 c) m = m.
  Proof.
    induction r; intros; destruct m; simpl.
    - rewrite mat_r0; auto.
    - replace (@mat0 T T0 (S r) t) with (vec0 T0 t, @mat0 T T0 r t).
      + f_equal; auto. apply vdotm_0_r; auto.
      + rewrite mat0_S. auto. 
  Qed.
  
  Lemma mdot_0_l : forall {r c t} (m : @mat T t c),
    mdot (@mat0 T T0 r c) m = mat0 T0.
  Proof.
    intros. rewrite mdot_comm. rewrite mdot_0_r.
    rewrite mtrans_mat0. auto.
  Qed.
  
  mdot T0 fadd fmul m (mat1 T0 T1 c) = m *)

End mdot.

Arguments mdot {T} T0 fadd fmul {r c t}.
Arguments vdotm_comm_mdot {T} T0 fadd fmul fmul_comm {r c}.
Arguments mhdc_mdot_eq_vdotm {T} T0 fadd fmul fmul_comm {r c t}.
Arguments mtlc_mdot {T} T0 fadd fmul {r c t}.
Arguments mdot_split_l {T} T0 fadd fmul {r c t}.
Arguments mdot_split_r {T} T0 fadd fmul {r c t}.
Arguments mdot_comm {T} T0 fadd fmul fmul_comm {r c t}.
Arguments mdot_tt {T} T0 fadd fmul {r c}.
Arguments mhdr_mdot {T} T0 fadd fmul {r c}.
Arguments mhdc_mdot {T} T0 fadd fmul fmul_comm {r c t}.
Arguments vdotm_assoc {T} T0 fadd fmul fadd_comm fmul_comm 
  fadd_assoc fmul_assoc fmul_fadd_dist_l fmul_0_l fadd_0_r {r c t}.
Arguments mdot_assoc {T} T0 fadd fmul fadd_comm fmul_comm
  fadd_assoc fmul_assoc fmul_fadd_dist_l fmul_0_l fadd_0_r {r c t}.


(** matrix multiplication. m1(r,c) * m2(c,t) = m(r,t) *)
Section mmul.

  Variable T : Type.
  Variable T0 T1 : T.
  Variable fadd fmul : T -> T -> T.
  Variable fadd_comm : forall a b, fadd a b = fadd b a.
  Variable fadd_assoc : forall a b c, fadd (fadd a b) c = fadd a (fadd b c).
  Variable fadd_0_l : forall a, fadd T0 a = a.
  Variable fadd_0_r : forall a, fadd a T0 = a.
  Variable fmul_comm : forall a b, fmul a b = fmul b a.
  Variable fmul_assoc : forall a b c, fmul (fmul a b) c = fmul a (fmul b c).
  Variable fmul_fadd_dist_l : forall a b c, 
    fmul a (fadd b c) = fadd (fmul a b) (fmul a c).
  Variable fmul_0_l : forall a, fmul T0 a = T0.
  Variable fmul_0_r : forall a, fmul a T0 = T0.
  Variable fmul_1_l : forall a, fmul T1 a = a.
  Variable fmul_1_r : forall a, fmul a T1 = a.
  
  Definition mmul {r c s} (m1 : @mat T r c) (m2 : @mat T c s) : @mat T r s :=
    mdot T0 fadd fmul m1 (mtrans m2).

  Lemma mmul_trans {r c s} (m1 : @mat T r c) (m2 : @mat T c s) 
    : mtrans (mmul m1 m2) = mmul (mtrans m2) (mtrans m1).
  Proof.
    unfold mmul. rewrite <- mdot_comm;auto. rewrite mtrans_trans; auto.
  Qed.
  
  Lemma mmul_assoc {r c s t} (m1 : @mat T r c) (m2 : @mat T c s) 
    (m3 : @mat T s t) : mmul (mmul m1 m2) m3 = mmul m1 (mmul m2 m3).
  Proof.
    unfold mmul. rewrite <- mdot_comm; auto.
    rewrite mdot_assoc; auto. f_equal. f_equal. rewrite mtrans_trans. auto.
  Qed.

  Lemma mmul_madd_distr_l : forall {r c s} (m1 : mat r c) (m2 m3 : mat c s), 
    mmul m1 (madd fadd m2 m3) = madd fadd (mmul m1 m2) (mmul m1 m3).
  Proof.
    intros. unfold mmul. rewrite mtrans_madd.
    rewrite mdot_madd_distr_l; auto.
  Qed.
  
  Lemma mmul_madd_distr_r : forall {r c s} (m1 m2 : mat r c) (m3 : mat c s), 
    mmul (madd fadd m1 m2) m3 = madd fadd (mmul m1 m3) (mmul m2 m3).
  Proof.
    intros. unfold mmul.
    rewrite mdot_madd_distr_r; auto.
  Qed.
  
  Lemma mmul_consr_l : forall {r c s} (v1 : vec c) (m1 : mat r c) 
    (m2 : mat c s),
    mmul ((v1, m1) : mat (S r) c) m2 = 
    (vdotm T0 fadd fmul v1 (mtrans m2), mmul m1 m2).
  Proof.
    intros. unfold mmul. rewrite mdot_split_l. rewrite mconsr_eq. auto.
  Qed.
  
  (* a difficult lemma *)
  (** (v1 | m1) x (v2 / m2) = [v1^T]x[v2] + m1 x m2 *)
  Lemma mmul_consc_consr : forall {r c s} (v1 : vec r) (m1 : mat r c)
    (v2 : vec s) (m2 : mat c s),
    mmul (mconsc v1 m1) (mconsr v2 m2) = 
    madd fadd (mmul (v2cm v1) (v2rm v2)) (mmul m1 m2).
  Proof.
    unfold mmul. 
    induction r.
    - intros; simpl; auto.
    - induction c.
      + intros; simpl. destruct v1,m1,m2. destruct v0. simpl.
        rewrite vdotm_0_l; auto. rewrite vadd_0_r; auto. f_equal.
        rewrite IHr. auto.
      + intros; simpl. destruct v1,m1,m2. destruct v0. f_equal; simpl.
        * rewrite vdotm_cons. rewrite vdotm_cons.
          repeat rewrite mhdc_mtrans_eq_mhdr.
          unfold v2rm. simpl.
          rewrite mtlc_mtrans_eq_mtrans_mtlr. simpl.
          rewrite vdotm_0_l; auto.
          rewrite vadd_0_r; auto.
          rewrite (@vdotm_cons T T0 fadd fmul s (S c) t (t0,v0)).
          rewrite mhdc_mtrans_eq_mhdr. simpl. f_equal.
          rewrite mtlc_mtrans_eq_mtrans_mtlr.
          rewrite mtlr_mconsr.
          rewrite vdotm_cons.
          rewrite mhdc_mtrans_eq_mhdr, mtlc_mtrans_eq_mtrans_mtlr. simpl.
          auto.
        * auto.
  Qed.
  
  Lemma mmul_0_l : forall {r c t} (m : mat c t), 
    mmul (@mat0 T T0 r c) m = mat0 T0.
  Proof.
    intros. unfold mmul. rewrite mdot_0_l; auto.
  Qed.
  
  Lemma mmul_0_r : forall {r c t} (m : mat r c), 
    mmul m (@mat0 T T0 c t) = mat0 T0.
  Proof.
    intros. unfold mmul. rewrite mtrans_mat0. rewrite mdot_0_r; auto.
  Qed.
  
  Lemma mmul_1_r : forall {r c} (m : mat r c), mmul m (mat1 T0 T1 c) = m.
  Proof.
    induction r; intros; destruct m; simpl; auto.
    rewrite mmul_consr_l. f_equal; auto.
    rewrite mtrans_mat1. rewrite vdotm_1_r; auto.
  Qed.
  
  Lemma mmul_1_l : forall {r c} (m : mat r c), mmul (mat1 T0 T1 r) m = m.
  Proof.
    induction r; intros; destruct m; simpl; auto.
    rewrite mconsr_eq. rewrite mmul_consr_l. f_equal; auto.
    - rewrite vdotm_cons. rewrite <- vec0_eq_vrepeat0.
      rewrite vdotm_0_l; auto.
      rewrite vadd_0_r; auto.
      rewrite vcmul_1_l; auto.
      rewrite mhdc_mtrans_eq_mhdr. auto.
    - rewrite <- mconsr_eq. rewrite mmul_consc_consr.
      replace (mmul (v2cm (vrepeat r T0)) (v2rm v)) with (@mat0 T T0 r c).
      + rewrite IHr. rewrite madd_0_l; auto.
      + rewrite <- vec0_eq_vrepeat0.
        rewrite v2cm_vec0_eq_mat0. rewrite mmul_0_l. auto.
  Qed.
  
End mmul.

Arguments mmul {T} T0 fadd fmul {r c s}.
Arguments mmul_trans {T} T0 fadd fmul fmul_comm {r c s}.
Arguments mmul_assoc {T} T0 fadd fmul fadd_comm fadd_assoc 
  fadd_0_r fmul_comm fmul_assoc fmul_fadd_dist_l fmul_0_l {r c s}.


(** ** Row-vector multiply a matrix, or matrix multiply column-vector. 
  1. v(r) converted to mv(1,r)
  2. v(r) * m(r,c) = mv(1,r) * m(r,c) = m'(1,c) *)
Section vmulm_mmulv.
  
  Variable T : Type.
  Variable T0 : T.
  Variable fadd fmul : T -> T -> T.
    
  Definition vmulm {r c} (v : @vec T r) (m : @mat T r c) : (@mat T 1 c) :=
    mmul T0 fadd fmul (v2rm v) m.
    
  Definition mmulv {r c} (m : @mat T r c) (v : @vec T c) : @mat T r 1:=
    mmul T0 fadd fmul m (v2cm v).
  
End vmulm_mmulv.

Arguments vmulm {T} T0 fadd fmul {r c}.
Arguments mmulv {T} T0 fadd fmul {r c}.


(** Matrix to list list *)
Section m2l.

  Variable A : Type.
  Variable A0 : A.
  
  Fixpoint m2l {r c} : (@mat A r c) -> list (list A) :=
    match r with
    | O => fun (m : @vec (@vec A c) 0) => nil
    | S r' => fun (m : @vec (@vec A c) (S r')) =>
      cons (v2l (fst m)) (m2l (snd m))
    end.

  Fixpoint l2m (dl : list (list A)) (r c : nat) {struct r} : @mat A r c :=
    match r as r0 return (@vec (@vec A c) r0) with
    | 0 => tt
    | S n' => (l2v A0 (hd nil dl) c, l2m (tl dl) n' c)
    end.
  
  Lemma m2l_l2m_id : forall {r c} (dl : list (list A)) (H1 : length dl = r)
    (H2 : width dl c), m2l (l2m dl r c) = dl.
  Proof.
    unfold m2l,l2m. induction r; intros; simpl.
    - apply length_zero_iff_nil in H1; auto.
    - rewrite IHr; auto.
      + rewrite v2l_l2v_id; auto.
        * destruct dl; simpl in *; auto. lia.
        * destruct dl; simpl in *; auto. lia. destruct H2; auto.
      + destruct dl; simpl in *; auto. lia.
      + destruct dl; simpl in *; auto. destruct H2; auto.
  Qed.
  
  Lemma l2m_m2l_id : forall {r c} (m : mat r c), l2m (m2l m) r c = m. 
  Proof.
    induction r; intros; destruct m; simpl; auto. f_equal; auto.
    apply l2v_v2l_id.
  Qed.
  
End m2l.

Arguments m2l {A r c}.
Arguments l2m {A} A0 dl r c.

