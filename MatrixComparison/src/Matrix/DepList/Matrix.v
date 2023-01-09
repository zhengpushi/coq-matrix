(*
 Copyright 2022 ZhengPu Shi
  This file is part of coq-matrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Matrix implemented with Dependent List
  author    : ZhengPu Shi
  date      : 2021.12
  
  remark    :
  1. use Coq.Vectors.Vector
  2. given more functions and properties
  3. some design ideas com from CoLoR
  
*)

(* 演示矩阵定义的代码 ======== 开始 *)

Module Demo.

(* The definition of vector in Coq.Vectors.Vector *)
Inductive vec (A : Type) : nat -> Type :=
| nil : vec A 0 
| cons : A -> forall n : nat, vec A n -> vec A (S n).
(* The definition of matrix *)
Definition matrix (A : Type) (r c : nat) := @vec (@vec A c) r.

End Demo.

(* 演示矩阵定义的代码 ======== 结束 *)

(* 注意，这两个库的顺序不要颠倒，会有一点小问题，下次再仔细检查一下 *)

Require Export ListListExt.

Require Export Coq.Vectors.Fin.
Require Export Coq.Vectors.Vector.
Require Import Extraction.
Require Import Relations.
Require Import FunctionalExtensionality.
Require Import Lia.

Import ListNotations.   (* list_scope, delimiting with list *)

(** Use notations from Vecotrs.VectorNotations *)
Export VectorNotations. (* vector_scope, delimiting with vector *)

Open Scope vector_scope.
Open Scope nat_scope.


(** ** Global Notations for familiar naming style *)

Notation fin := Fin.t.

Notation vec := Vector.t.
Notation vnil := Vector.nil.

Notation vcons := Vector.cons.

Notation vhd := Vector.hd.
Notation vtl := Vector.tl.
Notation vconst := Vector.const.

Notation vnth := Vector.nth.      (* 取元素 *)
Notation vfoldl := fold_left.
Notation vfoldr := fold_right.
Notation vmap := map.
Notation vmap2 := map2.

Arguments vec {A}.
Arguments vnil {A}.
Arguments vcons [A] _ [n] _.
Arguments vhd [A n] _.
Arguments vtl [A n] _.
Arguments vconst [A] _ _.


(** ** fin decompose *)
Section fin_decompose.

  (** There isn't fin 0 *)
  Lemma fin_0 (i : fin 0) : False.
  Proof. 
    (* refine tactic:
       1. behaves like exact,
       2. the user can leave some holes in the term.
       3. generate as many subgoals as there are remaining holes in the
          elaborated term.
    *)
    refine (match i with end). 
  Qed.
  
  (** Decompose "fin (S n)" object *)
  Lemma fin_S (n : nat) (i : fin (S n)) :
    (i = Fin.F1) + { i' | i = Fin.FS i' }.
  Proof.
    (* eauto tactic:
       1. generalizes auto.
       2. it internally use a tactic close to [simple eapply]
    *)
    refine (match i with 
            | F1 => _
            | FS _ => _ 
            end); eauto.
  Qed.
  
  (** Construct a "fin n" object which equal to i *)

  Fixpoint fin_gen (n i : nat) : option (Fin.t n) :=
    match n,i with
    | O, _ => @None (Fin.t 0)
    | S n', O => Some F1
    | S n', S i' => 
      let a := fin_gen n' i' in
        match a with
        | None => None
        | Some x => Some (FS x)
        end
    end.
  
End fin_decompose.

Arguments fin_S {n}.


(** ** vec decompose *)
Section vec_decompose.

  Variable A : Type.
  
  (** all vec 0 are same *)
  Lemma vec_0 (v : @vec A 0) : v = vnil.
  Proof.
    refine (match v with vnil => _ end). auto.
  Qed.

  (** vec (S n) could be decomposed, exist: x:A, v':vec n *)
  Lemma vec_S {n : nat} (v : @vec A (S n)) :
    {x & {v' | v = vcons x v'}}.  (* sig T *)
  Proof.
    refine (match v with
            | vcons x v' =>  _
            end); eauto.
  Qed.
 
End vec_decompose.

Arguments vec_0 {A}.
Arguments vec_S {A n}.


(** ** Equality of vec *)
Section veq.

  Variable A : Type.
  Variable Teqb : A -> A -> bool.
  Variable Teq_dec : forall (x y : A), {x = y} + {x <> y}.
  
  (** Equality is decidable *)
  Lemma veq_dec : forall {n} (v1 v2 : @vec A n), {v1 = v2} + {v1 <> v2}.
  Proof.
    induction n; intros.
    - rewrite (vec_0 v1);rewrite (vec_0 v2). left. auto.
    - pose proof vec_S v1 as [x1 [v1' ->]].
      pose proof vec_S v2 as [x2 [v2' ->]]. 
      destruct (IHn v1' v2'), (Teq_dec x1 x2); subst; auto;
      try right; intros H; apply cons_inj in H; destruct H; auto.
  Qed.

End veq.

(* Arguments veq {A} {n}. *)
Arguments veq_dec {A} _ {n}.


(** ** vmap2 *)
Section vmap2.
  
  Variable A : Type.
  Variable f : A -> A -> A.
  Variable f_comm : forall a b, f a b = f b a.
  Lemma vmap2_comm : forall n (v1 v2 : @vec A n),
    vmap2 f v1 v2 = vmap2 f v2 v1.
  Proof.
    induction n; intros; simpl.
    - rewrite (vec_0 v1),(vec_0 v2). auto.
    - pose proof vec_S v1 as [x1 [v1' ->]].
      pose proof vec_S v2 as [x2 [v2' ->]]. simpl. f_equal; auto.
  Qed.

End vmap2.

(** ** vnth,head,tail *)
Section vnth_head_tail.

  Variable A : Type.
  
  Lemma vnth_head : forall n (v : @vec A (S n)), vhd v = vnth v F1.
  Proof. 
    intros. pose proof vec_S v as [x1 [v1' ->]]. auto.
  Qed.

  Lemma vnth_tail : forall n (v : @vec A (S n)) (fn : fin n),
    vnth (vtl v) fn = vnth v (FS fn).
  Proof. 
    intros. pose proof vec_S v as [x1 [v1' ->]]. auto.
  Qed.
  
  Lemma vnth_nil : forall (fn : fin 0), vnth vnil fn -> False.
  Proof.
    intros. apply (fin_0 fn).
  Qed.

End vnth_head_tail.


(** ** Build vector with a function *)
Section vmake.

  Variable A : Type.
  Variable A0 : A.

  (** Build vector with a function [gen: fin n -> A] *)
  Fixpoint vmake {n} : (fin n -> A) -> vec n :=
    match n with
    | O => fun _ => []
    | S n' => fun (gen : fin (S n') -> A) =>
       (gen F1) :: (vmake (fun (fn':fin n') => gen (FS fn'))) 
    end.
    
  (** nth element of a vector generated by vmake, equal to [gen i] *)
  Lemma vmake_nth : forall n gen (fn : fin n), nth (vmake gen) fn = gen fn.
  Proof.
    induction n; intros gen fn.
    - exfalso; now apply fin_0.
    - pose proof fin_S fn as [-> | (fi & ->)].
      + auto.
      + simpl. apply IHn.
  Qed.
  
  (** head element of a vector generated by vmake, equal to [gen F1] *)
  Lemma vmake_head : forall n (gen : fin (S n) -> A) ,
    vhd (vmake gen) = gen F1.
  Proof. intros. rewrite vnth_head, vmake_nth. auto. Qed.
  
  (** tail element of a vector generated by vmake, equal to a vector with 
    generated by vmake with the next position. eg, tail [1;2;3;4] = [2;3;4] *)
  Lemma vmake_tail n (gen : fin (S n) -> A) :
    vtl (vmake gen) = vmake (fun (fn : fin n) => gen (FS fn)).
  Proof.
    (* rewrite !A: rewriting A as long as possible (at least once)
       rewrite ?A: rewriting A as long as possible (possibly never)
       rewrite 3?A: rewriting A at most three times
       rewrite 3 A or rewrite 3!A: rewriting A exact 3 times
    *)
    apply eq_nth_iff; intros; subst. rewrite vnth_tail, !vmake_nth. auto.
  Qed.

  (** 用 A0 生成的向量 等于 vconst A0 *)
  Lemma vmake_0_eq_vconst_0 : forall n, 
    vmake (fun _ : fin n => A0) = vconst A0 n.
  Proof.
    intros. 
    apply eq_nth_iff. intros ? p ->. rewrite vmake_nth, const_nth. auto.
  Qed.

  (* vmap2 f {gen} v = vmake {f (gen[i]) v[i]} *)
  Lemma vmap2_vmake_l : forall (f : A -> A -> A) n gen (v : vec n),
    vmap2 f (vmake (fun fn : fin n => gen fn)) v = 
    vmake (fun fn : fin n => f (gen fn) (vnth v fn)).
  Proof.
    intros f n.
    induction n; intros.
    - rewrite (vec_0 v). simpl. auto.
    - pose proof vec_S v as [x [v' ->]]. simpl. f_equal. auto.
  Qed.

  (* vmap2 f v {gen} = vmake {f v[i] (gen[i])} *)
  Lemma vmap2_vmake_r : forall (f : A -> A -> A) n gen (v : vec n),
    vmap2 f v (vmake (fun fn : fin n => gen fn)) = 
    vmake (fun fn : fin n => f (vnth v fn) (gen fn)).
  Proof.
    intros f n.
    induction n; intros.
    - rewrite (vec_0 v). simpl. auto.
    - pose proof vec_S v as [x [v' ->]]. simpl. f_equal. auto.
  Qed.
  
End vmake.

Arguments vmake {A n}.
Arguments vmake_nth {A n}.
Arguments vmake_0_eq_vconst_0 {A}.


(** 创建行数为 r，元素为 vnil 的矩阵，得到统一的对象 *)
Lemma vmake_nil_eq_vconstnil : forall {A} r, 
  vmake (fun _ : fin r => @vnil A) = vconst vnil r.
Proof.
  intros. 
  apply eq_nth_iff; intros; subst; rewrite ?vmake_nth.
  rewrite const_nth; auto.
Qed.

Arguments vmake_nil_eq_vconstnil {A}.


(** get / set an element of a vector *)
Section vget_vset.
  Variable A : Type.
  Variable A0 : A.

  Fixpoint vget {n} (v:vec n) (i:nat) : A :=
    match v, i with
    | [], _ => A0
    | a::v', 0 => a
    | a::v', S i' => vget v' i'
    end.

  (** Note, this is not tail recursion *)
  Fixpoint vset {n} (v:vec n) (i:nat) (x:A) : vec n :=
    match v, i with
    | [], _ => []
    | a::v', 0 => x::v'
    | a::v', S i' => a::(vset v' i' x)
    end.

End vget_vset.


(** ** Matrix Definitions *)

Section MatrixDefinition.

  Variable A : Type.
  Variable A0 : A.
  Variable Aeqb : A -> A -> bool.
  Variable Aeq_dec : forall (x y : A), {x = y} + {x <> y}.
  
  (* r 行 c 列的矩阵 *)
  Definition mat r c := @vec (@vec A c) r.
  
  (* 矩阵相等 *)
(*   Definition meq {r c} (m1 m2 : mat r c) : Prop := m1 = m2. *)
  
  (* 矩阵相等是可判定的 *)
  Lemma meq_dec : forall {r c} (m1 m2 : mat r c), {m1 = m2} + {m1 <> m2}.
  Proof.
    induction r; intros.
    - rewrite (vec_0 m1);rewrite (vec_0 m2). left. auto.
    - pose proof vec_S m1 as [v1 [m1' ->]].
      pose proof vec_S m2 as [v2 [m2' ->]]. 
      destruct (IHr c m1' m2'), (veq_dec Aeq_dec v1 v2); subst; auto;
      try right; intros H; apply cons_inj in H; destruct H; auto.
  Qed.
  
(*   (** 矩阵相等是一种等价关系 *)
  Definition meq_equiv : forall {r c}, equivalence (mat r c) meq.
  Proof.
    intros. refine (Build_equivalence _ _ _ _ _); unfold meq.
    - intros m. auto.
    - intros m1 m2 m3. intros. subst. auto.
    - intros m1 m2. intros. auto.
  Qed. *)

  (* 取矩阵的一行 *)
  Definition mrowi {r c} (M : mat r c) (fr : fin r) := vnth M fr.
  
  (* 取矩阵的一列，第一种定义 *)
  Definition mcoli {r c} (M : mat r c) :=
    fun fc : fin c => vmake (fun fr : fin r => nth (nth M fr) fc).
  
(*   (* 取矩阵的一列，第二种定义，不使用 *)
  Definition mcoli2 r c (M : mat r c) (fc : fin c) := 
    map (fun v => vnth v fc) M. *)
  
  (* 取一个元素 *)
  Definition mnth {r c} (M : mat r c) (fr : fin r) (fc : fin c) := 
    vnth (vnth M fr) fc.
  
  (** 矩阵相等，当且仅当每个元素都相同 *)
  Lemma meq_iff_nth : forall r c (M N : mat r c), 
    (forall (fr : fin r) (fc : fin c), mnth M fr fc = mnth N fr fc) -> 
    M = N.
  Proof.
    unfold mat. unfold mnth in *.
    induction r; intros.
    - rewrite (vec_0 M),(vec_0 N); auto.
    - rewrite (eta M),(eta N); f_equal.
      + apply eq_nth_iff; intros; subst; rewrite ?vmake_nth.
        rewrite ?vnth_head. auto.
      + apply IHr. intros. rewrite !vnth_tail. apply H.
  Qed.
  
  (** 取出由生成函数构成的矩阵的元素，等于直接生成该元素 *)
  Lemma mnth_gen_iff : forall {r c} fr fc (gen : fin r -> fin c -> A),
    mnth (vmake (fun fr0 : fin r => vmake (fun fc0 : fin c => gen fr0 fc0))) 
      fr fc = gen fr fc.
  Proof.
    intros. unfold mnth. rewrite vmake_nth. rewrite vmake_nth. auto.
  Qed.

  (* mcoli (vcons v m) n = vcons (vnth v n) (mcoli m n) *)
  Lemma mcoli_vcons : forall (r c : nat) (fc : fin c) (v : @vec A c) 
    (m : mat r c),
    mcoli (vcons v m) fc = vcons (vnth v fc) (mcoli m fc).
  Proof.
    destruct r; intros; simpl; auto.
  Qed.
  
  (* mcoli (vconst (vconst A0 c) r) fr) = vconst A0 r *)
  Lemma mcoli_vconst_vconst0 : forall r c fr,
    mcoli (vconst (vconst A0 c) r) fr = vconst A0 r.
  Proof.
    intros. unfold mcoli.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth.
    rewrite ?const_nth. auto.
  Qed.

  (** get / set an element of a matrix *)
  Definition mget {r c} (m:mat r c) (i j:nat) : A :=
    vget _ A0 (vget _ (vconst A0 c) m i) j.
  Definition mset {r c} (m:mat r c) (i j : nat) (x:A) : mat r c :=
    @vset _ r m i (@vset _ c (@vget _ (vconst A0 c) _ m i) j x).
  
End MatrixDefinition.

Arguments mat {A}.
(* Arguments meq {A r c}. *)
Arguments mrowi {A r c}.
Arguments mcoli {A r c}.
Arguments mnth {A r c}.
Arguments mget {A} A0 {r c}.
Arguments mset {A} A0 {r c}.


(** ** mat0, mat1 *)
Section mat0_mat1.

  Variable A : Type.
  Variable A0 A1 : A.

  (** mat0 *)
  Definition mat0 {r c} : @mat A r c :=
    vmake (fun (fr : fin r) => (vmake (fun (fc : fin c) => A0))).

  (** mat1 *)
  Definition mat1 {n} : @mat A n n :=
    vmake (fun (fr : fin n) => (vmake (fun (fc : fin n) =>
      if Fin.eq_dec fr fc then A1 else A0))).
    
End mat0_mat1.

Arguments mat0 {A A0}.
Arguments mat1 {A A0 A1}.


(* =============================================================== *)
(** ** 矩阵转置操作 *)

Section MatTrans.

  Variable A : Type.

  (* 转置。M[i][j] -> M[j][i]  *)
  Definition mtrans {r c : nat} (M : @mat A r c) : mat c r :=
    vmake (fun fc : fin c => vmake 
      (fun fr : fin r => vnth (vnth M fr) fc)).
  
  (* i-th column of transposed mat equal to i-th row of original mat. *)
  Lemma mcoli_of_transed_eq_mrowi (r c : nat) (M : @mat A r c) :
    forall (i : Fin.t r), mcoli (mtrans M) i = nth M i.
  Proof.
    intros i. unfold mcoli,mtrans.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth. auto.
  Qed.
  
  (* i-th row of transposed mat equal to i-th column of original mat *)
  Lemma mrowi_of_transed_eq_mcoli (r c : nat) (M : @mat A r c) :
    forall (i : Fin.t c), nth (mtrans M) i = mcoli M i.
  Proof.
    intros i. unfold mcoli,mtrans.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth. auto.
  Qed.
  
  (* 二次转置等于自身 *)
  Theorem mtrans_trans (r c : nat) (M : @mat A r c) : mtrans (mtrans M) = M.
  Proof.
    unfold mtrans.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth.
    auto.
  Qed.
  
  (* M[i,j] = (M^T)[j,i] *)
  Lemma mtrans_elem_inv (r c : nat) (M : @mat A r c) :
    forall (fr : fin r) (fc : fin c), 
    vnth (vnth M fr) fc = vnth (vnth (mtrans M) fc) fr.
  Proof.
    intros. unfold mtrans. rewrite ?vmake_nth. auto.
  Qed.
  
End MatTrans.

Arguments mtrans {A r c}.
Arguments mtrans_trans {A r c}.
Arguments mtrans_elem_inv {A r c}.


(** vmake 的性质 *)
Section vmake_props.

  (* 生成函数先行后列或先列后行生成的数组互为转置 *)
  Lemma vmake_rc_eq_cr {A r c} (gen : fin r -> fin c -> A) :
    let m1 := vmake (fun fr : fin r => (vmake (fun fc : fin c => gen fr fc))) in
    let m2 := vmake (fun fc : fin c => (vmake (fun fr : fin r => gen fr fc))) in
      m1 = mtrans m2.
  Proof.
    intros. unfold m1,m2,mtrans. f_equal.
    apply functional_extensionality. intros. f_equal.
    apply functional_extensionality. intros.
    rewrite ?vmake_nth. auto.
  Qed.

End vmake_props.


(* =============================================================== *)
(** ** 折叠 fold_left_rev，另一种折叠方法 *)

Section VfoldLeftRev.

  Variable A : Type.
  Variable fadd : A -> A -> A.
  Variable A0 : A.

  Fixpoint vfoldlrev {n} (v : vec n) : A :=
    match v with
      | vnil => A0
      | vcons b w => fadd (vfoldlrev w) b
    end.

End VfoldLeftRev.

Arguments vfoldlrev {A} fadd A0 {n}.


(** ** fold的一些性质 *)
Section VfoldProp.

  Variable A B : Type.
  Variable A0 : A.
  Variable fadd : A -> A -> A.
  Variable fadd_comm : forall x y, fadd x y = fadd y x.
  Variable fadd_assoc : forall x y z, fadd (fadd x y) z = fadd x (fadd y z).
  Variable fadd_0_r : forall x, fadd x A0 = x.

  (* fold (+) (a1 + a2) v = a1 + (fold (+) a2 v) *)
  Lemma vfoldl_a1a2 : forall n (a1 a2 : A) (v : @vec A n),
    vfoldl fadd (fadd a1 a2) v = fadd a1 (vfoldl fadd a2 v).
  Proof.
    induction n.
    - intros. rewrite (vec_0 v). auto.
    - intros. pose proof vec_S v as [a [v' ->]]. simpl.
      rewrite (fadd_assoc). apply IHn.
  Qed.
  
  (* fold (+) (a1 + a2) v = a1 + (fold (+) a2 v) *)
  Lemma vfoldr_a1a2 : forall n (a1 a2 : A) (v : @vec A n),
    vfoldr fadd v (fadd a1 a2) = fadd a1 (vfoldr fadd v a2).
  Proof.
    induction n.
    - intros. rewrite (vec_0 v). auto.
    - intros. pose proof vec_S v as [a [v' ->]]. simpl.
      rewrite IHn. rewrite <- ?fadd_assoc. rewrite (fadd_comm a). auto.
  Qed.
  
  (* fold (+) (a1 + a2) v = a1 + (fold (+) a2 v) *)
  Lemma vfoldlrev_a1a2 : forall n (a1 a2 : A) (v : @vec A n),
    vfoldlrev fadd (fadd a1 a2) v = fadd a1 (vfoldlrev fadd a2 v).
  Proof.
    induction n.
    - intros. rewrite (vec_0 v). simpl. auto.
    - intros. pose proof vec_S v as [a [v' ->]]. simpl.
      rewrite IHn. auto.
  Qed.
  
  (* fold (+) 0 (a::v) = a + (fold (+) 0 v) *)
  Lemma vfoldlrev_cons : forall n (a : A) (v : @vec A n),
    vfoldlrev fadd A0 (a::v) = fadd a (vfoldlrev fadd A0 v).
  Proof.
    destruct n.
    - intros. rewrite (vec_0 v). simpl. auto.
    - intros. pose proof vec_S v as [x [v' ->]]. simpl. auto.
  Qed.
  
  (* fold (+) 0 (const 0) = 0 *)
  Lemma vfoldlrev_vconstZero : forall c,
    vfoldlrev fadd A0 (vconst A0 c) = A0.
  Proof.
    induction c.
    - simpl. auto.
    - simpl. rewrite IHc. auto.
  Qed.
  
  (** foldl a0 v = foldr a0 v*)
  Lemma vfoldl_eq_vfoldr : forall {n} (v : @vec A n), 
    vfoldl fadd A0 v = vfoldr fadd v A0.
  Proof.
    induction n; intros.
    - rewrite (vec_0 v). auto.
    - pose proof (vec_S v) as [a [v' ->]]. simpl.
      rewrite <- IHn. rewrite fadd_comm.
      rewrite vfoldl_a1a2. auto.
  Qed.
  
  (** foldl a0 v = foldlrev a0 v *)
  Lemma vfoldl_eq_vfoldlrev : forall {n} (v : @vec A n), 
    vfoldl fadd A0 v = vfoldlrev fadd A0 v.
  Proof.
    induction n; intros.
    - rewrite (vec_0 v). auto.
    - pose proof (vec_S v) as [a [v' ->]]. simpl.
      rewrite <- IHn. rewrite fadd_comm.
      rewrite vfoldl_a1a2. auto.
  Qed.
  
  (** foldr v a0 = foldlrev a0 v *)
  Lemma vfoldr_eq_vfoldlrev : forall {n} (v : @vec A n), 
    vfoldr fadd v A0 = vfoldlrev fadd A0 v.
  Proof.
    intros. rewrite <- vfoldl_eq_vfoldr. rewrite vfoldl_eq_vfoldlrev. auto.
  Qed.
  
End VfoldProp.

Notation vfold := vfoldl.

Arguments vfoldl_a1a2 {A}.
Arguments vfoldlrev_a1a2 {A}.
Arguments vfoldlrev_cons {A}.


(** ** 向量的算术运算 *)

Section VecArith.

  Variable A : Type.
  Variable A0 A1 : A.
  Variable fopp : A -> A.
  Variable fadd fmul : A -> A -> A.
  Variable fadd_comm : forall x y, fadd x y = fadd y x.
  Variable fadd_assoc : forall x y z, fadd (fadd x y) z = fadd x (fadd y z).
  Variable fadd_0_l : forall x, fadd A0 x = x.
  Variable fadd_0_r : forall x, fadd x A0 = x.

  (* 取反 *)
  Definition vopp {n} (v : vec n) := map fopp v.
  
  (* 加法 *)
  Definition vadd {n} (v1 v2 : vec n) := map2 fadd v1 v2.
  
  (* 加法交换律 *)
  Lemma vadd_comm (n : nat) (v1 v2 : vec n) : vadd v1 v2 = vadd v2 v1.
  Proof.
    unfold vadd.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
    (* nth_map2: vnth (map2 f v1 v2) p1 = f (nth v1 p) (nth v2 p) *)
    rewrite ?nth_map2 with (p2:=p2) (p3:=p2); auto.
  Qed.
  
  (* 加法结合律 *)
  Lemma vadd_assoc (n : nat) (v1 v2 v3 : vec n) :
    vadd (vadd v1 v2) v3 = vadd v1 (vadd v2 v3).
  Proof.
    unfold vadd.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
    rewrite ?nth_map2 with (p2:=p2) (p3:=p2); auto.
  Qed.
  
  (* 右加零元 *)
  Lemma vadd_nil_r : forall (v : vec 0), vadd v vnil = v.
  Proof.
    intros. rewrite (vec_0 v). simpl. auto.
  Qed.
  
  (* fold (a + b) v = a + (fold b v) *)
  Lemma vfold_add : forall n a b (v : @vec A n),
    vfold fadd (fadd a b) v = fadd a (vfold fadd b v).
  Proof.
    induction n; intros.
    - rewrite (vec_0 v); simpl. auto.
    - pose proof (vec_S v) as [x [v' ->]]; simpl. rewrite ?IHn.
      rewrite fadd_assoc. f_equal.
  Qed.
  
  (* fold (a + b) v = b + (fold a v) *)
  Lemma vfold_add_rev : forall n a b (v : @vec A n),
    vfold fadd (fadd a b) v = fadd b (vfold fadd a v).
  Proof.
    induction n; intros.
    - rewrite (vec_0 v); simpl. auto.
    - pose proof (vec_S v) as [x [v' ->]]; simpl. rewrite ?IHn.
      rewrite <- ?fadd_assoc. f_equal. auto.
  Qed.
  
  (* fold (a + b) (v1 + v2) = (fold a v1) + (fold b v2) *)
  Lemma vfold_vadd : forall n a b (v1 v2 : @vec A n),
    vfold fadd (fadd a b) (vadd v1 v2) =
    fadd (vfold fadd a v1) (vfold fadd b v2).
  Proof.
    induction n; intros.
    - rewrite (vec_0 v1), (vec_0 v2). simpl. auto.
    - pose proof (vec_S v1) as [x1 [v1' ->]].
      pose proof (vec_S v2) as [x2 [v2' ->]]. simpl.
      replace (fadd (fadd a b) (fadd x1 x2))
        with (fadd (fadd a x1) (fadd b x2)).
      + rewrite IHn. f_equal.
      + rewrite ?fadd_assoc. f_equal.
        rewrite <- ?fadd_assoc. f_equal. auto.
  Qed.
  
  (* (v1 + v2)[n] = v1[n] + v2[n] *)
  Lemma vadd_nth : forall n (vl vr : @vec A n) (fn : fin n),
    vnth (vadd vl vr) fn = fadd (vnth vl fn) (vnth vr fn).
  Proof. 
    intros. unfold vadd.
    rewrite nth_map2 with (p2:=fn) (p3:=fn); auto.
  Qed.
  
  (* vadd (gen1) (gen2) = gen (gen1 + gen2) *)
  Lemma vadd_vmake_vmake : forall n gen1 gen2,
    vadd (vmake gen1) (vmake gen2) = 
    vmake (fun fn : fin n => fadd (gen1 fn) (gen2 fn)).
  Proof.
    induction n; intros; simpl; auto.
    f_equal. rewrite IHn. f_equal.
  Qed.
  
  (* vadd (vnth m1 fr) (vnth m2 fr) = gen (m1[fr] + m2[fr]) *)
  Lemma vadd_vnth_vnth : forall r c fr (m1 m2 : mat r c),
    vadd (vnth m1 fr) (vnth m2 fr) =
    vmake (fun fc : fin c => 
      fadd (vnth (vnth m1 fr) fc) (vnth (vnth m2 fr) fc)).
  Proof.
    intros.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
    rewrite vadd_nth; auto.
  Qed.
  
End VecArith.

Arguments vopp {A} fopp {n}.
Arguments vadd {A} fadd {n}.



(* =============================================================== *)
(** ** fold的更多性质 *)

Section VfoldPropMore.

  Variable A : Type.
  Variable A0 : A.
  Variable fadd fmul : A -> A -> A.
  Variable fadd_0_l : forall x, fadd A0 x = x.
  Variable fadd_0_r : forall x, fadd x A0 = x.
  Variable fadd_comm : forall x y, fadd x y = fadd y x.
  Variable fadd_assoc : forall x y z, fadd (fadd x y) z = fadd x (fadd y z).
  Variable fmul_0_r : forall x, fmul x A0 = A0.
  Variable fmul_add_distl : forall x y z,
    fmul x (fadd y z) = fadd (fmul x y) (fmul x z).
  
  (* A0构成的向量，折叠后等于 初始值 *)
  Lemma vfold_constA0 : forall n (a : A), vfold fadd a (vconst A0 n) = a.
  Proof.
    intros. induction n.
    - simpl. auto.
    - simpl. rewrite fadd_0_r. rewrite IHn. auto.
  Qed.
  
  (* sum a (b::v) = sum (fadd a b) v *)
  Lemma vfold_cons : forall n (a b : A) (v : @vec A n),
    vfold fadd a (b :: v) = vfold fadd (fadd a b) v.
  Proof.
    intros. auto.
  Qed.
  
  (* sum a (b::v) = fadd a (sum b v) *)
  Lemma vfold_cons_eq_add : forall n (a b : A) (v : @vec A n),
    vfold fadd a (b :: v) = fadd a (vfold fadd b v).
  Proof.
    induction n; intros.
    - rewrite (vec_0 v). simpl. auto.
    - pose proof (vec_S v) as [x [v' ->]]. simpl.
      rewrite <- IHn. simpl. f_equal.
      rewrite <- fadd_assoc. f_equal; auto.
  Qed.
  
  (* sum a (b::v) = fadd b (sum a v) *)
  Lemma vfold_cons_eq_add_exchg : forall n (a b : A) (v : @vec A n),
    vfold fadd a (b :: v) = fadd b (vfold fadd a v).
  Proof.
    induction n; intros.
    - rewrite (vec_0 v). simpl. auto.
    - pose proof (vec_S v) as [x [v' ->]]. simpl.
      rewrite <- IHn. simpl. f_equal.
      rewrite ?fadd_assoc. f_equal; auto.
  Qed.
  
  (* sum (a + b) (vmap2 f v1 v2) = f (sum a v1) (sum b v2) *)
  Lemma vfold_vmap2 : forall n a b (v1 v2 : @vec A n),
    vfold fadd (fadd a b) (vmap2 fadd v1 v2) = 
    fadd (vfold fadd a v1) (vfold fadd b v2).
  Proof.
    induction n.
    - intros. rewrite (vec_0 v1),(vec_0 v2). compute. auto.
    - intros.
      pose proof (vec_S v1) as [x1 [v1' ->]].
      pose proof (vec_S v2) as [x2 [v2' ->]].
      simpl.
      rewrite <- IHn. f_equal.
      rewrite ?fadd_assoc. f_equal.
      rewrite <- ?fadd_assoc. f_equal. auto.
  Qed.
  
  (* sum A0 (vmap2 f v1 v2) = f (sum A0 v1) (sum A0 v2) *)
  Lemma vfold_vmap2_A0 : forall n (v1 v2 : @vec A n),
    vfold fadd A0 (vmap2 fadd v1 v2) = 
    fadd (vfold fadd A0 v1) (vfold fadd A0 v2).
  Proof.
    intros. rewrite <- vfold_vmap2. f_equal. auto.
  Qed.
  
End VfoldPropMore.

Arguments vfold_constA0 {A}.



(** ** 求和 *)
Section Sum.

  Variable A : Type.
  Variable A0 : A.
  Variable fadd : A -> A -> A.

  (* 求和 *)
  Definition sum n (v : @vec A n) := vfold fadd A0 v.
  
End Sum.

Arguments sum {A} A0 fadd {n}.


(** ** 二维求和 *)

Section Sumsum.

  Variable A : Type.
  Variable A0 : A.
  Variable fadd : A -> A -> A.
  Variable fadd_comm : forall x y, fadd x y = fadd y x.
  Variable fadd_assoc : forall x y z, fadd (fadd x y) z = fadd x (fadd y z).
  Variable fadd_0_r : forall x, fadd x A0 = x.
  
  (* 数组求和，每一行求和构成的向量再求和 *)
  Definition sumsum {r c} (M : @mat A r c) : A :=
    sum A0 fadd (sum (vconst A0 c) (fun v1 v2 => vadd fadd v1 v2) M).
  
  (* 用生成函数先行后列的生成一个二维数组，然后求和 *)
  Definition sumsum_rc {r c} (gen : fin r -> fin c -> A) :=
    sum A0 fadd (sum (vconst A0 c) (vadd fadd) 
      (vmake (fun fr : fin r => (vmake (fun fc : fin c => gen fr fc))))).
  
  (* 用生成函数先列后行的生成一个二维数组，然后求和 *)
  Definition sumsum_cr {r c} (gen : fin r -> fin c -> A) :=
    sum A0 fadd (sum (vconst A0 r) (vadd fadd) 
      (vmake (fun fc : fin c => (vmake (fun fr : fin r => gen fr fc))))).
  
  (* 生成函数先行后列或先列后行生成的数组求和结果相同，也就是对二维数组转置后求和与
    原二维数组求和相等 *)
(*   Lemma sumsum_rc_eq_cr : forall {r c}, @sumsum_rc r c = @sumsum_cr r c.
  Proof.
    unfold sumsum_rc, sumsum_cr.
    intros.
    apply functional_extensionality. intros.
    unfold sum.
    generalize dependent x.
    generalize dependent c.
    generalize dependent r.
    induction r; intros.
    - simpl. rewrite vfold_constA0; auto.
      replace (vmake (fun _ : fin c => vnil)) with (vconst (@vnil A) c).
      + rewrite vfold_constA0; auto.
        intros. apply vadd_nil_r.
      + clear. induction c; simpl in *; auto. f_equal. apply IHc.
    - Abort. *)
(*       replace (vmake (fun fr : fin (S r) => vmake (fun fc : fin c => x fr fc)))
      with (cons (vmake (fun fc : fin c => x  _).
 *)      
   
  (* 求和指标可交换，即双重求和时可交换两个下标 *)
(*   Lemma sumsum_trans : forall r c (M : @mat A r c),
    sumsum M = sumsum (mtrans M).
  Proof.
    intros. unfold sumsum. unfold sum. unfold mtrans.
    (* generalize dependent M.
    generalize dependent c. *)
    induction r; intros.
    - simpl. rewrite (vec_0 M). simpl.
      rewrite vmake_nil_eq_vconstnil.
      rewrite ?vfold_constA0; auto.
      apply vadd_nil_r.
    - pose proof vec_S M as [x [v ->]]. simpl.
      Check (fun v1 v2 : vec c => vadd fadd v1 v2).
      Check (@vadd A fadd c).
      replace (fun v1 v2 : vec c => vadd fadd v1 v2) with (@vadd A fadd c) in *.
      2:{ unfold vadd. auto. }
(*       rewrite vfold_cons_eq_add. *)
      rewrite vfold_vadd.
      Search vfold. f_equal.
      Check vfold_cons.
      rewrite vmap2_vmake_l.
      rewrite vfold_vadd; auto. rewrite IHr.
    Abort. *)

End Sumsum.

Arguments sumsum {A} A0 fadd {r c}.
Arguments sumsum_rc {A} A0 fadd {r c}.
Arguments sumsum_cr {A} A0 fadd {r c}.


(** ** vmap的一些性质 *)
Section VmapProp.

  Variable A : Type.
  Variable A0 : A.
  Variable fopp : A -> A.
  Variable fadd fmul : A -> A -> A.
  Variable fmul_comm : forall x y, fmul x y = fmul y x.
  Variable fmul_0_l : forall x, fmul A0 x = A0.
  Variable fmul_0_r : forall x, fmul x A0 = A0.
  
  Lemma vmap_cons : forall n a (v : vec n), 
    vmap fopp (a :: v) = (fopp a) :: (vmap fopp v).
  Proof.
    induction n; intros.
    - rewrite (vec_0 v); auto.
    - pose proof vec_S v as [x [v' ->]]. rewrite IHn. simpl. auto.
  Qed.
  
  Lemma vmap2_cons : forall n a1 a2 (v1 v2 : vec n), 
    vmap2 fadd (a1 :: v1) (a2 :: v2) = (fadd a1 a2) :: (vmap2 fadd v1 v2).
  Proof.
    induction n; intros a1 a2 v1 v2.
    - rewrite (vec_0 v1); rewrite (vec_0 v2); auto.
    - pose proof vec_S v1 as [x1 [v1' ->]].
      pose proof vec_S v2 as [x2 [v2' ->]].
      rewrite IHn. simpl. auto.
  Qed.
  
  (* vmap2 vnil v = vnil *)
  Lemma vmap2_vnil_l : forall {n} (v : @vec A n),
    vmap2 fmul (vconst A0 n) v = vconst A0 n.
  Proof.
    induction n; intros.
    - rewrite (vec_0 v). auto.
    - pose proof vec_S v as [x [v' ->]]. simpl. rewrite IHn. f_equal. auto.
  Qed.
  
  (* vmap2 v vnil = vnil *)
  Lemma vmap2_vnil_r : forall {n} (v : @vec A n),
    vmap2 fmul v (vconst A0 n) = vconst A0 n.
  Proof.
    induction n; intros.
    - rewrite (vec_0 v). auto.
    - pose proof vec_S v as [x [v' ->]]. simpl. rewrite IHn. f_equal. auto.
  Qed.
  
End VmapProp.

  
Section Vdot.

  Variable A : Type.
  Variable A0 : A.
  Variable fopp : A -> A.
  Variable fadd fmul : A -> A -> A.
  Variable fadd_comm : forall x y, fadd x y = fadd y x.
  Variable fadd_assoc : forall x y z, fadd (fadd x y) z = fadd x (fadd y z).
  Variable fmul_comm : forall x y, fmul x y = fmul y x.
  Variable fmul_assoc : forall x y z, fmul (fmul x y) z = fmul x (fmul y z).
  Variable fmul_0_l : forall x, fmul A0 x = A0.
  Variable fmul_0_r : forall x, fmul x A0 = A0.
  Variable fadd_0_l : forall x, fadd A0 x = x.
  Variable fadd_0_r : forall x, fadd x A0 = x.
  Variable fmul_add_distl : forall x y z,
    fmul x (fadd y z) = fadd (fmul x y) (fmul x z).
  Variable fmul_add_distr : forall x y z,
    fmul (fadd x y) z = fadd (fmul x z) (fmul y z).
  
  Infix "+" := fadd.
  Infix "*" := fmul.
  
  Definition vdot {n} (v1 v2 : vec n) := vfold fadd A0
    (map2 (fun x1 x2 => x1 * x2) v1 v2).
  
  Lemma vdot_comm (n : nat) (v1 v2 : vec n) : 
    vdot v1 v2 = vdot v2 v1.
  Proof.
    unfold vdot.
    destruct n.
    - rewrite (vec_0 v1); rewrite (vec_0 v2); auto.
    - pose proof vec_S v1 as [x1 [v1' ->]].
      pose proof vec_S v2 as [x2 [v2' ->]].
      f_equal. simpl. f_equal; auto.
      rewrite vmap2_comm; auto.
  Qed.

  Lemma vdot_cons : forall n a1 a2 (v1 v2 : vec n),
    vdot (a1::v1) (a2::v2) = 
    fadd (fmul a1 a2) (vdot v1 v2).
  Proof.
    intros n. unfold vdot. 
    induction n; intros a1 a2 v1 v2.
    - rewrite (vec_0 v1); rewrite (vec_0 v2); simpl; auto.
    - pose proof vec_S v1 as [x1 [v1' ->]].
      pose proof vec_S v2 as [x2 [v2' ->]].
      rewrite IHn. rewrite vmap2_cons.
      rewrite vfold_cons.
      rewrite fadd_comm. rewrite vfold_add; auto. f_equal.
      rewrite vmap2_cons. rewrite vfold_cons.
      rewrite fadd_comm. rewrite vfold_add; auto.
  Qed.
  
  Lemma vdot_nil_l : forall (v : vec 0), vdot nil v = A0.
  Proof.
    intros. rewrite (vec_0 v). unfold vdot. simpl. auto.
  Qed.
  
  Lemma vdot_nil_r : forall (v : vec 0), vdot v nil = A0.
  Proof.
    intros. rewrite (vec_0 v). unfold vdot. simpl. auto.
  Qed.
  
  Lemma vdot_vconst0_l : forall {n} (v : vec n), 
    vdot (vconst A0 n) v = A0.
  Proof.
    induction n; intros; simpl.
    - rewrite (vec_0 v); simpl. auto.
    - pose proof vec_S v as [x [v' ->]].
      rewrite vdot_cons. rewrite IHn. rewrite fmul_0_l. auto.
  Qed.
  
  Lemma vdot_vconst0_r : forall {n} (v : vec n), 
    vdot v (vconst A0 n) = A0.
  Proof.
    intros. rewrite vdot_comm. apply vdot_vconst0_l.
  Qed.
  
  Lemma vdot_vadd_distr_r : forall n (v vl vr : vec n),
    vdot v (vadd fadd vl vr) = 
    fadd (vdot v vl) (vdot v vr).
  Proof.
    induction n; intros.
    - rewrite (vec_0 v),(vec_0 vl),(vec_0 vr); simpl; auto.
    - pose proof vec_S vl as [x1 [v1' ->]].
      pose proof vec_S v  as [x2 [v2' ->]].
      pose proof vec_S vr as [x3 [v3' ->]]. simpl.
      rewrite ?vdot_cons; auto.
      rewrite IHn.
      rewrite <- ?fadd_assoc. f_equal.
      rewrite fmul_add_distl.
      rewrite -> ?fadd_assoc. f_equal.
      rewrite fadd_comm. auto.
  Qed.
  
  Lemma vdot_vadd_distr_l n (v vl vr : vec n) :
    vdot (vadd fadd vl vr) v = 
    fadd (vdot vl v) (vdot vr v).
  Proof.
    rewrite vdot_comm; auto.
    rewrite vdot_vadd_distr_r. f_equal; apply vdot_comm; auto.
  Qed.

  Lemma vdot_mult_distr_l : forall n a (v v' : vec n),
    fmul a (vdot v v') = 
    vdot (vmake (fun fn => fmul a (vnth v fn))) v'.
  Proof.
    induction n; intros.
    - rewrite (vec_0 v),(vec_0 v'). unfold vdot. simpl; auto.
    - pose proof vec_S v  as [x1 [v1 ->]].
      pose proof vec_S v' as [x2 [v2 ->]].
      simpl.
      rewrite vdot_cons; auto.
      rewrite vdot_cons; auto. rewrite <- IHn.
      rewrite fmul_add_distl. f_equal. auto.
      (* 这里的证明比 CoLoR VecArith.v vdot_mult_distr_l 简单 *)
  Qed.
  
  (* 点积的结合性 *)
  Lemma vdot_assoc : forall r c (v1 : @vec A r) (m : mat r c) 
    (v2 : vec c),
    vdot 
      v1 (vmake (fun fr : fin r => vdot (mrowi m fr) v2)) =
    vdot 
      (vmake (fun fc : fin c => vdot v1 (mcoli m fc))) v2.
  Proof.
    induction r; intros.
    - (* induction base *)
      rewrite (vec_0 v1),(vec_0 m). simpl.
      rewrite ?vdot_nil_l.
      replace (vmake (fun fc : fin c => vdot vnil 
        (mcoli vnil fc)))
        with (vconst A0 c).
      + rewrite vdot_vconst0_l; auto.
      + apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
        rewrite ?const_nth. rewrite vdot_nil_l. auto.
    - (* induction case *)
(*       pose proof vec_S v as [x1 [v1 ->]]. *)
(*       pose proof vec_S M as [v [M' ->]]. simpl. *)
(*       rewrite vdot_cons; auto.
       *)
      rewrite (eta v1).
      rewrite (eta (vmake (fun fr => vdot (mrowi m fr) v2))).
      rewrite vdot_cons; auto.
      rewrite !vnth_head.
      rewrite vmake_nth.
      rewrite vmake_tail.
      rewrite (eta m). simpl.
      (* 应用归纳假设 *)
      rewrite (IHr).
      (* 尾部点积 *)
      set (va := (vmake (fun fc : fin c => vdot (vtl v1) 
        (mcoli (vtl m) fc)))).
      (* 头部元素 *)
      set (vb := vmake (fun (fc : fin c) => vnth v1 F1 * (vnth (vhd m) fc))).
      (* 整体 *)
      set (vc := (vmake (fun fc : fin c => vdot (vcons 
        (vnth v1 F1) (vtl v1)) (mcoli (vcons (vhd m) (vtl m)) fc)))).
      (* 重要的一个关系式，将向量和矩阵的点积分解为两部分 *)
      assert (vc = vadd fadd va vb).
      + apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
        unfold va,vb,vc.
        rewrite vadd_vmake_vmake. f_equal. f_equal.
        apply functional_extensionality; intros.
        rewrite mcoli_vcons. rewrite vdot_cons; auto.
      + rewrite H.
        rewrite vdot_vadd_distr_l; auto. rewrite fadd_comm. f_equal.
        unfold vb.
        rewrite vdot_mult_distr_l; auto.
  Qed.
  
End Vdot.

Arguments vdot {A} _ _ _ {n}.
Arguments vdot_comm {A} _ _ _ _ {n}.


(** ** Mapping matrix to matrix *)
Section mmap.
  
  Variable A : Type.
  Variable f : A -> A.
  
  Definition mmap {r c} (M : mat r c) : mat r c :=
    vmake (fun fr : fin r => vmake (fun fc : fin c => 
      f (mnth M fr fc))).

  Fixpoint mmap_old {r c} (m : mat r c) : mat r c :=
    match m with
    | vnil => vnil
    | vcons h t => cons (vmap f h) (mmap_old t)
    end.
    
End mmap.

Arguments mmap {A} f {r c}.


(** ** Mapping two matrices to another matrix *)
Section mmap2.
  
  Variable A : Type.
  Variable f : A -> A -> A.
  Variable f_comm : forall a b, f a b = f b a.
  Variable f_assoc : forall a b c, f (f a b) c = f a (f b c). 

  Definition mmap2 {r c} (M1 M2 : mat r c) : mat r c :=
    vmake (fun fr : fin r => vmake (fun fc : fin c => 
      f (mnth M1 fr fc) (mnth M2 fr fc) )).

  Lemma mmap2_comm {r c} (M1 M2 : mat r c) :
    mmap2 M1 M2 = mmap2 M2 M1.
  Proof.
    unfold mmap2, mnth.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
  Qed.
  
  Lemma mmap2_assoc {r c} (M1 M2 M3 : mat r c) :
    mmap2 (mmap2 M1 M2) M3 = mmap2 M1 (mmap2 M2 M3).
  Proof.
    unfold mmap2, mnth.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
  Qed.

End mmap2.

Arguments mmap2 {A} f {r c}.
Arguments mmap2_comm {A} f f_comm {r c}.
Arguments mmap2_assoc {A} f f_assoc {r c}.


Section MatArith.

  Variable A : Type.
  Variable A0 A1 : A.
  Variable fopp : A -> A.
  Variable fadd fsub fmul : A -> A -> A.
  Variable fadd_comm : forall x y, fadd x y = fadd y x.
  Variable fadd_assoc : forall x y z, fadd (fadd x y) z = fadd x (fadd y z).
  Variable fmul_comm : forall x y, fmul x y = fmul y x.
  Variable fmul_assoc : forall x y z, fmul (fmul x y) z = fmul x (fmul y z).
  Variable fadd_0_l : forall x, fadd A0 x = x.
  Variable fadd_0_r : forall x, fadd x A0 = x.
  Variable fmul_0_l : forall x, fmul A0 x = A0.
  Variable fmul_0_r : forall x, fmul x A0 = A0.
  Variable fmul_add_distl : forall x y z,
    fmul x (fadd y z) = fadd (fmul x y) (fmul x z).
  Variable fmul_add_distr : forall x y z,
    fmul (fadd x y) z = fadd (fmul x z) (fmul y z).
  Variable fopp_opp : forall a, fopp (fopp a) = a.
  Variable fadd_opp : forall a, fadd a (fopp a) = A0.
  Variable fsub_comm : forall a b, fsub a b = fopp (fsub b a).
  Variable fsub_assoc : forall a b c, fsub (fsub a b) c = fsub a (fadd b c).
  Variable fsub_0_l : forall t, fsub A0 t = fopp t.
  Variable fsub_0_r : forall t, fsub t A0 = t.
  Variable fsub_self : forall t, fsub t t = A0.
  Variable fmul_1_l : forall a, fmul A1 a = a.
  
  (* 一元运算 *)
  Definition mopp {r c} (M : mat r c) : mat r c :=
    vmake (fun fr : fin r => vmake (fun fc : fin c => 
      fopp (mnth M fr fc))).
  
  Lemma mopp_mopp : forall {r c} (m : mat r c), mopp (mopp m) = m.
  Proof.
    intros. unfold mopp, mnth.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
  Qed.
    
  
  (* 加法 *)
  Definition madd {r c} (M1 M2 : mat r c) : mat r c :=
    vmake (fun fr : fin r => vmake (fun fc : fin c => 
      fadd (mnth M1 fr fc) (mnth M2 fr fc) )).
  
  (* 减法 *)
  Definition msub {r c} (M1 M2 : mat r c) : mat r c :=
    vmake (fun fr : fin r => vmake (fun fc : fin c => 
      fsub (mnth M1 fr fc) (mnth M2 fr fc) )).
  
  Lemma madd_comm {r c} (M1 M2 : mat r c) :
    madd M1 M2 = madd M2 M1.
  Proof.
    unfold madd, mnth.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
  Qed.
  
  Lemma madd_assoc {r c} (M1 M2 M3 : mat r c) :
    madd (madd M1 M2) M3 = madd M1 (madd M2 M3).
  Proof.
    unfold madd, mnth.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
  Qed.
  
  Lemma madd_0_l : forall {r c} (m : @mat A r c), 
    madd (@mat0 A A0 r c) m = m.
  Proof.
    unfold madd, mnth, mat0. intros.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
  Qed.
  
  Lemma madd_0_r : forall {r c} (m : @mat A r c), 
    madd m (@mat0 A A0 r c) = m.
  Proof.
    unfold madd, mnth, mat0. intros.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
  Qed.
  
  Lemma msub_comm : forall {r c} (m1 m2 : mat r c), 
    msub m1 m2 = mopp (msub m2 m1).
  Proof.
    unfold msub, mopp, mnth. intros.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
  Qed.
  
  Lemma msub_assoc : forall {r c} (m1 m2 m3 : mat r c), 
    msub (msub m1 m2) m3 = msub m1 (madd m2 m3).
  Proof.
    unfold msub, madd, mnth. intros.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
  Qed.

  Lemma msub_0_l : forall {r c} (m : mat r c), 
    msub (@mat0 A A0 r c) m = mopp m.
  Proof.
    unfold msub, mopp, mat0, mnth. intros.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
  Qed.
  
  Lemma msub_0_r : forall {r c} (m : mat r c), 
    msub m (@mat0 A A0 r c) = m.
  Proof.
    unfold msub, mat0, mnth. intros.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
  Qed.
  
  Lemma msub_self : forall {r c} (m : mat r c), 
    msub m m = (@mat0 A A0 r c).
  Proof.
    unfold msub, mat0, mnth. intros.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
  Qed.
  
  Lemma madd_mopp : forall {r c} (m : mat r c),
    madd m (mopp m) = @mat0 _ A0 r c.
  Proof.
    unfold madd, mopp, mat0, mnth. intros.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
  Qed.
  
  
  (** 矩阵数乘 *)
  Definition mcmul {r c} (a : A) (m : mat r c) : mat r c :=
    vmake (fun fr : fin r => vmake (fun fc : fin c => 
      fmul a (mnth m fr fc))).
  
  Definition mmulc {r c} (m : mat r c) (a : A) : mat r c :=
    vmake (fun fr : fin r => vmake (fun fc : fin c => 
      fmul (mnth m fr fc) a)).
  
  Lemma mmulc_eq_mcmul : forall {r c} (a : A) (m : mat r c), 
    mmulc m a = mcmul a m.
  Proof.
    unfold mcmul, mmulc, mnth. intros.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
  Qed.
  
  Lemma mcmul_assoc1 : forall {r c} (a b : A) (m : mat r c), 
    mcmul a (mcmul b m) = mcmul (fmul a b) m.
  Proof.
    unfold mcmul, mmulc, mnth. intros.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
  Qed.
  
  Lemma mcmul_assoc2 : forall {r c} (a b : A) (m : mat r c), 
    mcmul a (mcmul b m) = mcmul b (mcmul a m).
  Proof.
    unfold mcmul, mmulc, mnth. intros.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
    repeat rewrite <- fmul_assoc. f_equal. auto.
  Qed.
  
  Lemma mcmul_distr_l : forall {r c} (a : A) (m1 m2 : mat r c), 
    mcmul a (madd m1 m2) = madd (mcmul a m1) (mcmul a m2).
  Proof.
    unfold mcmul, madd, mnth. intros.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
  Qed.
  
  Lemma mcmul_distr_r : forall {r c} (a b : A) (m : mat r c), 
    mcmul (fadd a b) m = madd (mcmul a m) (mcmul b m).
  Proof.
    unfold mcmul, madd, mnth. intros.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
  Qed.
  
  Lemma mcmul_1_l : forall {r c} (m : mat r c),  mcmul A1 m = m.
  Proof.
    unfold mcmul, mnth. intros.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
  Qed.
  
  Lemma mcmul_0_l : forall {r c} (m : mat r c),  mcmul A0 m = @mat0 A A0 r c.
  Proof.
    unfold mcmul, mnth, mat0. intros.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
  Qed.
  
End MatArith.

Arguments madd {A} _ {r c}.
Arguments mopp {A} _ {r c}.
Arguments msub {A} _ {r c}.
Arguments mcmul {A} _ {r c}.
Arguments mmulc {A} _ {r c}.


Section vdotm.

  Variable A : Type.
  Variable A0 A1 : A.
  Variable fadd fmul : A -> A -> A.
  Variable fadd_comm : forall x y, fadd x y = fadd y x.
  Variable fmul_comm : forall x y, fmul x y = fmul y x.
  Variable fadd_assoc : forall x y z, fadd (fadd x y) z = fadd x (fadd y z).

  (* vdotm : vec r -> mat r c -> vec c *)
  Definition vdotm {r c} (v : vec r) (M : mat r c) : vec c :=
    vmake (fun fc : fin c => vdot A0 fadd fmul v (mcoli M fc)). 
  
  (* mdotv : mat r c -> vec c -> vec r *)
  Definition mdotv {r c} (M : mat r c) (v : vec c) : vec r :=
    vmake (fun fr : fin r => vdot A0 fadd fmul (mrowi M fr) v).

End vdotm.


(** ** 矩阵乘法 *)
Section MatMult.

  Variable A : Type.
  Variable A0 A1 : A.
  Variable fopp : A -> A.
  Variable fadd fmul : A -> A -> A.
  Variable fadd_comm : forall x y, fadd x y = fadd y x.
  Variable fadd_assoc : forall x y z, fadd (fadd x y) z = fadd x (fadd y z).
  Variable fmul_comm : forall x y, fmul x y = fmul y x.
  Variable fmul_assoc : forall x y z, fmul (fmul x y) z = fmul x (fmul y z).
  Variable fadd_0_l : forall x, fadd A0 x = x.
  Variable fadd_0_r : forall x, fadd x A0 = x.
  Variable fmul_0_l : forall x, fmul A0 x = A0.
  Variable fmul_0_r : forall x, fmul x A0 = A0.
  Variable fmul_add_distl : forall x y z,
    fmul x (fadd y z) = fadd (fmul x y) (fmul x z).
  Variable fmul_add_distr : forall x y z,
    fmul (fadd x y) z = fadd (fmul x z) (fmul y z).
  Variable fmul_1_l : forall a, fmul A1 a = a.
  Variable fmul_1_r : forall a, fmul a A1 = a.
  
  Infix "+" := fadd.
  Infix "*" := fmul.
  
  (* 矩阵乘法，定义1 *)
  Definition mmul {r s c} (M1 : mat r s) (M2 : mat s c) : mat r c :=
    vmake (fun fr : fin r => vmake (fun fc : fin c => 
      vdot A0 fadd fmul (nth M1 fr) (mcoli M2 fc) )).

  (* (A * B)^T = B^T * A^T *)
  Lemma mmul_mtrans (r s c : nat) (M1 : mat r s) (M2 : mat s c) :
    mtrans (mmul M1 M2) = mmul (mtrans M2) (mtrans M1).
  Proof.
    unfold mmul.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
    rewrite mcoli_of_transed_eq_mrowi.
    rewrite <- mtrans_elem_inv.
    rewrite ?vmake_nth.
    rewrite vdot_comm; auto. rewrite mrowi_of_transed_eq_mcoli. auto.
  Qed.
  
  Lemma mmul_assoc r s c t  (M1 : mat r s) (M2 : mat s c) (M3 : mat c t) :
    mmul (mmul M1 M2) M3 = mmul M1 (mmul M2 M3).
  Proof.
    unfold mmul. unfold mat in *.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
    (* dot的关键性证明 *)
    rewrite <- vdot_assoc; auto. f_equal.
    unfold mcoli.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
  Qed.

  (* m1 * (m2 + m3) = m1 * m2 + m1 * m3 *)
  Lemma mmul_madd_distr_l : forall {r c t} (m1 : mat r c) (m2 m3 : mat c t), 
    mmul m1 (madd fadd m2 m3) = madd fadd (mmul m1 m2) (mmul m1 m3).
  Proof.
    intros. unfold mmul, madd.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth; auto.
    rename p2 into fr0. rename p0 into fc0.
    unfold mnth.
    rewrite ?vmake_nth.
    rewrite <- vdot_vadd_distr_r; auto. f_equal.
    (* a better view *)
    unfold mcoli.
    rewrite vadd_vmake_vmake. f_equal.
    apply functional_extensionality; intros.
    rewrite ?vmake_nth. auto.
  Qed.
  
  (* (m1 + m2) * m3 = m1 * m3 + m2 * m3 *)
  Lemma mmul_madd_distr_r : forall {r c s} (m1 m2 : mat r c) (m3 : mat c s), 
    mmul (madd fadd m1 m2) m3 = madd fadd (mmul m1 m3) (mmul m2 m3).
  Proof.
    intros. unfold mmul. unfold madd.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth.
    rename p2 into fr0. rename p0 into fc0.
    unfold mnth.
    rewrite ?vmake_nth.
    rewrite <- vdot_vadd_distr_l; auto. f_equal.
    (* a better view *)
    unfold mcoli. rewrite vadd_vnth_vnth. f_equal.
  Qed.
  
  (* mat0 * m = mat0 *)
  Lemma mmul_0_l : forall {r c t} (m : mat c t), 
    mmul (@mat0 A A0 r c) m = @mat0 A A0 r t.
  Proof.
    intros. unfold mmul. unfold mat0. 
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth.
    rewrite vmake_0_eq_vconst_0.
    rewrite vdot_vconst0_l; auto.
  Qed.
  
  (* m * mat0 = mat0 *)
  Lemma mmul_0_r : forall {r c t} (m : mat r c), 
    mmul m (@mat0 A A0 c t) = @mat0 A A0 r t.
  Proof.
    intros. unfold mmul. unfold mat0. 
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth.
    rewrite ?vmake_0_eq_vconst_0.
    rewrite mcoli_vconst_vconst0.
    rewrite vdot_vconst0_r; auto.
  Qed.
  
  (* mcoli of a generated matrix get exact column *)
  Lemma mcoli_vmake : forall r c fc0 (gen : fin r -> fin c -> A),
    mcoli (vmake (fun fr : fin r => vmake (fun fc : fin c => gen fr fc))) fc0
    = vmake (fun fr : fin r => gen fr fc0).
  Proof.
    intros.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth.
    rename p2 into fr.
    generalize dependent c.
    generalize dependent fr.
    destruct r; intros.
    - inversion fr.
    - pose proof fin_S fr as [-> | (fr' & ->)].
      + simpl. rewrite vmake_nth. auto.
      + simpl. rewrite ?vmake_nth. auto.
  Qed.
  
  (* v . (col_of_mat1 fc) = v[fc] *)
  Lemma vdot_mat1col_r : forall n (fn : fin n) v,
    vdot A0 fadd fmul v 
      (vmake (fun fn' : fin n => if Fin.eq_dec fn' fn then A1 else A0)) = 
    vnth v fn.
  Proof.
    induction n; intros.
    - inversion fn.
    - simpl. pose proof (vec_S v) as [x [v' ->]].
      pose proof fin_S fn as [-> | (fn' & ->)]; simpl.
      + rewrite vdot_cons; auto.
        rewrite vmake_0_eq_vconst_0. rewrite vdot_vconst0_r; auto.
        rewrite fadd_0_r.
        destruct (Fin.eq_dec F1 F1); auto. tauto.
      + rewrite vdot_cons; auto. rewrite <- IHn.
        rewrite fmul_0_r, fadd_0_l. f_equal.
        apply eq_nth_iff; intros; subst; rewrite ?vmake_nth.
        destruct (Fin.eq_dec p2 fn').
        * subst. destruct (Fin.eq_dec (FS fn') (FS fn')); try tauto.
        * destruct (Fin.eq_dec (FS p2) (FS fn')); try tauto.
          apply Coq.Vectors.Fin.FS_inj in e. tauto.
  Qed.
  
  (* mat1^T = mat1 *)  
  Lemma mtrans_mat1 : forall n, mtrans (@mat1 A A0 A1 n) = (@mat1 A A0 A1 n).
  Proof.
    intros. unfold mtrans, mat1.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth.
    destruct (Fin.eq_dec p0 p2).
    - subst. destruct (Fin.eq_dec p2 p2); try tauto.
    - destruct (Fin.eq_dec p2 p0); try tauto. rewrite e in n0. tauto.
  Qed.
  
  (* m * mat1 = m *)
  Lemma mmul_1_r : forall {r c} (m : mat r c), 
    mmul m (@mat1 A A0 A1 c) = m.
  Proof.
    intros. unfold mmul,mat1.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth.
    apply eq_nth_iff; intros; subst; rewrite ?vmake_nth.
    rewrite mcoli_vmake.
    remember (vnth m p2) as v1.
    rewrite vdot_mat1col_r.
    auto.
  Qed.
  
  (* mat1 * m = m *)
  Lemma mmul_1_l : forall {r c} (m : mat r c), 
    mmul (@mat1 A A0 A1 r) m = m.
  Proof.
    intros.
    rewrite <- mtrans_trans at 1. rewrite mmul_mtrans.
    rewrite mtrans_mat1. rewrite mmul_1_r. rewrite mtrans_trans. auto.
  Qed.
  
End MatMult.


(** vector to list *)
Section v2l.
  Variable A : Type.
  Variable A0 : A.
  
  Fixpoint v2l {n} (v : @vec A n) : list A :=
    match v with
    | []%vector => []%list
    | (x :: v')%vector => (x :: (v2l v'))%list
    end.
  
  Lemma v2l_length : forall n (v : @vec A n), length (v2l v) = n.
  Proof.
    intros. induction v; simpl; auto.
  Qed.
  
  Fixpoint l2v (l : list A) (n : nat) : vec n :=
    match n with
    | 0 => []%vector
    | S n' => (List.hd A0 l) :: (l2v (List.tl l) n')
    end.
  
  Lemma v2l_l2v_id : forall (n : nat) (l : list A), length l = n ->
    v2l (l2v l n) = l.
  Proof.
    induction n; intros; simpl.
    - apply length_zero_iff_nil in H; auto.
    - rewrite IHn; auto.
      + destruct l; auto; simpl in *. discriminate H.
      + destruct l; auto; simpl in *. discriminate H.
  Qed.
  
  Lemma l2v_v2l_id : forall (n : nat) (v : vec n), l2v (v2l v) n = v.
  Proof.
    intros. induction v; simpl; auto. rewrite IHv. auto.
  Qed.
  
End v2l.

Arguments v2l {A n}.
Arguments l2v {A}.


(** Matrix to list list *)
Section m2l.

  Variable A : Type.
  Variable A0 : A.
  
  Fixpoint m2l {r c} (m : @mat A r c) : list (list A) :=
    match m with
    | []%vector => []%list
    | (x :: v')%vector => (v2l x) :: (m2l v')
    end.

  Fixpoint l2m (dl : list (list A)) (r c : nat) : @mat A r c :=
    match r with
    | 0 => Vector.nil
    | S n' => Vector.cons (l2v A0 (List.hd List.nil dl) c) 
      (l2m (List.tl dl) n' c)
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
    intros. induction m; simpl; auto. f_equal; auto.
    apply l2v_v2l_id.
  Qed.
  
End m2l.

Arguments m2l {A r c}.
Arguments l2m {A} A0 dl r c.


(** ** 矩阵乘法（来自 CoLoR的定义） *)
Module MatMultCoLoR.

  Section mat_mul.
    Variable A : Type.
    Variable A0 A1 : A.
    Variable fopp : A -> A.
    Variable fadd fmul : A -> A -> A.
    Variable fadd_comm : forall x y, fadd x y = fadd y x.
    Variable fadd_assoc : forall x y z, fadd (fadd x y) z = fadd x (fadd y z).
    Variable fmul_comm : forall x y, fmul x y = fmul y x.
    Variable fmul_assoc : forall x y z, fmul (fmul x y) z = fmul x (fmul y z).
    Variable fadd_0_l : forall x, fadd A0 x = x.
    Variable fadd_0_r : forall x, fadd x A0 = x.
    Variable fmul_0_r : forall x, fmul x A0 = A0.
    Variable fmul_0_l : forall x, fmul A0 x = A0.
    Variable fmul_add_distl : forall x y z,
      fmul x (fadd y z) = fadd (fmul x y) (fmul x z).
    Variable fmul_add_distr : forall x y z,
      fmul (fadd x y) z = fadd (fmul x z) (fmul y z).
    
    Infix "+" := fadd.
    Infix "*" := fmul.
    
    Lemma mat_build_spec : forall {r c} 
      (gen : forall (fr : fin r) (fc : fin c), A), 
      { M : mat r c | forall (fr : fin r) (fc : fin c), 
        mnth M fr fc = gen fr fc }.
    Proof.
      induction r; intros c gen.
      - (* case r = 0 *)
        exists (vnil). intros. inversion fr.
      - (* case m > 0 *)
        set (gen' := fun (fr : fin r) (fc : fin c) => gen (FS fr) fc).
        destruct (IHr c gen') as [Mtl Mtl_spec].
        set (gen_1 := fun (fc:fin c) => gen F1 fc).
        set (Mhd := vmake gen_1).
        set (Mhd_spec := vmake_nth gen_1).
        exists (vcons Mhd Mtl).
        intros fr fc.
        unfold mnth in *.
        pose proof fin_S fr as [-> | (fr' & ->)].
        + simpl. auto.
        + simpl. rewrite Mtl_spec. auto.
    Defined.

    Definition mat_build {r c} gen : mat r c := proj1_sig (mat_build_spec gen).

    
    Lemma mat_build_elem : forall r c gen (fr : fin r) (fc : fin c), 
      mnth (mat_build gen) fr fc = gen fr fc.
    Proof.
      intros. unfold mat_build. destruct (mat_build_spec gen). simpl. apply e.
    Qed.

    Lemma mat_build_nth : forall r c gen (fr : fin r) (fc : fin c),
      vnth (vnth (mat_build gen) fr) fc = gen fr fc.
    Proof.
      intros. fold (mrowi (mat_build gen) fr).
      fold (mnth (mat_build gen) fr fc).
      apply mat_build_elem.
    Qed.
    
    Definition mat_transpose {r c} (M : mat r c) := 
      mat_build (fun fr fc => mnth M fc fr).

    Lemma mat_transpose_idem : forall m n (M : mat m n),
      mat_transpose (mat_transpose M) = M.
    Proof.
      intros. apply meq_iff_nth. intros.
      unfold mat_transpose. rewrite !mat_build_elem. auto.
    Qed.

    Definition mat_mult {m n p} (L : mat m n) (R : mat n p) :=
      mat_build (fun fr fc => vdot A0 fadd fmul (mrowi L fr) (mcoli R fc)).
    Infix "<*>" := mat_mult (at level 40).

    Lemma mat_mult_elem : forall r m c (M : mat r m) (N : mat m c) 
      (fr : fin r) (fc : fin c),  
      vnth (vnth (mat_mult M N) fr) fc = 
      vdot A0 fadd fmul (mrowi M fr) (mcoli N fc).
    Proof. intros. unfold mat_mult. rewrite ?mat_build_nth. auto. Qed.
    
    Lemma mat_mult_spec : forall m n p (M : mat m n) (N : mat n p) 
      (fm : fin m) (fp : fin p), 
      mnth (mat_mult M N) fm fp = 
      vdot A0 fadd fmul (mrowi M fm) (mcoli N fp).
    Proof. 
      intros. unfold mnth,mcoli,mrowi.
      rewrite mat_mult_elem. auto.
    Qed.
    
    Notation vdot := (vdot).
    
    Lemma mat_mult_row : forall m n p (M : mat m n) (N : mat n p) 
      (fm : fin m),
      mrowi (M <*> N) fm = 
      vmake (fun fp => vdot A0 fadd fmul (mrowi M fm) (mcoli N fp)).
    Proof.
      intros.
      apply eq_nth_iff. intros ? fp ->.
      unfold mrowi, mcoli. rewrite vmake_nth.
      rewrite mat_mult_elem. auto.
    Qed.

    Lemma mat_mult_col : forall m n p (M : mat m n) (N : mat n p) 
      (fp : fin p),
      mcoli (M <*> N) fp = 
      vmake (fun fm => vdot A0 fadd fmul (mrowi M fm) (mcoli N fp)).
    Proof.
      intros.
      apply eq_nth_iff. intros ? fm ->.
      unfold mrowi, mcoli. rewrite ?vmake_nth.
      rewrite mat_mult_elem. auto.
    Qed.

    Lemma mat_mult_assoc : forall m n p l 
      (M : mat m n) (N : mat n p) (P : mat p l),
      M <*> (N <*> P) = M <*> N <*> P.
    Proof.
      intros. apply meq_iff_nth. intros. unfold mnth.
      rewrite !mat_mult_elem, mat_mult_row, mat_mult_col.
      apply vdot_assoc; auto.
    Qed.
  
  End mat_mul.

End MatMultCoLoR.

