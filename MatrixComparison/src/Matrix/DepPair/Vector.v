(*
  purpose   : Vector implmented with Recursive Pair
  author    : ZhengPu Shi
  date      : 2021.01
  
  remark    :
  1. the definition of vec inspired by Coquelicot.
  2. all definitions are polymorphism.
  
*)

Require Import Lia.
Require Import List. 

Require Export VectorThySig.

Open Scope vec_scope.

(** ** Definition of vector *)
Section vec.

  Variable T : Type.
  
  Fixpoint vec (n : nat) : Type :=
    match n with
    | O => unit
    | S n => prod T (vec n)
    end.
  
  (** all vec 0 are same *)
  Lemma vec_0 (v : vec 0) : v = tt.
  Proof. destruct v. auto. Qed.
  
(*   (** vec 1 must be one element *)
  Lemma vec_1 : forall (v : vec 1), {a | v = (a,tt)}.
  Proof. intros. destruct v,v. exists t. auto. Qed. *)
  
  (** vec (S n) must be a prod type *)
  Lemma vec_S (n : nat) (v : vec (S n)) : {x & { v' | v = (x, v')}}.
  Proof. refine (match v with (x,v') => _ end). eauto. Qed.
  
  (** Convert between "T * vec n" and "vec (S n)", just type conversion *)
  Lemma vec_eq_pair : forall {n} a (v : vec n), 
    ((a,v) : T * (vec n)) = ((a,v) : vec (S n)).
  Proof. intros; auto. Qed.
  
End vec.

Arguments vec {T}.
Arguments vec_0 {T}.
Arguments vec_S {T}.

Bind Scope vec_scope with vec.

(** ** Notations for vec *)
Notation "[ x ]" := (prod x (vec 0)) : vec_scope.
Notation "[ x1 ; .. ; xn ]" := (pair x1 .. (pair xn tt) .. ) : vec_scope.


(** ** Equality of vec *)
Section vec_eq.

  Variable T : Type.
  Variable Teqb : T -> T -> bool.
  Variable Teq_dec : forall (x y : T), {x = y} + {x <> y}.
  
  (** Equality of vec *)
  Fixpoint vec_eqb {n : nat} : vec n -> vec n -> bool := 
    match n with
    | O => fun (v1 v2 : vec 0) => true
    | S n' => fun (v1 v2 : vec (S n')) => 
      andb (Teqb (fst v1) (fst v2)) (vec_eqb (snd v1) (snd v2))
    end.
    
  (** Decidable equality on vector *)
  Lemma vec_eq_dec {n} (v1 v2 : @vec T n) : {v1 = v2} + {v1 <> v2}.
  Proof.
    induction n.
    - rewrite (vec_0 v1);rewrite (vec_0 v2). left. auto.
    - destruct v1,v2. destruct (IHn v v0), (Teq_dec t t0); subst; auto;
      try right; intros H; inversion H; auto.
  Qed.
  
End vec_eq.


(** ** Construct a vector with same element *)
Section vrepeat.

  Variable T : Type.

  Fixpoint vrepeat (n : nat) (val : T) : vec n := match n with
  | O => tt
  | S n' => (val, vrepeat n' val)
  end.
  
  Lemma vrepeat_0 a : vrepeat 0 a = tt.
  Proof. compute. auto. Qed.

  Lemma vrepeat_S r a : vrepeat (S r) a = (a, vrepeat r a).
  Proof. induction r; simpl; auto. Qed.

End vrepeat.

Arguments vrepeat {T}.


(** ** vec0, its elements is 0 *)
Section vec0.
  
  Variable T : Type.
  Variable T0 : T.
  
  Definition vec0 (n : nat) := vrepeat n T0.
  
  Lemma vec0_S : forall n, vec0 (S n) = (T0, vec0 n).
  Proof. intros. auto. Qed.
  
  Lemma vec0_eq_vrepeat0 : forall n, vec0 n = vrepeat n T0.
  Proof. auto. Qed.
  
End vec0.

Arguments vec0 {T}.


(** ** Get head element *)
Section vhead.
  
  Variable T : Type.
  Variable T0 : T.
  
  Definition vhd {n} : vec n -> T := match n with
  | O => fun (_ : vec O) => T0
  | S n' => fun (v : vec (S n')) => fst v
  end.

End vhead.

Arguments vhd {T} T0 {n}.


(** ** Get tail vector *)
Section vtail.

  Variable T : Type.

  Definition vtl {n} (v : @vec T (S n)) : vec n := snd v.

End vtail.

Arguments vtl {T n}.


(** ** Get last element *)
Section vlast.

  Variable T : Type.
  Variable T0 : T.

  (* why fail? *)
  Fail Fixpoint vlast (n : nat) : vec n -> T := match n with
  | O => fun (_ : vec O) => T0
  | 1 => fun (v : vec 1) => fst v
  | S n' => fun (v : vec (S n')) => vlast n' (snd v)
  end.

  Fixpoint vlast {n} : vec (S n) -> T := match n with
  | O => fun (v : vec 1) => fst v
  | S n' => fun (v : vec (S (S n'))) => vlast (snd v)
  end.
  
End vlast.

Arguments vlast {T n}.


(** Construct a vector with a function *)
Section vmake.

  Variable T : Type.
  Variable T0 : T.

  (* it is wrong direction, we need (f 0, f 1 ..), but got (f n, f (n-1) ..) *)
  Fixpoint vmake_old (n : nat) (f : nat  -> T) : vec n := match n with
  | O => tt
  | S n' => (f n', vmake_old n' f)
  end.

  Fixpoint vmake_aux (n : nat) (i : nat) (f : nat  -> T) : vec n
    := match n with
  | O => tt
  | S n' => (f i, vmake_aux n' (S i) f)
  end.

  Lemma vmake_aux_S (n : nat) (i : nat) (f : nat  -> T) :
    vmake_aux n (S i) f = vmake_aux n i (fun j => f (S j)).
  Proof.
    generalize dependent f.
    generalize dependent i.
    induction n.
    - simpl. auto.
    - simpl. intros. f_equal. rewrite IHn. f_equal.
  Qed.
  
  Lemma vmake_aux_zero_eq_vec0 : forall n, 
    (vmake_aux n 0 (fun _ => T0)) = vec0 T0 n.
  Proof.
    induction n; simpl; auto. rewrite vmake_aux_S. f_equal; auto.
  Qed.
  
  
  Definition vmake (n : nat) (f : nat  -> T) : vec n := vmake_aux n 0 f.
  
  Lemma vmake_0 (f : nat  -> T) : vmake 0 f = tt.
  Proof. auto. Qed.

  Lemma vmake_S n (f : nat  -> T) : 
    vmake (S n) f = (f 0%nat, vmake n (fun i => f (S i))).
  Proof.
    unfold vmake. destruct n; simpl; auto.
    f_equal. f_equal. apply vmake_aux_S.
  Qed.
  
  Lemma vmake_zero_eq_vec0 : forall n, (vmake n (fun _ => T0)) = vec0 T0 n.
  Proof.
    unfold vmake. apply vmake_aux_zero_eq_vec0.
  Qed.

End vmake.

Arguments vmake_aux {T}.
Arguments vmake_aux_S {T}.
Arguments vmake_aux_zero_eq_vec0 {T}.
Arguments vmake_old {T}.
Arguments vmake {T}.
Arguments vmake_0 {T}.
Arguments vmake_S {T}.
Arguments vmake_zero_eq_vec0 {T}.


(** ** Append two vectors *)
Section vapp.

  Variable T : Type.

  Fixpoint vapp {n1 n2} : @vec T n1 -> vec n2 -> vec (n1 + n2) := 
    match n1 with
    | 0 => fun (v1 : vec 0) (v2 : vec n2) => v2
    | S n1' => fun (v1 : vec (S n1')) (v2 : vec n2) =>
      (fst v1, vapp (snd v1) v2)
    end.

End vapp.

Arguments vapp {T n1 n2}.


(** Reverse a vector *)
Section vrev.
  
  Variable T : Type.
  
  Fail Fixpoint vrev {n : nat} : @vec T n -> @vec T n :=
    match n with
    | O => fun _ => let v : @vec T 0 := tt in v
    | S n' => fun (v : @vec T (S n')) => let (x, v') := v in
      @vapp T n' 1 (vrev v') [x]
    end.

End vrev.


(** Get n-th element of a vector *)
Section vnth.
  
  Variable T : Type.
  Variable T0 : T.
  
  Fixpoint vnth {n} (i : nat) : (vec n) -> T := match n with
  | O => fun (_ : vec O) => T0
  | S n' => fun (v : vec (S n')) => match i with
     | O => (fst v)
     | S i' => vnth i' (snd v)
     end
  end.
  
  Lemma vnth_0 {n} (v : vec (S n)) : vnth 0 v = fst v.
  Proof. destruct v. simpl. auto. Qed.

  Lemma vnth_S {n} i (v : vec (S n)) : 
    vnth (S i) v = vnth i (snd v).
  Proof. destruct v. simpl. auto. Qed.

  (** Every element pair of two vectors are same iff the two vectors same *)
  Lemma vnth_iff : forall {n} (v1 v2 : vec n),
    v1 = v2 <-> (forall i, vnth i v1 = vnth i v2).
  Proof.
    split.
    - intros. subst. auto.
    - intros; destruct n; destruct v1,v2; auto. f_equal.
      + apply (H 0%nat).
      + Abort.  (* I cannot prove it  *)
  
  Lemma v0_nth : forall n i, vnth i (vec0 T0 n) = T0.
  Proof. induction n; intros; auto. destruct i; simpl; auto. Qed.
  
  Lemma vnth_vmake_invalid : forall {n} f i, i >= n -> vnth i (vmake n f) = T0.
  Proof. 
    induction n; intros; simpl; auto. unfold vmake in *.
    Abort.
  
  Lemma vnth_vmake_valid : forall {n} f i, i < n -> vnth i (vmake n f) = f i.
  Proof.
    induction n; intros. lia.
    simpl. unfold vmake in *. destruct i; auto.
    rewrite vmake_aux_S. rewrite IHn; auto. lia.
  Qed.

End vnth.

Arguments vnth {T} T0 {n}.


(** ** Get top k element of a vector *)
Section vfirstn.

  Variable T : Type.
  Variable T0 : T.
  
  Fixpoint vfirstn {n} (k : nat) : (vec n) -> (vec k) := 
    match n,k with
    | O, O => fun (v : vec O) => tt
    | O, S k' => fun (v : vec O) => (T0, vfirstn k' v)
    | S n', O => fun (v : vec (S n')) => tt
    | S n', S k' => fun (v : vec (S n')) => (fst v, vfirstn k' (snd v))
    end.

End vfirstn.

Arguments vfirstn {T} T0 {n}.


(** Get remain (n-k) elements of a vector *)
Section vskipn.

  Variable T : Type.

  Fixpoint vskipn {n} (k : nat) : @vec T n -> vec (n-k) := 
    match n,k with
    | O, O => fun (v : vec 0) => let v1 : vec (0-0) := tt in v1
    | O, S k' => fun (v : vec O) => let v1 : vec (0 - (S k')) := tt in v1
    | S n', O => fun (v : vec (S n')) => let v1 : vec (S n' - 0) := v in v1
    | S n', S k' => fun (v : vec (S n')) => let v1 : vec (S n' - S k') :=
      vskipn k' (snd v) in v1
    end.

End vskipn.

Arguments vskipn {T n}.


(** ** Maping a vector to another *)
Section vmap.

  Variable T : Type.
  Variable f : T -> T.

  Fixpoint vmap {n} : vec n -> vec n :=
    match n with
    | O => fun (v : vec 0) => tt
    | S n' => fun (v : vec (S n')) => (f (fst v), vmap (snd v))
    end.

End vmap.

Arguments vmap {T} f {n}.


Section vmap_props.  

  Variable T : Type.
  Variable f g : T -> T.
  Variable Hfg : forall x, f x = g x.
  
  Lemma vmap_eq : forall {n} (v : vec n), vmap f v = vmap g v.
  Proof.
    induction n; intros; simpl; auto. f_equal; auto.
  Qed. 
  
End vmap_props.


Section vmap_props2.  

  Variable T : Type.
  Variable fmul : T -> T -> T.
  Variable fmul_comm : forall a b, fmul a b = fmul b a.
  Variable fmul_assoc : forall a b c, fmul (fmul a b) c = fmul a (fmul b c).
  
  Lemma vmap_assoc1 : forall {n} a b m, 
    vmap (fun x : T => fmul a x) (@vmap T (fun x : T => fmul b x) n m) =
    vmap (fun x => fmul (fmul a b) x) m.
  Proof.
    induction n; intros; simpl; auto. f_equal; auto.
  Qed.
  
  Lemma vmap_assoc2 : forall {n} a b m, 
    vmap (fun x : T => fmul a x) (@vmap T (fun x : T => fmul b x) n m) =
    vmap (fun x : T => fmul b x) (@vmap T (fun x : T => fmul a x) n m).
  Proof.
    induction n; intros; simpl; auto. f_equal; auto.
    repeat rewrite <- fmul_assoc. f_equal. auto.
  Qed.
   
End vmap_props2.


(** Mapping two vectors to another vector *)
Section vmap2.

  Variable T : Type.
  Variable f : T -> T  -> T.
  Variable f_comm : forall a b, f a b = f b a.
  Variable f_assoc : forall a b c, f (f a b) c = f a (f b c).
  
  Fixpoint vmap2 {n} : vec n -> vec n -> vec n :=
    match n with
    | O => fun (v1 : vec 0) (v2 : vec 0) => tt
    | S n' => fun (v1 : vec (S n')) (v2 : vec (S n')) => 
      (f (fst v1) (fst v2), vmap2 (snd v1) (snd v2))
    end.
    
  Lemma vmap2_S : forall {n} t1 t2 (v1 v2 : vec n),
    vmap2 ((t1, v1):vec (S n)) (t2, v2) = (f t1 t2, vmap2 v1 v2).
  Proof. induction n; intros; destruct v1,v2; simpl; auto. Qed.
    
  Lemma vmap2_comm {n} (v1 v2 : vec n): vmap2 v1 v2 = vmap2 v2 v1.
  Proof.
    induction n; intros; destruct v1,v2; auto. simpl. f_equal; auto.
  Qed.

  Lemma vmap2_assoc {n} (v1 v2 v3 : vec n) :
    vmap2 (vmap2 v1 v2) v3 = vmap2 v1 (vmap2 v2 v3).
  Proof.
    induction n; intros; destruct v1,v2; auto. simpl. f_equal; auto.
  Qed.

End vmap2.

Arguments vmap2 {T} f {n}.


(** ** Vector addition *)
Section vadd.
  
  Variable T : Type.
  Variable T0 : T.
  Variable fadd : T -> T -> T.
  Variable fadd_comm : forall a b, fadd a b = fadd b a.
  Variable fadd_assoc : forall a b c, fadd (fadd a b) c = fadd a (fadd b c).
  Variable fadd_0_l : forall t, fadd T0 t = t.
  Variable fmul : T -> T -> T.
  Variable fmul_add_distr_l : forall a b1 b2,
    fmul a (fadd b1 b2) = fadd (fmul a b1) (fmul a b2).
  Variable fmul_add_distr_r : forall a1 a2 b,
    fmul (fadd a1 a2) b = fadd (fmul a1 b) (fmul a2 b).
  
  Definition vadd {n} (v1 v2 : vec n) : vec n := vmap2 fadd v1 v2.

  Lemma vadd_comm {n} (v1 v2 : vec n): vadd v1 v2 = vadd v2 v1.
  Proof. unfold vadd. apply vmap2_comm. auto. Qed.

  Lemma vadd_assoc {n} (v1 v2 v3 : vec n): 
    vadd (vadd v1 v2) v3 = vadd v1 (vadd v2 v3).
  Proof. unfold vadd. apply vmap2_assoc. auto. Qed.
  
  Lemma vadd_S : forall {n} t1 t2 (v1 v2 : vec n),
    vadd ((t1, v1) : vec (S n)) (t2, v2) = (fadd t1 t2, vadd v1 v2).
  Proof. intros. apply vmap2_S. Qed.
  
  Lemma vadd_0_l : forall {n} (v : vec n), vadd (vec0 T0 n) v = v.
  Proof.
    induction n; intros; destruct v;auto. rewrite vec0_S. rewrite vadd_S.
    f_equal. auto. auto.
  Qed.
  
  Lemma vadd_0_r : forall {n} (v : vec n), vadd v (vec0 T0 n) = v.
  Proof. intros. rewrite vadd_comm. apply vadd_0_l. Qed.

  Lemma vmap_vadd_distr_l : forall {n} a (v1 v2 : vec n), 
    vmap (fun x : T => fmul a x) (vadd v1 v2) =
    vadd (vmap (fun x : T => fmul a x) v1) (vmap (fun x : T => fmul a x) v2).
  Proof.
    induction n; intros; simpl; auto. f_equal; auto.
  Qed.
  
  Lemma vmap_vadd_distr_r : forall {n} a b (v : vec n), 
    vmap (fun x : T => fmul (fadd a b) x) v =
    vadd (vmap (fun x : T => fmul a x) v) (vmap (fun x : T => fmul b x) v).
  Proof.
    induction n; intros; simpl; auto. f_equal; auto.
  Qed.
  
End vadd.

Arguments vadd {T} fadd {n}.


(** ** Vector substraction *)
Section vsub.
  
  Variable T : Type.
  Variable T0 : T.
  Variable fopp : T -> T.
(*   Variable fadd fsub : T -> T -> T. *)
  Variable fadd : T -> T -> T.
  Infix "+" := fadd.
  Notation "- x" := (fopp x).
  Notation "a - b" := (a + (-b)). 
  
  Variable fopp_opp : forall a, - (- a) = a.
  Variable fadd_comm : forall a b, a + b = b + a.
  Variable fadd_assoc : forall a b c, (a + b) + c = a + (b + c).
  Variable fadd_0_l : forall t, T0 + t = t.
  Variable fadd_0_r : forall t, t + T0 = t.
  Variable fadd_opp : forall a, a + (-a) = T0.
  Variable fopp_add_dist : forall a b, -(a+b) = -a + -b.
  Variable fopp_0 : - T0 = T0.
  
  Definition vopp {n} (v : vec n) : vec n := vmap fopp v.
  
  Lemma vopp_S : forall {n} a (v : vec n), 
    vopp ((a, v) : vec (S n)) = (fopp a, vopp v).
  Proof.
    induction n; auto.
  Qed.
  
  Lemma vopp_vopp : forall {n} (v : vec n), vopp (vopp v) = v.
  Proof.
    induction n; intros; destruct v; simpl; auto. f_equal; auto.
  Qed.
  
  Definition vsub {n} (v1 v2 : vec n) : vec n := 
    vadd fadd v1 (vopp v2).
(*     vmap2 fsub v1 v2. *)
  
  Lemma vsub_comm : forall {n} (v1 v2 : vec n), vsub v1 v2 = vopp (vsub v2 v1).
  Proof.
    unfold vsub.
    induction n; intros; simpl; auto. f_equal; auto.
    rewrite fopp_add_dist. rewrite fopp_opp. auto.
  Qed.
  
  Lemma vsub_assoc {n} (v1 v2 v3 : vec n): 
    vsub (vsub v1 v2) v3 = vsub v1 (vadd fadd v2 v3).
  Proof.
    unfold vsub.
    induction n; intros; simpl; auto. f_equal; auto.
    rewrite fopp_add_dist. auto.
  Qed.
  
  Lemma vsub_S : forall {n} t1 t2 (v1 v2 : vec n),
    vsub ((t1, v1) : vec (S n)) (t2, v2) = (t1 - t2, vsub v1 v2).
  Proof. intros. apply vmap2_S. Qed.
  
  Lemma vsub_v0_l : forall {n} (v : vec n), vsub (vec0 T0 n) v = vopp v.
  Proof.
    induction n; intros; destruct v;auto. rewrite vec0_S. rewrite vsub_S.
    rewrite vopp_S. f_equal. auto. auto.
  Qed.
  
  Lemma vsub_v0_r : forall {n} (v : vec n), vsub v (vec0 T0 n) = v.
  Proof. 
    induction n; intros; destruct v; auto. rewrite vec0_S. rewrite vsub_S.
    f_equal. rewrite fopp_0. auto. auto.
  Qed.
  
  Lemma vsub_self : forall {n} (v : vec n), vsub v v = vec0 T0 n.
  Proof.
    unfold vsub.
    induction n; intros; destruct v; simpl; auto. f_equal; auto.
  Qed.
  
End vsub.

Arguments vopp {T} fopp {n}.
Arguments vsub {T} fopp fadd {n}.


(** ** Vector constant multiplication *)
Section vcmul_vmulc.
  
  Variable T : Type.
  Variable T0 T1 : T.
  Variable fmul : T -> T -> T.
  Variable fmul_comm : forall a b, fmul a b = fmul b a.
  Variable fmul_0_l : forall a, fmul T0 a = T0.
  Variable fmul_0_r : forall a, fmul a T0 = T0.
  Variable fmul_1_l : forall a, fmul T1 a = a.
  
  Definition vcmul {n} a v : vec n := vmap (fun x => fmul a x) v.
  Definition vmulc {n} v a : vec n := vmap (fun x => fmul x a) v.
  
  Lemma vcmul_eq_vmulc : forall {n} a (v : vec n), vcmul a v = vmulc v a.
  Proof.
    unfold vcmul,vmulc.
    induction n; intros; destruct v; simpl; auto. f_equal; auto.
  Qed.

  Lemma vcmul_S : forall {n} a b (v : vec n),
    vcmul a ((b,v):vec (S n)) = (fmul a b, vcmul a v).
  Proof. induction n; intros; destruct v; unfold vcmul; simpl; auto. Qed.

  Lemma vmulc_S : forall {n} a b (v : vec n),
    vmulc ((b,v):vec (S n)) a = (fmul b a, vmulc v a).
  Proof. induction n; intros; destruct v; unfold vcmul; simpl; auto. Qed.
  
  (** 0 * l = 0 *)
  Lemma vcmul_0_l : forall {n} (v : vec n), vcmul T0 v = vec0 T0 n.
  Proof.
    induction n; intros; simpl; auto. f_equal; auto.
  Qed.
  
  (** l * 0 = 0 *)
  Lemma vcmul_0_r : forall {n} a, vcmul a (vec0 T0 n) = vec0 T0 n.
  Proof.
    induction n; intros; simpl; auto. f_equal; auto.
  Qed.
  
  (** 1 * l = l *)
  Lemma vcmul_1_l : forall {n} (v : vec n), vcmul T1 v = v.
  Proof.
    induction n; intros; destruct v; simpl; auto. f_equal; auto.
  Qed.

End vcmul_vmulc.

Arguments vcmul {T} fmul {n}.
Arguments vmulc {T} fmul {n}.


(** ** Fold a vector to an element *)
Section vfold.

  Variable T : Type.
  
  Variable fadd : T -> T -> T.
  
  Fixpoint vfoldl {n} (init_val : T) : (vec n) -> T := 
    match n with
    | O => fun (v : vec 0) => init_val
    | S n' => fun (v : vec (S n')) => 
      fadd (fst v) (vfoldl init_val (snd v))
    end.
  

  (** Fold a vector to en element from right to left *)
  Fixpoint vfoldr {n} (init_val : T) : (vec n) -> T := 
    match n with
    | O => fun (v : vec 0) => init_val
    | S n' => fun (v : vec (S n')) => 
      fadd (vfoldr init_val (snd v)) (fst v)
    end.

End vfold.

Arguments vfoldl {T} fadd {n}.
Arguments vfoldr {T} fadd {n}.


(** ** Dot product of two vectors *)
Section vdot.

  Variable T : Type.
  Variable T0 : T.
  Variable fadd : T -> T -> T.
  Variable fmul : T -> T -> T.
  Variable fadd_comm : forall a b, fadd a b = fadd b a.
  Variable fmul_comm : forall a b, fmul a b = fmul b a.
  Variable fmul_0_l : forall a, fmul T0 a = T0.
  Variable fadd_0_r : forall t, fadd t T0 = t.
  Variable fmul_fadd_dist_l : forall a b c, 
    fmul a (fadd b c) = fadd (fmul a b) (fmul a c).
  Variable fadd_assoc: forall a b c, fadd a (fadd b c) = fadd (fadd a b) c.
  Variable fmul_assoc: forall a b c, fmul a (fmul b c) = fmul (fmul a b) c.

  Definition vdot {n} (v1 v2 : vec n) := vfoldl fadd T0 (vmap2 fmul v1 v2).
  
  Lemma vdot_S : forall {n} (a b : T) (v1 v2 : vec n),
      vdot ((a,v1):vec (S n)) (b,v2) = fadd (fmul a b) (vdot v1 v2).
  Proof. induction n; intros; auto. Qed.
  
  Lemma vdot_comm {n} (v1 v2 : vec n) : vdot v1 v2 = vdot v2 v1.
  Proof. unfold vdot. f_equal. apply vmap2_comm. intros; auto. Qed.
  
  Lemma vdot_tt (v : vec 0) : vdot v v = T0.
  Proof. unfold vdot. simpl. auto. Qed.
  
  Lemma vdot_0_l : forall {n} (v : vec n), vdot (vec0 T0 n) v = T0.
  Proof. 
    induction n; intros; destruct v; simpl. apply vdot_tt.
    rewrite vdot_S. rewrite IHn. rewrite fmul_0_l. auto.
  Qed.
  
  Lemma vdot_0_r : forall {n} (v : vec n), vdot v (vec0 T0 n) = T0.
  Proof.
    intros. rewrite vdot_comm. apply vdot_0_l.
  Qed.
  
  Lemma vdot_vcmul_l : forall {n} a (v1 v2 : vec n),
    vdot (vcmul fmul a v1) v2 = fmul a (vdot v1 v2).
  Proof.
    induction n; intros; destruct v1,v2; simpl.
    - repeat rewrite vdot_tt. rewrite fmul_comm. auto.
    - repeat rewrite vdot_S. rewrite IHn.
      remember (vdot v v0). rewrite fmul_fadd_dist_l. f_equal. auto.
  Qed.
  
  Lemma vdot_vcmul_r : forall {n} a (v1 v2 : vec n),
    vdot v1 (vcmul fmul a v2) = fmul a (vdot v1 v2).
  Proof. 
    intros. rewrite vdot_comm. rewrite vdot_vcmul_l. f_equal.
    apply vdot_comm.
  Qed.
  
  Lemma vdot_vmulc_l : forall {n} a (v1 v2 : vec n),
    vdot (vmulc fmul v1 a) v2 = fmul a (vdot v1 v2).
  Proof. intros. rewrite <- vcmul_eq_vmulc; auto. apply vdot_vcmul_l. Qed.
  
  Lemma vdot_vmulc_r : forall {n} a (v1 v2 : vec n),
    vdot v1 (vmulc fmul v2 a) = fmul a (vdot v1 v2).
  Proof. intros. rewrite <- vcmul_eq_vmulc; auto. apply vdot_vcmul_r. Qed.
  
  Lemma vdot_vadd_l : forall {n} (v1 v2 v3 : vec n),
    vdot v1 (vadd fadd v2 v3) = fadd (vdot v1 v2) (vdot v1 v3).
  Proof. 
    induction n; intros; destruct v1,v2,v3; simpl.
    - repeat rewrite vdot_tt. auto.
    - repeat rewrite ?vdot_S, ?vadd_S. rewrite IHn.
      remember (vdot v v0). remember (vdot v v1).
      rewrite fmul_fadd_dist_l.
      repeat rewrite fadd_assoc. f_equal.
      remember (fmul t t0). remember (fmul t t1).
      repeat rewrite <- fadd_assoc. f_equal.
      apply fadd_comm.
  Qed.

  Lemma vdot_vadd_r : forall {n} (v1 v2 v3 : vec n),
    vdot (vadd fadd v1 v2) v3 = fadd (vdot v1 v3) (vdot v2 v3).
  Proof. 
    intros. rewrite vdot_comm. rewrite vdot_vadd_l. 
    f_equal; apply vdot_comm.
  Qed.
  
End vdot.

Arguments vdot {T} T0 fadd fmul {n}.


(** ** Concatenation a nested vector to a plain vector *)
Section vvflat.

  Variable T : Type.
  
  Fixpoint vvflat {r c} : (@vec (@vec T c) r) -> @vec T (r * c) :=
    match r with
    | O => fun (m : @vec (vec c) 0) => tt
    | S r' => fun (m : @vec (vec c) (S r')) =>
      vapp (fst m) (vvflat (snd m))
    end.

End vvflat.

Arguments vvflat {T r c}.


(** vector to list *)
Section v2l.
  Variable A : Type.
  Variable A0 : A.
  
  Fixpoint v2l {n} : @vec A n -> list A :=
    match n with
    | 0 => fun (v : @vec A 0) => nil
    | S n' => fun (v : @vec A (S n')) => cons (fst v) (v2l (snd v))
    end.
  
  Lemma v2l_length : forall n (v : @vec A n), length (v2l v) = n.
  Proof.
    induction n; intros; destruct v; simpl; auto.
  Qed.
  
  Fixpoint l2v (l : list A) (n : nat) {struct n} : vec n :=
    match n as n0 return (vec n0) with
    | 0 => tt
    | S n' => (hd A0 l, l2v (tl l) n')
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
    intros. induction n; destruct v; simpl; auto. rewrite IHn. auto.
  Qed.
    
End v2l.

Arguments v2l {A n}.
Arguments l2v {A}.

(* Check ([1;2;3] : vec 3).
Compute v2l ([1;2;3] : vec 3).
Compute l2v 0 (cons 1 (cons 2 nil)) 2. *)


(** ** Linear Space. These code is for test *)
Section LinearSpace.
  
  (** definition of Linear Space:
  V ~~ vec
  P ~~ T
  + ~~ vadd
  . ~~ vcmul/vmulc
  *)
  
  (* dimension *)
  Variable n : nat.
  
  (* P *)
  Variable T : Type.
  Variable T0 : T.
  Variable T1 : T.
  Variable Topp : T -> T.
  Variable Tadd Tmul : T -> T -> T.
  
  Declare Scope T_scope.
  Delimit Scope T_scope with t.
  Open Scope T_scope.
  Notation "- t" := (Topp t) : T_scope.
  Infix "+" := Tadd : T_scope.
  Infix "*" := Tmul : T_scope.
  
  (** 这里有很多有趣的性质，等待去证明。
   平时我们用的都是直觉或特例，但是抽象的类型需要证明。
   研究课题：代数系统、群、环、域，等这些内容。
   研究目标：彻底弄懂这些定义。到底哪个是因，哪个是果 *)
  Variable Tadd_comm : forall a b, a + b = b + a.
  Variable Tadd_assoc : forall a b c, (a + b) + c = a + (b + c).
  Variable Tadd_0_l : forall a, T0 + a = a.
  Variable Tadd_opp : forall a, a + (-a) = T0.
  Variable Tadd_elim_l : forall a b c, a + b = a + c -> b = c.
  Variable Tadd_elim_2 : forall a b, a + b = a -> b = T0.
  Variable Tadd_elim_3 : forall a b, a + b = T0 -> a = -b.
  Variable Tadd_elim_4 : forall a b, a = -b <-> -a = b.
  Variable Tmul_1_l : forall t, T1 * t = t.
  Variable Tmul_comm : forall a b, a * b = b * a.
  Variable Tmul_assoc : forall a b c, (a * b) * c = a * (b * c).
  Variable Tmul_Tadd_dist_r : forall a b c, (a + b) * c = a * c + b * c.
  
  (* V *)
  Definition V := @vec T n.
  Definition V0 := @vec0 T T0 n.
  Definition Vadd := @vadd T Tadd n.
  Definition Vcmul := @vcmul T Tmul n.
  Definition Vmulc := @vmulc T Tmul n.

  Declare Scope V_scope.
  Delimit Scope V_scope with v.
  Open Scope V_scope.
  Notation "v1 + v2" := (Vadd v1 v2)  
    : V_scope.
  Notation "a c* v" := (Vcmul a v) : V_scope.
  Notation "v *c a" := (Vmulc v a) : V_scope.
  
  (* (1), v1 + v2 = v2 + v1 *)
  Lemma Vadd_comm : forall (v1 v2 : V), v1 + v2 = v2 + v1.
  Proof. intros. apply vadd_comm. auto. Qed.
  
  (* (2), (v1 + v2) + v3 = v1 + (v2 + v3) *)
  Lemma Vadd_assoc : forall (v1 v2 v3 : V), (v1 + v2) + v3 = v1 + (v2 + v3).
  Proof. intros. apply vmap2_assoc. auto. Qed.
  
  (* (3), v + 0 = v *)
  Lemma Vadd_0_r : forall (v : V), v + V0 = v.
  Proof. intros. apply vadd_0_r; auto. Qed.
  
  (* (4), ∀α∈V (∃β (α + β = 0)) *)
  Lemma Vopp_exist : forall (v1 : V), {v2 | v1 + v2 = V0}.
  Proof.
    unfold V,V0,Vadd in *. induction n; intros; destruct v1; simpl.
    - exists tt. auto.
    - exists (-t, vmap Topp v). f_equal; simpl; auto.
      destruct (IHn0 v). clear IHn0 e x.
      induction n0; destruct v; simpl; auto. f_equal; auto.
  Qed.
  
  (* (5) 1 . v = v *)
  Lemma Vcmul_1_l : forall (v : V), T1 c* v = v.
  Proof.
    unfold V, Vcmul. intros. induction n; destruct v; simpl; auto.
    f_equal; auto.
  Qed.
  
  (* (6) k . (m . v) = (km) . v *)
  Lemma Vcmul_assoc : forall (k m : T) (v : V), 
    k c* (m c* v) = (k*m) c* v.
  Proof.
    unfold V, Vcmul. intros. induction n; destruct v; simpl; auto.
    f_equal; auto.
  Qed.
  
  (* (7) (k + m) . v = k.v + m.v *)
  Lemma Vcmul_dist_c : forall (k m : T) (v : V),
    (k + m)%t c* v = (k c* v) + (m c* v).
  Proof.
    unfold V,Vadd,Vcmul. intros. induction n; destruct v; simpl; auto.
    f_equal; auto.
  Qed.
  
  (* (8) k . (v1 + v2) = k.v1 + k.v2 *)
  Lemma Vcmul_dist_v : forall (k : T) (v1 v2 : V),
    k c* (v1 + v2) = (k c* v1) + (k c* v2).
  Proof.
    unfold V,Vadd,Vcmul. intros. induction n; destruct v1,v2; simpl; auto.
    f_equal; auto. rewrite Tmul_comm. rewrite Tmul_Tadd_dist_r. f_equal; auto.
  Qed.
  
End LinearSpace.
