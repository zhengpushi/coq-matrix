(*
  purpose   : Extension for general list
  author    : ZhengPu Shi
  date      : 2021.12
  
  remark    :
  1. reference "A Gentle Introduction to Type Classes and Relations in Coq"
  
  history   :
  1. 2021.12, by Zhengpu Shi.
    first version

  2. 2022.05, by Zhengpu Shi.
    split big file into small modules
*)

Require Export BasicConfig.
Require Export NatExt.

Require Export List.
        Export ListNotations.

Require Export FunctionalExtensionality.
Require Export Lia.

Open Scope nat_scope.


(** Redefine 'length_zero_iff_nil', original is opaque, we transparent it *)
Lemma length_zero_iff_nil
     : forall (A : Type) (l : list A), length l = 0 <-> l = [].
Proof.
  intros. destruct l; intros; split; intros; try reflexivity;
  simpl in *; discriminate.
Defined.


(* ======================================================================= *)
(** ** Properties of cons *)

(** Equality of cons, iff both parts are equal *)
Lemma cons_eq_iff {A} : forall (a1 a2 : A) (l1 l2 : list A),
  a1 :: l1 = a2 :: l2 <-> a1 = a2 /\ l1 = l2.
Proof. intros. split; intros H; inversion H; subst; auto. Qed.

(** Inequality of cons, iff at least one parts are not equal *)
Lemma cons_neq_iff {A} (Aeqdec : forall a b : A, {a = b} + {a <> b}) 
  : forall (a1 a2 : A) (l1 l2 : list A),
  (a1 :: l1 <> a2 :: l2) <-> ((a1 <> a2) \/ (l1 <> l2)).
Proof.
  intros. split; intros H.
  - destruct (Aeqdec a1 a2), (list_eq_dec Aeqdec l1 l2); auto.
    subst; auto.
  - intro H1; inversion H1. subst; auto. destruct H; auto.
Qed.


(* ======================================================================= *)
(** ** Properties of hd and tl *)

(** pred version *)
Lemma tl_length {A} : forall (l : list A), length (tl l) = pred (length l).
Proof. induction l; auto. Qed.


(* ======================================================================= *)
(** ** Properties of nth *)
  
(** nth [] a = a *)
Lemma nth_nil {A} : forall (a : A) (i : nat), nth i [] a = a.
Proof.
  intros. destruct i; auto.
Qed.

(** Two list equal iff all nth visit equal *)
Lemma list_eq_iff_nth {A} (A0 : A) : forall n (l1 l2 : list A)
  (H1 : length l1 = n) (H2 : length l2 = n),
  l1 = l2 <-> (forall (i : nat), i < n -> nth i l1 A0 = nth i l2 A0).
Proof.
  intros; split; intros.
  - subst; auto.
  - apply nth_ext with (d := A0) (d' := A0).
    + subst; auto.
    + intros. apply H. subst; auto.
Qed.

(** Get from repeat x and default value x always return x *)
Lemma nth_repeat_same {A} : forall (a : A) (n i : nat),
  nth i (repeat a n) a = a.
Proof.
  intros a n. induction n; auto.
  - destruct i; auto.
  - destruct i; auto. simpl. auto.
Qed.


(* ======================================================================= *)
(** ** Set element with a constant value *)
  
Fixpoint lst_chg {A} (l : list A) (i : nat) (x : A) : list A :=
  match l, i with
  | [], _ => []
  | a :: l, 0 => x :: l
  | a :: l, S i => a :: (lst_chg l i x)
  end.

(** Height property *)
Lemma lst_chg_height {A} : forall (l : list A) ni n x, 
  length l = n ->
  length (lst_chg l ni x) = n.
Proof.
  intros l; induction l; auto. induction ni; auto; simpl; intros.
  destruct n; auto. easy.
Qed.


(* ======================================================================= *)
(** ** Set element with a generation function *)

(** Inner version. i0 is given position, i is changing every loop *)
Fixpoint lst_chgf_aux {A} (l : list A) (i0 i : nat) (f : nat -> A) 
  : list A :=
  match l, i with
  | [], _ => []
  | a :: l, 0 => f i0 :: l
  | a :: l, S i => a :: (lst_chgf_aux l i0 i f)
  end.

(** User version that hide i0 parameter *)
Definition lst_chgf {A} (l : list A) (i : nat) (f : nat -> A) : list A :=
  lst_chgf_aux l i i f.

(* Let f_gen := fun (i : nat) => (i + 5).
Compute lst_chgf [1;2;3] 0 f_gen.
Compute lst_chgf [1;2;3] 1 f_gen.
 *)
 
(** Height property *)
Lemma lst_chgf_aux_height {A} : forall (l : list A) ni n ni0 f, 
  length l = n ->
  length (lst_chgf_aux l ni0 ni f) = n.
Proof.
  intros l; induction l; auto. destruct ni; auto; simpl; intros.
  destruct n; auto. easy.
Qed.

Lemma lst_chgf_height {A} : forall (l : list A) n ni f, 
  length l = n ->
  length (lst_chgf l ni f) = n.
Proof.
  intros. apply lst_chgf_aux_height; auto.
Qed.


(* ======================================================================= *)
(** ** Properties of length *)
(* Section length_props. *)

(** decompose a list which length is 1 *)

(** Note that, we need this lemma to split a list with only one element,
  although the definition end with "Defined", we cannot got a explicit 
  result by Compute. In practice, won't use this lemma if you needn't *)
Lemma list_length_1 {A} : forall (l : list A),
  length l = 1 -> {x | l = [x]}.
Proof. 
  destruct l; intros. inversion H. inversion H.
  apply length_zero_iff_nil in H1; subst. exists a. auto.
Defined.

Section Test.
  Let l := [1].
  Definition h : length l = 1. auto. Defined.
(*   Compute proj2_sig (list_length_1 l h). *)
End Test.

(** a list has only one element equal to [hd _ l] *)
Lemma list_length1_eq_hd : forall {A} (x : A) (l:list A), 
  length l = 1 -> [hd x l] = l.
Proof.
  intros A x l. destruct l.
  - intros. simpl in *. lia.
  - intros. simpl in *. f_equal.
    apply eq_add_S in H. apply length_zero_iff_nil in H. auto.
Qed.

(** decompose a list which length is S n *)
Lemma list_length_Sn : forall {A} (l : list A) n,
  length l = S n -> {x & { t | l = x :: t}}.
Proof. destruct l; intros. inversion H. exists a. exists l. auto. Qed.

(** decompose a list which length is S (S n) *)
Lemma list_length_SSn : forall {A} (l : list A) n,
  length l = S (S n) -> {x & { y & { t | l = x :: y :: t}}}.
Proof.
  destruct l; intros. inversion H.
  exists a. destruct l. inversion H.
  exists a0. exists l. auto.
Qed.

(** Split list which length is 1 *)
Lemma list_length1_neq :  forall A (l : list A) (a b : A), 
  (length (a :: l) = 1 /\ (a :: l) <> [b]) -> (a <> b /\ l = []).
Proof.
  intros A l. induction l; intros; destruct H.
  - simpl in *. split; auto. intro H1. subst. easy.
  - simpl in *. easy.
Qed.


(* ======================================================================= *)
(** ** Customized list induction *)

(** Connect induction principle between nat and list *)
Lemma ind_nat_list {A} : forall (P : list A -> Prop) ,
  (forall n l, length l = n -> P l) -> (forall l, P l).
Proof.
  intros. apply (H (length l)). auto.
Qed.

(** Two step induction principle for list *)
Theorem list_ind2 : forall {A : Type} (P : list A -> Prop),
  (P []) -> 
  (forall a, P [a]) -> 
  (forall l a b, P l -> P (a :: b :: l)) ->
  (forall l, P l).
Proof.
  intros A P H0 H1 H2. apply ind_nat_list. induction n using nat_ind2. 
  - intros. apply length_zero_iff_nil in H; subst; auto.
  - intros. apply list_length_1 in H. destruct H. subst; auto.
  - destruct l; auto. destruct l; auto.
    intros. apply H2. apply IHn. simpl in H.
    repeat apply eq_add_S in H. auto.
Qed.


(* ======================================================================= *)
(** ** list repeat properties *)

(** repeat S n times equal to another form *)
Lemma list_repeat_Sn {A} (A0 : A) : forall n, repeat A0 (S n) = A0 :: repeat A0 n.
Proof. intros. auto. Qed.


(* ======================================================================= *)
(** ** Zero list *)

(** A friendly name for zero list *)
Definition lzero {A} (A0 : A) n := repeat A0 n.

(** lzero's length law *)
Lemma lzero_length {A} (A0 : A) : forall n, length (lzero A0 n) = n.
Proof. intros. apply repeat_length. Qed.

(** append two zero list to a zero list satisfy length relation *)
Lemma lzero_app {A} (A0 : A) : forall n1 n2,
  lzero A0 n1 ++ lzero A0 n2 = lzero A0 (n1 + n2).
Proof. unfold lzero. intros. rewrite repeat_app. auto. Qed.

(** lzero equal to map to_zero *)
Lemma lzero_eq_map_to_zero {A} (A0 : A) : forall {n} l (H1 : length l = n),
  lzero A0 n = map (fun x : A => A0) l.
Proof.
  induction n; intros.
  - apply length_zero_iff_nil in H1. subst; auto.
  - destruct l. discriminate. simpl. rewrite <- IHn; auto.
Qed.


(* ======================================================================= *)
(** ** Properties of map *)

(** map and repeat is communtative *)
Lemma map_repeat {A B} (f : A -> B) : forall (a : A) n, 
  map f (repeat a n) = repeat (f a) n.
Proof. 
  induction n; simpl; auto. f_equal; auto.
Qed.

(** Mapping is fixpoint, iff f is id *)
Lemma map_fixpoint_imply_id {A} (f : A -> A) : forall (l : list A), 
    map f l = l -> (forall x, In x l -> f x = x).
Proof.
  induction l; intros; simpl in *. easy. inversion H.
  destruct H0. subst; auto. apply IHl; auto.
Qed.


(* ======================================================================= *)
(** ** map two lists to a list *)
Section map2.

  Variable A B C : Type.
  Variable f : A -> B -> C.

  (** map operation to two list *)
  Fixpoint map2 (l1 : list A) (l2 : list B) : list C :=
    match l1, l2 with
    | x1 :: t1, x2 :: t2 => (f x1 x2) :: (map2 t1 t2)
    | _, _ => []
    end.
  
  (** length of map2 *)
  Lemma map2_length : forall (l1 : list A) (l2 : list B) n,
    length l1 = n -> length l2 = n -> length (map2 l1 l2) = n.
  Proof. 
    induction l1,l2; simpl; auto. intros. destruct n; simpl; auto. easy.
  Qed.
  
  (** map2 to two lists could be separated by two segments with same length *)
  Lemma map2_app : forall (la1 la2 : list A) (lb1 lb2 : list B),
    length la1 = length lb1 -> length la2 = length lb2 ->
    map2 (la1 ++ la2) (lb1 ++ lb2) = (map2 la1 lb1) ++ (map2 la2 lb2).
  Proof.
    induction la1, lb1; intros; simpl; auto; simpl in H; try easy.
    f_equal. apply IHla1; auto.
  Qed.
  
  (** map2 [] l = [] *)
  Lemma map2_nil_l : forall l, map2 [] l = [].
  Proof.
    destruct l; auto.
  Qed.

  (** map2 l [] = [] *)
  Lemma map2_nil_r : forall l, map2 l [] = [].
  Proof.
    destruct l; auto.
  Qed.
  
End map2.

Arguments map2 {A B C}.


(* ======================================================================= *)
(** ** map2 on dlist *)

Section map2_dlist.

  Variable A B C : Type.
  Variable f : A -> B -> C.
  
  (** tail of map2 to dlist, equal to map2 to tail part of original dlists *)
  Lemma tail_map2_dlist : forall dl1 dl2,
    tl (map2 (map2 f) dl1 dl2) =
    map2 (map2 f) (tl dl1) (tl dl2).
  Proof.
    destruct dl1, dl2; simpl; auto. rewrite map2_nil_r. auto.
  Qed.

End map2_dlist.


(* ======================================================================= *)
(** ** map2 properties with same base type *)
Section map2_sametype.
  
  Variable A : Type.
  Variable f : A -> A -> A.
  Variable f_comm : forall a b, f a b = f b a.
  Variable f_assoc : forall a b c, f (f a b) c = f a (f b c).
  
  (** l1 . l2 = l2 . l1 *)
  Lemma map2_comm : forall (l1 l2 : list A),
    map2 f l1 l2 = map2 f l2 l1.
  Proof. induction l1,l2; simpl; auto. rewrite IHl1. f_equal. auto. Qed.
  
  (** (l1 . l2) . l3 = l1 . (l2 . l3) *)
  Lemma map2_assoc : forall (l1 l2 l3 : list A),
    map2 f (map2 f l1 l2) l3 = map2 f l1 (map2 f l2 l3).
  Proof. induction l1,l2,l3; simpl; auto. rewrite IHl1. f_equal. auto. Qed.
  
  (** map2 with map of two components *)
  Lemma map2_map_map : forall (f1 f2 g : A -> A) (h : A -> A -> A) 
    (H : forall x, g x = h (f1 x) (f2 x)) l,
    map2 h (map f1 l) (map f2 l) = map g l.
  Proof. induction l; simpl; auto. rewrite IHl. f_equal. auto. Qed.
  
  (** map2 over map is homorphism *)
  Lemma map2_map_hom : forall (f : A -> A) (g : A -> A -> A) 
    (H : forall x1 x2, f (g x1 x2) = g (f x1) (f x2)) l1 l2,
    map2 g (map f l1) (map f l2) = map f (map2 g l1 l2).
  Proof. induction l1,l2; auto. simpl. rewrite IHl1. f_equal. auto. Qed.

  (** nth (map2 f l1 l2) i = f (nth l1 i) (nth l2 i) *)
  Lemma map2_nth : forall i (a : A) l1 l2,
    i < length l1 -> i < length l2 ->
    nth i (map2 f l1 l2) a = f (nth i l1 a) (nth i l2 a).
  Proof.
    intros i a l1.
    generalize dependent a.
    generalize dependent i.
    induction l1; intros.
    - simpl in *. lia.
    - induction l2 eqn : E2; intros.
      + simpl in *. lia.
      + simpl map2.
        induction i.
        * simpl. auto.
        * simpl. apply IHl1.
          ** clear IHl1 IHl IHi. simpl in *. lia.
          ** clear IHl1 IHl IHi. simpl in *. lia.
  Qed.
  
End map2_sametype.


(* ======================================================================= *)
(** ** map2 is considered as ladd *)
Section ladd.

  Variable A : Type.
  Variable A0 : A.
  Variable add : A -> A -> A.
  Variable add_comm : forall a b, add a b = add b a.
  Variable add_0_l : forall a, add A0 a = a.
  
  (** l1 + l2 *)
  Definition ladd (l1 l2 : list A) : list A := map2 add l1 l2.
  
  (** l1 + l2 = l2 + l1 *)
  Lemma ladd_comm : forall l1 l2, ladd l1 l2 = ladd l2 l1.
  Proof. apply map2_comm; auto. Qed.
  
  (** [] + l = [] *)
  Lemma ladd_nil_l : forall l, ladd l [] = [].
  Proof. induction l; auto. Qed.
  
  (** l + [] = [] *)
  Lemma ladd_nil_r : forall l, ladd [] l = [].
  Proof. auto. Qed.
  
  (** 0 + l = l *)
  Lemma ladd_zero_l : forall l n, 
    length l = n -> ladd (lzero A0 n) l = l.
  Proof.
    induction l; simpl; intros. apply map2_nil_r.
    induction n ; simpl. inversion H. f_equal; auto.
  Qed.
  
  (** l + 0 = l *)
  Lemma ladd_zero_r : forall l n, 
    length l = n -> ladd l (lzero A0 n) = l.
  Proof.
    intros. unfold ladd. rewrite map2_comm; auto.
    apply ladd_zero_l; auto.
  Qed.
  
End ladd.

Arguments ladd {A}.


(* ======================================================================= *)
(** ** list sub, list opp *)
Section lsub_lopp.
  
  Variable A : Type.
  Variable A0 : A.
  Variable add : A -> A -> A.
  Variable opp : A -> A.
  Variable sub : A -> A -> A.
  Variable sub_comm : forall a b, sub a b = opp (sub b a).
  Variable sub_assoc1 : forall a b c, sub (sub a b) c = sub a (sub c b).
  Variable sub_assoc2 : forall a b c, sub (sub a b) c = sub a (add b c).
  Variable sub_0_l : forall a, sub A0 a = opp a.
  Variable sub_0_r : forall a, sub a A0 = a.
  Variable sub_self : forall a, sub a a = A0.
  
  (** - l *)
  Definition lopp (l : list A) : list A := map opp l.
  
  (** l1 - l2 *)
  Definition lsub (l1 l2 : list A) : list A := map2 sub l1 l2.
  
  (** l1 - l2 = - (l2 - l1) *)
  Lemma lsub_comm : forall (l1 l2 : list A),
    lsub l1 l2 = map opp (lsub l2 l1).
  Proof. induction l1,l2; simpl; auto. rewrite IHl1. f_equal. auto. Qed.
  
  (** (l1 - l2) - l3 = (l1 - l3) - l2 *)
  Lemma lsub_assoc1 : forall (l1 l2 l3 : list A),
    lsub (lsub l1 l2) l3 = lsub l1 (lsub l3 l2).
  Proof. induction l1,l2,l3; simpl; auto. rewrite IHl1. f_equal. auto. Qed.
  
  (** (l1 - l2) - l3 = l1 - (l2 + l3) *)
  Lemma lsub_assoc2 : forall (l1 l2 l3 : list A),
    lsub (lsub l1 l2) l3 = lsub l1 (map2 add l2 l3).
  Proof. induction l1,l2,l3; simpl; auto. rewrite IHl1. f_equal. auto. Qed.
  
  (** 0 - l = - l *)
  Lemma lsub_zero_l : forall l n, 
    length l = n -> lsub (lzero A0 n) l = map opp l.
  Proof.
    induction l; simpl; intros. apply map2_nil_r.
    induction n ; simpl. inversion H. f_equal; auto.
  Qed.
  
  (** l - 0 = l *)
  Lemma lsub_zero_r : forall l n, 
    length l = n -> lsub l (lzero A0 n) = l.
  Proof.
    induction l; simpl; intros; auto. destruct n; simpl. inversion H.
    f_equal; auto.
  Qed.
  
  (** l - l = 0 *)
  Lemma lsub_self : forall l n, 
    length l = n -> lsub l l = (lzero A0 n).
  Proof.
    induction l; simpl; intros; subst; auto. simpl. f_equal; auto.
  Qed.
  
End lsub_lopp.

Arguments lopp {A}.
Arguments lsub {A}.


(* ======================================================================= *)
(** ** constant multiplication of list *)
Section lcmul_lmulc.
  
  Variable A : Type.
  Variable A0 A1 : A.
  Variable mul : A -> A -> A.
  Infix "*" := mul.
  Variable mul_comm : forall a b, a * b = b * a.
  Variable mul_0_l : forall a, A0 * a = A0.
  Variable Aeqdec : forall a1 a2 : A, {a1 = a2} + {a1 <> a2}.
  Variable mul_1_l : forall a : A, A1 * a = a.
  Variable mul_cancel_r : forall r1 r2 r : A, 
      r <> A0 -> r1 * r = r2 * r -> r1 = r2. 
  
  (** a * l *)
  Definition lcmul (a : A) (l : list A) : list A := map (fun x => a * x) l.
  
  (** l * a *)
  Definition lmulc (l : list A) (a : A) : list A := map (fun x => x * a) l.
  
  (** cmul keep its length *)
  Lemma lcmul_length : forall a l n, length l = n -> 
    length (lcmul a l) = n.
  Proof. intros. unfold lcmul. rewrite map_length; auto. Qed.
  
  (** a * l = l * a *)
  Lemma lmulc_lcmul : forall a l,
    lmulc l a = lcmul a l.
  Proof. induction l; auto. simpl. f_equal; auto. Qed.
  
  (** a * [] = [] *)
  Lemma lcmul_nil : forall a, lcmul a [] = [].
  Proof. intros. auto. Qed.
  
  (** [] * a = [] *)
  Lemma lmulc_nil : forall a, lmulc [] a = [].
  Proof. intros. auto. Qed.
  
  (** mul k x = x -> k = 1 \/ x = 0 *)
  Lemma fcmul_fixpoint_imply_k1_or_zero :
    forall (k x : A), mul k x = x -> k = A1 \/ x = A0.
  Proof.
    intros. destruct (Aeqdec x A0). auto. left.
    rewrite <- mul_1_l in H.
    apply (mul_cancel_r k A1 x n H).
  Qed.
  
  (** mul x k = x -> k = 1 \/ x = 0 *)
  Lemma fmulc_fixpoint_imply_k1_or_zero :
    forall (k x : A), mul x k = x -> k = A1 \/ x = A0.
  Proof.
    intros. rewrite mul_comm in H.
    apply fcmul_fixpoint_imply_k1_or_zero; auto.
  Qed.
  
  (** lcmul is fixpoint, iff k1 or lzero *)
  Lemma lcmul_fixpoint_imply_k1_or_lzero : 
    forall {n} (l : list A) (Hl : length l = n) (k : A),
      lcmul k l = l -> (k = A1 \/ l = lzero A0 n).
  Proof.
    intros n l. gd n. induction l; intros. subst; auto.
    destruct n. easy. simpl in *. inversion H. inversion Hl.
    apply fcmul_fixpoint_imply_k1_or_zero in H1.
    destruct (Aeqdec k A1).
    - left; auto.
    - assert (a = A0). { destruct H1. easy. auto. }
      right. f_equal.
      + subst. rewrite mul_comm; auto.
      + rewrite H2,H3. destruct (IHl n H3 k); auto. easy.
  Qed.
  
  (** lmulc is fixpoint, iff k1 or lzero *)
  Lemma lmulc_fixpoint_imply_k1_or_lzero : 
    forall {n} (l : list A) (Hl : length l = n) (k : A),
      lmulc l k = l -> (k = A1 \/ l = lzero A0 n).
  Proof.
    intros n l. gd n. induction l; intros. subst; auto.
    destruct n. easy. simpl in *. inversion H. inversion Hl.
    apply fmulc_fixpoint_imply_k1_or_zero in H1.
    destruct (Aeqdec k A1).
    - left; auto.
    - assert (a = A0). { destruct H1. easy. auto. }
      right. f_equal.
      + subst. auto.
      + rewrite H2,H3. destruct (IHl n H3 k); auto. easy.
  Qed.
  
End lcmul_lmulc.

Arguments lcmul {A}.
Arguments lmulc {A}.



(* ======================================================================= *)
(** ** product of two lists *)
Section ldot.
  
  Variable A : Type.
  Variable A0 : A.
  Variable add mul : A -> A -> A.
  Infix "+" := add.
  Infix "*" := mul.
  Variable add_comm : forall a b, a + b = b + a.
  Variable add_assoc : forall a b c, (a + b) + c = a + (b + c).
  Variable mul_assoc : forall a b c, (a * b) * c = a * (b * c).
  Variable mul_comm : forall a b, a * b = b * a.
  Variable mul_add_distr_l : forall a b1 b2, a * (b1 + b2) = a * b1 + a * b2.
  Variable mul_add_distr_r : forall a1 a2 b, (a1 + a2) * b = a1 * b + a2 * b.
  Variable add_0_l : forall a, A0 + a = a.
  Variable mul_0_l : forall a, A0 * a = A0.
  
  (** dot product, marked as l1 . l2 *)
  Definition ldot (l1 l2 : list A) : A :=
    fold_right add A0 (map2 mul l1 l2).
  
  (** l1 . l2 = l2 . l1 *)
  Lemma ldot_comm : forall (l1 l2 : list A),
    ldot l1 l2 = ldot l2 l1.
  Proof. intros. unfold ldot. f_equal. apply map2_comm. auto. Qed.
  
  (** [] . l = 0 *)
  Lemma ldot_nil_l : forall (l : list A), ldot nil l = A0.
  Proof. intros. destruct l; simpl; auto. Qed.
  
  (** l . [] = 0 *)
  Lemma ldot_nil_r : forall (l : list A), ldot l nil = A0.
  Proof. intros. destruct l; simpl; auto. Qed.

  (** ldot cons *)
  Lemma ldot_cons : forall l1 l2 x1 x2,
    ldot (x1 :: l1) (x2 :: l2) = add (mul x1 x2) (ldot l1 l2).
  Proof. induction l1,l2; simpl; intros; auto. Qed.
  
  (** lzero . l = 0 *)
  Lemma ldot_zero_l : forall l n, ldot (lzero A0 n) l = A0.
  Proof.
    induction l,n; simpl; intros; auto. rewrite ldot_cons.
    rewrite IHl. rewrite add_comm, add_0_l, mul_0_l. auto.
  Qed.
  
  (** l . lzero = 0 *)
  Lemma ldot_zero_r : forall l n, ldot l (lzero A0 n) = A0.
  Proof. intros. rewrite ldot_comm. apply ldot_zero_l. Qed.
  
  (** ldot left distributive over ladd.
    l1 . (l2 + l3) = l1.l2 + l1.l3 *)
  Lemma ldot_ladd_distr_l : forall l1 l2 l3 r,
    length l1 = r -> length l2 = r -> length l3 = r ->
    ldot l1 (ladd add l2 l3) = add (ldot l1 l2) (ldot l1 l3).
  Proof.
    induction l1,l2,l3; simpl; intros; subst; auto; try discriminate.
    repeat rewrite ldot_cons. inversion H1. inversion H0.
    rewrite IHl1 with (r:=length l1); auto.
    (* IF we have ring ability, it is easy. *)
    rewrite mul_add_distr_l.
    remember (mul a a0). remember (mul a a1).
    remember (ldot l1 l2). remember (ldot l1 l3).
    (* (a2 + a3) + (a4 + a5)  = (a2 + a4) + (a3 + a5) *)
    repeat rewrite add_assoc; f_equal. repeat rewrite <- add_assoc; f_equal.
    auto.
  Qed.
  
  (** ldot right distributive over ladd.
    (l1 + l2) . l3 = l1.l3 + l2.l3 *)
  Lemma ldot_ladd_distr_r : forall l1 l2 l3 r,
    length l1 = r -> length l2 = r -> length l3 = r ->
    ldot (ladd add l1 l2) l3 = add (ldot l1 l3) (ldot l2 l3).
  Proof.
    induction l1,l2,l3; simpl; intros; subst; auto; try discriminate.
    repeat rewrite ldot_cons. inversion H1. inversion H0.
    rewrite IHl1 with (r:=length l1); auto.
    (* IF we have ring ability, it is easy. *)
    remember (ldot l1 l3). remember (ldot l2 l3).
    rewrite mul_add_distr_r. remember (mul a a1). remember (mul a0 a1).
    (* (a4 + a5) + (a2 + a3) = (a4 + a2) + (a5 + a3) *)
    repeat rewrite add_assoc; f_equal. repeat rewrite <- add_assoc; f_equal.
    auto.
  Qed.
  
  (** ldot right distributive over lcmul and mul.
    (x * l1) . l2 = x * (l1 . l2) *)
  Lemma ldot_lcmul_distr_r : forall l1 l2 x,
    ldot (lcmul mul x l1) l2 = mul x (ldot l1 l2).
  Proof.
    induction l1,l2; simpl; intros; auto.
    - repeat rewrite ldot_nil_l; rewrite mul_comm; auto.
    - repeat rewrite ldot_nil_l; rewrite mul_comm; auto.
    - repeat rewrite ldot_nil_r; rewrite mul_comm; auto.
    - repeat rewrite ldot_cons. rewrite IHl1.
      remember (ldot l1 l2). rewrite mul_add_distr_l. f_equal.
      rewrite mul_assoc. auto.
  Qed.
  
  (** ldot left distributve over map2.
    dot (map l1 l2) l3 = dot l1 l3 + dot l2 l3 *)
  Lemma ldot_map2_distr_l : forall l1 l2 l3 r,
    length l1 = r -> length l2 = r -> length l3 = r ->
    ldot (map2 add l1 l2) l3 = 
    add (ldot l1 l3) (ldot l2 l3).
  Proof.
    induction l1,l2,l3; simpl in *; intros; auto; subst; try discriminate.
    repeat rewrite ldot_cons.
    (* (r1 + p1) + (r2 + p2) => (r1 + r2) + (p1 + p2) *)
    remember (mul a a1) as r1. remember (mul a0 a1) as r2.
    remember (ldot l1 l3) as p1. remember (ldot l2 l3) as p2.
    rewrite <- add_assoc. rewrite (add_comm _ r2). rewrite <- add_assoc.
    rewrite (add_comm r2 r1). remember (add r1 r2) as r12.
    rewrite add_assoc. rewrite Heqr12,Heqp1,Heqp2,Heqr1,Heqr2. f_equal; auto.
    inversion H1. inversion H0.
    remember (length l1) as r0. apply IHl1 with (r:=r0); auto.
  Qed.
  
  (** ldot right distributve over map2.
    dot l1 (map l2 l3) = dot l1 l2 + dot l1 l3 *)
  Lemma ldot_map2_distr_r : forall l1 l2 l3 r,
    length l1 = r -> length l2 = r -> length l3 = r ->
    ldot l1 (map2 add l2 l3) = 
    add (ldot l1 l2) (ldot l1 l3).
  Proof.
    induction l1,l2,l3; simpl in *; intros; auto; subst; try discriminate.
    repeat rewrite ldot_cons.
    (* (r1 + p1) + (r2 + p2) => (r1 + r2) + (p1 + p2) *)
    remember (mul a a0) as r1. remember (mul a a1) as r2.
    remember (ldot l1 l2) as p1. remember (ldot l1 l3) as p2.
    rewrite <- add_assoc. rewrite (add_comm _ r2). rewrite <- add_assoc.
    rewrite (add_comm r2 r1). remember (add r1 r2) as r12.
    rewrite add_assoc. rewrite Heqr12,Heqp1,Heqp2,Heqr1,Heqr2. f_equal; auto.
    inversion H1. inversion H0.
    remember (length l1) as r0. apply IHl1 with (r:=r0); auto.
  Qed.

End ldot.

Arguments ldot {A}.
Arguments ldot_comm {A}.



(* ======================================================================= *)
(** ** Generate special list for MatrixUnit *)
Section GenerateSpecialList.
  
  Variable A : Type.
  Variable A0 A1 : A.
  
  (** create a list for matrix unit, which length is n and almost all elements 
    are A0 excepts i-th is A1. *)
  Fixpoint list_unit (n i : nat) : list A :=
    match n, i with
    | 0, _ => []
    | S n, 0 => A1 :: (repeat A0 n)
    | S n, S i => A0 :: (list_unit n i)
    end.
  
  Lemma list_unit_length : forall n i, length (list_unit n i) = n.
  Proof.
    induction n; auto. destruct i; simpl; auto. rewrite repeat_length. auto.
  Qed.
  
  (** list_unit(n,i) [i] = A1, when i < n *)
  Lemma list_unit_A1 : forall n i, i < n -> 
    nth i (list_unit n i) A0 = A1.
  Proof.
    induction n; try easy. destruct i; simpl; auto.
    intros; apply IHn.
    apply Nat.succ_lt_mono; auto.
  Qed.
  
  (** list_unit(n,i) [j] = A0, when i < n /\ j <> i *)
  Fact list_unit_spec1 : forall n i j, i < n -> j <> i ->
    nth j (list_unit n i) A0 = A0.
  Proof.
    induction n; try easy. intros. destruct i,j; simpl; try easy.
    - apply nth_repeat_same.
    - apply IHn; lia.
  Qed.
  
  (** list_unit(n,i) [j] = A0, j <> i *)
  Lemma list_unit_A0 : forall n i j, j <> i -> 
    nth j (list_unit n i) A0 = A0.
  Proof.
    induction n; try easy; simpl; intros. destruct j; auto.
    destruct i,j; simpl; try easy.
    apply nth_repeat_same. apply IHn. auto.
  Qed.
  
(*   (** create a list for matrix unit, which length is n and almost all elements 
    are A0 excepts the (n-i+1) element is A1. *)
  Fixpoint list_unit_rev (n i : nat) : list A :=
    match n, i with
    | 0, _ => []
    | S n, 0 => A1 :: (repeat A0 n)
    | S n, S i => A0 :: (list_unit n i)
    end. *)
    
End GenerateSpecialList.

Arguments list_unit {A}.

(* Compute list_unit 0 1 0 2.
Compute list_unit 0 1 3 0.
Compute list_unit 0 1 3 1.
Compute list_unit 0 1 3 2.
Compute list_unit 0 1 3 3. *)



(* ======================================================================= *)
(** ** Convert list to fixed-length list *)
Section List2FixedlengthList.
  
  Variable A : Type.
  Variable A0 : A.
  
  Fixpoint list_to_listN (l : list A) (n : nat) : list A :=
    match n with
    | 0 => []
    | S n' => (hd A0 l) :: (list_to_listN (tl l) n')
    end.
  
  Lemma list_to_listN_length : forall (l : list A) (n : nat),
    length (list_to_listN l n) = n.
  Proof.
    intros l n. gd l. induction n; intros; simpl; auto.
  Qed.
  
  Lemma list_to_listN_eq : forall (l : list A) (n : nat) 
    (H1 : length l = n), list_to_listN l n = l.
  Proof.
    intros l n. gd l. induction n; intros; simpl.
    - apply length_zero_iff_nil in H1; auto.
    - rewrite IHn; destruct l; auto. easy. easy.
  Qed.

End List2FixedlengthList.

Arguments list_to_listN {A}.
Arguments list_to_listN_length {A A0 l n}.


