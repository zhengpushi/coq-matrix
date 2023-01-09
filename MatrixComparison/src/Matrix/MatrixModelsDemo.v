(**
   purpose : Quick view of the different formal matrix models
   author  : ZhengPu Shi (zhengpushi@nuaa.edu.cn)
   remark  :
   1. there are five formal matrix models I known now.
   (1) DR: dependent record
   (2) DL: dependent list
   (3) DP: dependent pair
   (4) NF: function with natural indexing
   (5) FF: function with fin indexing
 *)

Require List ZArith.
Require Vectors.Fin Vectors.Vector.

Declare Scope vec_scope.
Delimit Scope vec_scope with vec.
Open Scope vec_scope.

Declare Scope mat_scope.
Delimit Scope mat_scope with mat.
Open Scope mat_scope.


(** * model 4 : NF : Function with Natural number indexing *)
(** Main idea: matrix is a function from two index to a value *)
Module NF.
  Import List ListNotations.
  
  (** matrix model *)
  Section matrix.
    Context {A : Type} (A0 : A) (Aadd Amul : A -> A -> A).

    (** Definition of matrix type *)
    Definition mat (r c : nat) : Type := nat -> nat -> A.

    (** Get i-th row of a matrix *)
    Fixpoint mrow_aux {r c : nat} (ri : nat) (cnt : nat) (m : mat r c) : list A :=
      match c with
      | O => nil
      | S c' => m ri cnt :: (@mrow_aux r c' ri (S cnt) m)
      end.
    Definition mrow {r c : nat} (ri : nat) (m : mat r c) := @mrow_aux r c ri 0 m.

    (** Convert between matrix and list list *)
    Fixpoint m2l_aux {r c : nat} (cnt : nat) (m : mat r c) : list (list A) := 
      match r with
      | O => nil
      | S r' => mrow cnt m :: (@m2l_aux r' c (S cnt) m)
      end.
    Definition m2l {r c} (m : mat r c) := m2l_aux 0 m.
    Definition l2m (r c : nat) (dl : list (list A)) : mat r c := 
      (fun x y => nth y (nth x dl []) A0).

    (** Sum of a sequence *)
    Fixpoint seqsum (f : nat -> A) (n : nat) : A :=
      match n with
      | O => A0
      | S n' => Aadd (seqsum f n') (f n')
      end.

    (** Multiplication of two matrices *)
    Definition mmul {r c t : nat} (m1 : mat r c) (m2 : mat c t) : mat r t :=
        (fun x z => seqsum (fun y => Amul (m1 x y) (m2 y z)) c).
    
  End matrix.

  Section matrix_Z.
    Import List ListNotations ZArith.
    Open Scope Z_scope.
 
    Notation l2m := (l2m 0).
    Notation mmul := (mmul 0 Zplus Zmult).

    Let m1 : mat 4 4 :=
          l2m 4 4
            [[1;2;3;4];
             [5;6;7;8];
             [9;10;11;12];
             [13;14;15;16]].
    Let m2 : mat 4 4 :=
          l2m 4 4
            [[17;18;19;20];
             [21;22;23;24];
             [25;26;27;28];
             [29;30;31;32]].

    Compute m2l (mmul m1 m2).
    (* = [[250; 260; 270; 280]; *)
    (*    [618; 644; 670; 696]; *)
    (*    [986; 1028; 1070; 1112]; *)
    (*    [1354; 1412; 1470; 1528]] *)
    (*  : list (list Z) *)
  End matrix_Z.

End NF.


(** * model 3 : DP : Dependent Pair *)
(** Main idea: matrix is a vector of vectors, which with a fixpoint function *)
Module DP.
  Import List ListNotations.

  (** vector model *)
  Section vector.
    Context {A : Type} (A0 : A).

    (** Definition of a vector *)
    Fixpoint vec (n : nat) : Type :=
      match n with
      | O => unit
      | S n => prod A (vec n)
      end.

    (** Convert between vector and list *)
    Fixpoint v2l {n} : vec n -> list A :=
      match n with
      | 0 => fun (v : vec 0) => []
      | S n' => fun (v : vec (S n')) => (fst v) :: (v2l (snd v))
      end.
    Fixpoint l2v (l : list A) (n : nat) {struct n} : vec n :=
      match n as n0 return (vec n0) with
      | 0 => tt
      | S n' => (hd A0 l, l2v (tl l) n')
      end.

    Notation "[ ]" := (tt : vec 0) : vec_scope.
    Notation "[ x ]" := (pair x (vec 0)) : vec_scope.
    Notation "[ x1 ; .. ; xn ]" := (pair x1 .. (pair xn tt) .. ) : vec_scope.

  End vector.
  
  (** matrix model *)
  Section matrix.
    Context {A : Type} (A0 : A) (Aadd Amul : A -> A -> A).

    (** Definition of matrix type *)
    Definition mat (r c : nat) : Type := @vec (@vec A c) r.

    (** Convert between matrix and list list *)
    Fixpoint m2l {r c} : (mat r c) -> list (list A) :=
      match r with
      | O => fun _ => nil
      | S r' => fun (m : @vec (@vec A c) (S r')) =>
                 cons (v2l (fst m)) (m2l (snd m))
      end.
    Fixpoint l2m (dl : list (list A)) (r c : nat) : mat r c :=
      match r with
      | 0 => tt
      | S n' => (l2v A0 (hd nil dl) c, l2m (tl dl) n' c)
      end.
    
    (** Fold a vector to an element from left to right *)
    Fixpoint vfoldl {n} (Aadd : A -> A -> A) (A0 : A) : (vec n) -> A := 
      match n with
      | O => fun (v : vec 0) => A0
      | S n' => fun (v : vec (S n')) => Aadd (fst v) (vfoldl Aadd A0 (snd v))
      end.

    (** Maping of two vectors *)
    Fixpoint vmap2 {n} (f : A -> A -> A) : vec n -> vec n -> vec n :=
      match n with
      | O => fun (v1 : vec 0) (v2 : vec 0) => tt
      | S n' => fun (v1 : vec (S n')) (v2 : vec (S n')) => 
                 (f (fst v1) (fst v2), vmap2 f (snd v1) (snd v2))
      end.

    (** dot product of two vectors *)
    Definition vdot {n} (v1 v2 : vec n) := vfoldl Aadd A0 (vmap2 Amul v1 v2).

    (** Inner product a vector and a matrix. v(c) *' m(r,c) = v(r) *)
    Fixpoint vdotm {r c} (v : @vec A c) : mat r c -> @vec A r :=
      match r with 
      | O => fun _ => tt
      | S r' => fun (m : mat (S r') c) => (vdot v (fst m), vdotm v (snd m))
      end.

    (** Inner product of two matrices. m(r1,c) *' (m(r2,c) = m(r1,r2) *)
    Fixpoint mdot {r c t} : (mat r c) -> (mat t c) -> (mat r t) :=
      match r with
      | O => fun _ _ => tt
      | S r' => fun (m1 : mat (S r') _) m2 => (vdotm (fst m1) m2, mdot (snd m1) m2)
      end.

    (** Get head column of a matrix *)
    Fixpoint mhdc {r c} : mat r (S c) -> vec r :=
      match r with
      | O => fun _ => tt
      | S r' => fun (m : mat (S r') (S c)) => (fst (fst m), mhdc (snd m))
      end.
    
    (** Get tail columns of a matrix *)
    Fixpoint mtlc {r c} : mat r (S c) -> mat r c :=
      match r with
      | O => fun _ => tt
      | S r' => fun (m : mat (S r') (S c)) => (snd (fst m), mtlc (snd m))
      end.

    (** Transpose a matrix *)
    Fixpoint mtrans {r c} : mat r c -> mat c r :=
      match c with
      | O => fun (m : mat r 0) => tt
      | S c' => fun (m : mat r (S c')) => (mhdc m, mtrans (mtlc m))
      end.

    (** Multiplication of two matrices *)
    Definition mmul {r c s} (m1 : mat r c) (m2 : mat c s) : mat r s :=
      mdot m1 (mtrans m2).
    
  End matrix.

  Section matrix_Z.
    Import List ListNotations ZArith.
    Open Scope Z_scope.
 
    Notation l2m := (l2m 0).
    Notation mmul := (mmul 0 Zplus Zmult).

    Let m1 : mat 4 4 :=
          l2m [[1;2;3;4];
               [5;6;7;8];
               [9;10;11;12];
               [13;14;15;16]] 4 4.
    Let m2 : mat 4 4 :=
          l2m [[17;18;19;20];
               [21;22;23;24];
               [25;26;27;28];
               [29;30;31;32]] 4 4.

    Compute m2l (mmul m1 m2).
    (* = [[250; 260; 270; 280]; *)
    (*    [618; 644; 670; 696]; *)
    (*    [986; 1028; 1070; 1112]; *)
    (*    [1354; 1412; 1470; 1528]] *)
    (*  : list (list Z) *)
  End matrix_Z.

End DP.


(** * model 2 : DL : Dependent List *)
(** Main idea: use Coq.Vectors.Vector *)
Module DL.
  Import Fin Vector.

  Notation fin := Fin.t.
  Notation vec := Vector.t.
  Arguments vec {A}.

  (** vector model *)
  Section vector.
    Import VectorNotations.
    Context {A : Type} (A0 : A) (Aadd Amul : A -> A -> A).
    
    (** Build vector with a function [gen: fin n -> A] *)
    Fixpoint vmake {n} : (fin n -> A) -> vec n :=
      match n with
      | O => fun _ => []
      | S n' => fun (gen : fin (S n') -> A) =>
                 (gen F1) :: (vmake (fun (fn':fin n') => gen (FS fn'))) 
      end.
  End vector.
  
  (** matrix model *)
  Section matrix.
    Import List ListNotations Vector VectorNotations.
    Context {A : Type} (A0 : A) (Aadd Amul : A -> A -> A).

    (** Definition of matrix type *)
    Definition mat r c := @vec (@vec A c) r.

    (** Convert between vector and list *)
    Fixpoint v2l {n} (v : @vec A n) : list A :=
      match v with
      | []%vector => []%list
      | (x :: v')%vector => (x :: (v2l v'))%list
      end.
    Fixpoint l2v (l : list A) (n : nat) : vec n :=
      match n with
      | 0 => []%vector
      | S n' => (List.hd A0 l) :: (l2v (List.tl l) n')
      end.

    (** Convert between matrix and list list *)
    Fixpoint m2l {r c} (m : mat r c) : list (list A) :=
      match m with
      | []%vector => []%list
      | (x :: v')%vector => (v2l x) :: (m2l v')
      end.
    Fixpoint l2m (dl : list (list A)) (r c : nat) : mat r c :=
      match r with
      | 0 => []
      | S n' => (l2v (List.hd List.nil dl) c) :: (l2m (List.tl dl) n' c)
      end.

    (** dot product of two vectors *)
    Definition vdot {n} (v1 v2 : vec n) := fold_left Aadd A0 (map2 Amul v1 v2).

    (** Get a column *)
    Definition mcol {r c} (m : mat r c) :=
      fun fc : fin c => vmake (fun fr : fin r => nth (nth m fr) fc).

    (** Multiplication of two matrices *)
    Definition mmul {r s c : nat} (m1 : mat r s) (m2 : mat s c) : mat r c :=
      vmake (fun fr : fin r =>
               vmake (fun fc : fin c =>
                        vdot (nth m1 fr) (mcol m2 fc)
        )).
  End matrix.

  Section matrix_Z.
    Import List ListNotations ZArith.
    Open Scope Z_scope.

    Notation l2m := (l2m 0).
    Notation mmul := (mmul 0 Zplus Zmult).

    Let m1 : mat 4 4 :=
          l2m [[1;2;3;4];
               [5;6;7;8];
               [9;10;11;12];
               [13;14;15;16]] 4 4.
    Let m2 : mat 4 4 :=
          l2m [[17;18;19;20];
               [21;22;23;24];
               [25;26;27;28];
               [29;30;31;32]] 4 4.

    Compute m2l (mmul m1 m2).
    (* = [[250; 260; 270; 280]; *)
    (*    [618; 644; 670; 696]; *)
    (*    [986; 1028; 1070; 1112]; *)
    (*    [1354; 1412; 1470; 1528]] *)
    (*  : list (list Z) *)
  End matrix_Z.

End DL.


(** * model 1 : DR : Dependent Record *)
(** Main idea: use (list (list A)) to store the matrix data *)
Module DR.

  Import List ListNotations.

  (** matrix model *)
  Section matrix.
    Context {A : Type}.
    
    (** All list in a dlist have same length. Note: dlist means list (list A)  *)
    Definition width (dl : list (list A)) (c : nat) : Prop :=
      Forall (fun l => length l = c) dl.

    (** Definition of matrix type *)
    Record mat (r c : nat) := {
        mat_data : list (list A);
        mat_length : length mat_data = r;
        mat_width : width mat_data c
      }.

    Arguments Build_mat {r c}.
    Arguments mat_data {r c}.
    Arguments mat_length {r c}.
    Arguments mat_width {r c}.

    (** Construct a dlist by column with a list and a dlist *)
    Fixpoint consc (l : list A) (dl : list (list A)) : list (list A) :=
      match l, dl with
      | xl :: tl, xdl :: tdl => (xl :: xdl) :: (consc tl tdl)
      | _, _ => []
      end.

    (** a list list that every list is nil, named as dnil *)
    Fixpoint dnil (n : nat) : list (list A) :=
      match n with
      | O => nil
      | S n' => nil :: (dnil n')
      end.

    (** Transposition of the content of a matrix *)
    Fixpoint dltrans (dl : list (list A)) (c : nat) : list (list A) :=
      match dl with
      | [] => dnil c
      | l :: tl => consc l (dltrans tl c)
      end.

    (** dltrans length law *)
    Lemma dltrans_length : forall dl c, width dl c -> length (dltrans dl c) = c.
    Proof. Admitted. (* this lemma is proved. details see the project *)
    
    (** dltrans width law *)
    Lemma dltrans_width : forall dl r c,
        length dl = r -> width dl c -> width (dltrans dl c) r.
    Proof. Admitted. (* this lemma is proved. details see the project *)

    (** Transposition of a matrix *)
    Definition mtrans {r c} (m : mat r c) : mat c r.
      refine (Build_mat (dltrans (mat_data m) c) _ _).
      apply dltrans_length. apply mat_width.
      apply dltrans_width. apply mat_length. apply mat_width.
    Defined.

    (** map operation to two list *)
    Fixpoint map2 (f : A -> A -> A) (l1 l2 : list A) : list A :=
      match l1, l2 with
      | x1 :: t1, x2 :: t2 => (f x1 x2) :: (map2 f t1 t2)
      | _, _ => []
      end.

    (** Assume that we have a zero number *)
    Context (A0 : A).

    (** list to fixed-length list (vector) *)
    Fixpoint l2v_aux (l : list A) (n : nat) : list A :=
      match n with
      | 0 => []
      | S n' => (hd A0 l) :: (l2v_aux (tl l) n')
      end.
    
    (** list list to fixed-shape list list (matrix) *)
    Fixpoint l2m_aux (dl : list (list A)) (r c : nat) : list (list A) :=
      match r with
      | 0 => []
      | S n' => (l2v_aux (hd nil dl) c) :: (l2m_aux (tl dl) n' c)
      end.
    
    Lemma l2m_aux_length : forall (dl : list (list A)) (r c : nat),
        length (l2m_aux dl r c) = r.
    Proof. Admitted. (* this lemma is proved. details see the project *)
    
    Lemma l2m_aux_width : forall (dl : list (list A)) (r c : nat),
        width (l2m_aux dl r c) c.
    Proof. Admitted. (* this lemma is proved. details see the project *)

    (** dlist to matrix *)
    Definition l2m (dl : list (list A)) (r c : nat) : mat r c.
      refine (Build_mat (l2m_aux dl r c) _ _).
      apply l2m_aux_length.
      apply l2m_aux_width.
    Defined.

    (** matrix to dlist *)
    Definition m2l {r c} (m : mat r c) := mat_data m.

    (** Assume that we have two operations of the element: Addition, Multiplication *)
    Context (Aadd Amul : A -> A -> A).

    (** dot product, marked as l1 . l2 *)
    Definition ldot (l1 l2 : list A) : A :=
      fold_right Aadd A0 (map2 Amul l1 l2).

    (** list dot product to dlist *)
    Fixpoint ldotdl (l : list A) (dl : list (list A)) : list A :=
      match dl with
      | h :: t => (ldot l h) :: (ldotdl l t)
      | [] => []
      end.

    (** dlist dot product *)
    Fixpoint dldotdl (dl1 dl2 : list (list A)) : list (list A) :=
      match dl1 with
      | h1 :: t1 => (ldotdl h1 dl2) :: (dldotdl t1 dl2)
      | [] => []
      end.

    (** dldotdl length law *)
    Lemma dldotdl_length : forall dl1 dl2 r1,
        length dl1 = r1 -> length (dldotdl dl1 dl2) = r1.
    Proof. Admitted. (* this lemma is proved. details see the project *)

    (** dldotdl width law *)
    Lemma dldotdl_width : forall dl1 dl2 r2 c,
        length dl2 = r2 -> width dl1 c -> width dl2 c ->  width (dldotdl dl1 dl2) r2.
    Proof. Admitted. (* this lemma is proved. details see the project *)

    (** Multiplication of two matrices *)
    Definition mmul {r c t : nat} (m1 : mat r c) (m2 : mat c t) : mat r t.
      refine (Build_mat (dldotdl (mat_data m1) (mat_data (mtrans m2))) _ _).
      apply dldotdl_length. apply mat_length.
      apply dldotdl_width with (c:=c). apply mat_length. apply mat_width.
      simpl. apply dltrans_width. apply mat_length. apply mat_width.
    Defined.

  End matrix.

  Section matrix_Z.
    Import ZArith.
    Open Scope Z_scope.
    Open Scope mat_scope.

    Notation l2m := (l2m 0).
    Notation mmul := (mmul 0 Zplus Zmult).

    Let m1 : mat 4 4 :=
          l2m [[1;2;3;4];
               [5;6;7;8];
               [9;10;11;12];
               [13;14;15;16]] 4 4.
    Let m2 : mat 4 4 :=
          l2m [[17;18;19;20];
               [21;22;23;24];
               [25;26;27;28];
               [29;30;31;32]] 4 4.

    Compute m2l (mmul m1 m2).
    (* = [[250; 260; 270; 280]; *)
    (*    [618; 644; 670; 696]; *)
    (*    [986; 1028; 1070; 1112]; *)
    (*    [1354; 1412; 1470; 1528]] *)
    (*  : list (list Z) *)
  End matrix_Z.

End DR.
