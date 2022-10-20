(*
  purpose   : Extension for general list list
  author    : ZhengPu Shi
  date      : 2021.12
  
  history   :
  
  1. 2021.12, by Zhengpu Shi.
    first version
  
  2. 2022.05, by Zhengpu Shi.
    split big file into small modules
  
*)


Require Export ListExt.



(* ======================================================================= *)
(** ** width of a dlist (list (list A)) *)
Section dlist_width.
  
  Variable A : Type.
  
  (** A proposition that every list of a list list has same length *)
  Fixpoint width (dl : list (list A)) n : Prop :=
    match dl with
    | [] => True
    | x :: t => (length x = n) /\ width t n
    end.
  
  (** width property should be kept by its child structure *)
  Lemma cons_width : forall (l : list A) dl n, width (l :: dl) n ->
    length l = n /\ width dl n.
  Proof. intros. auto. Qed.

  (** width property should be kept by every child element *)
  Lemma width_imply_in_length : forall l dl n, 
    width dl n -> In l dl -> length l = n.
  Proof.
    intros. induction dl.
    - inversion H0.
    - apply cons_width in H; destruct H. apply in_inv in H0. destruct H0.
      + subst. auto.
      + apply IHdl; auto.
  Qed.
  
  (** app operation won't change width property *)
  Lemma app_width : forall dl1 dl2 n, 
    width (dl1 ++ dl2) n <-> width dl1 n /\ width dl2 n.
  Proof.
    induction dl1; simpl; intros; split; intros H; auto; destruct H; auto.
    - apply IHdl1 in H0. destruct H0. repeat split; auto.
    - destruct H. split; auto. apply IHdl1. split; auto.
  Qed.
  
  (** rev operation won't change width property *)
  Lemma rev_width : forall dl n, width (rev dl) n -> width dl n.
  Proof.
    induction dl; simpl; intros; auto.
    apply app_width in H. simpl in H. destruct H. destruct H0. split; auto.
  Qed.
  
  (** repeat generated list list will keep width property same as seed element *)
  Lemma repeat_width : forall (l : list A) n k,
    length l = k -> width (repeat l n) k.
  Proof. induction n; intros; simpl; auto. Qed.
  
  (** width promise i-th row has same length *)
  Lemma width_imply_nth_length : forall i c dl, 
    i < length dl -> width dl c -> length (nth i dl []) = c.
  Proof.
    intros i c dl.
    gd c. gd i.
    induction dl.
    - intros. simpl in *. lia.
    - intros. simpl in *. destruct H0.
      destruct i; auto. apply IHdl; auto. lia.
  Qed.
  
End dlist_width.

Arguments width {A}.



(* ======================================================================= *)
(** ** Set element with a constant value *)
Section SetByConstant.
  
  (* --------------------------------------------------------------------- *)
  (** *** Modify a list list *)
  
  (** Definition *)
  Fixpoint dlst_chg {A} (dl : list (list A)) (ri ci : nat) (x : A) 
    : list (list A) :=
    match dl, ri with
    | [], _ => []
    | l :: dl, 0 => (lst_chg l ci x) :: dl
    | l :: dl, S ri => l :: (dlst_chg dl ri ci x)
    end. 
  
  (* Compute dlst_chg [] 0 1 9.
  Compute dlst_chg [[1;2];[3;4;5]] 0 1 9.
  Compute dlst_chg [[1;2];[3;4;5]] 1 1 9.
  Compute dlst_chg [[1;2];[3;4;5]] 2 1 9.
  Compute dlst_chg [[1;2];[3;4;5]] 1 5 9.
   *)
  
  (** Height property *)
  Lemma dlst_chg_height : forall {A} dl ri r ci x, 
    length dl = r ->
    length (@dlst_chg A dl ri ci x) = r.
  Proof.
    intros A dl; induction dl; auto. destruct ri; intros; auto; simpl in *.
    destruct r; auto. easy.
  Qed.
  
  (** Width property *)
  Lemma dlst_chg_width : forall {A} dl ri c ci x, 
    width dl c ->
    width (@dlst_chg A dl ri ci x) c.
  Proof.
    intros A dl; induction dl; auto.
    destruct ri; intros; simpl in *; auto; destruct H; split; auto.
    apply lst_chg_height; auto.
  Qed.

End SetByConstant.



(* ======================================================================= *)
(** ** Set element with a generation function *)
Section SetByFunction.

  (** Inner version, ri0 is given position, ri is changing every loop *)
  Fixpoint dlst_chgf_aux {A} (dl : list (list A)) (ri0 ri ci : nat) 
    (f : nat -> nat -> A) 
    : list (list A) :=
    match dl, ri with
    | [], _ => []
    | l :: dl, 0 => (lst_chgf l ci (f ri0)) :: dl
    | l :: dl, S ri => l :: (dlst_chgf_aux dl ri0 ri ci f)
    end. 
  
  (** User version that hide ri0 parameter *)
  Definition dlst_chgf {A} (dl : list (list A)) (ri ci : nat) 
    (f : nat -> nat -> A) 
    : list (list A) :=
    dlst_chgf_aux dl ri ri ci f.
  
  (* Let f_gen := fun (i j : nat) => (i + j + 10).
  Compute dlst_chgf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 0 0 f_gen.
  Compute dlst_chgf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 0 1 f_gen.
  Compute dlst_chgf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 0 2 f_gen.
  Compute dlst_chgf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 0 3 f_gen.
  Compute dlst_chgf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 0 4 f_gen.
  Compute dlst_chgf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 1 0 f_gen.
  Compute dlst_chgf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 1 1 f_gen.
  Compute dlst_chgf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 1 2 f_gen.
  Compute dlst_chgf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 1 3 f_gen.
  Compute dlst_chgf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 1 4 f_gen.
  *)
  
  (** Height property *)
  Lemma dlst_chgf_aux_height : forall {A} dl ri r ri0 ci f, 
    length dl = r ->
    length (@dlst_chgf_aux A dl ri0 ri ci f) = r.
  Proof.
    intros A dl; induction dl; auto. destruct ri; auto; simpl; intros.
    destruct r; auto. easy.
  Qed.
  
  Lemma dlst_chgf_height : forall {A} dl r ri ci f, 
    length dl = r ->
    length (@dlst_chgf A dl ri ci f) = r.
  Proof.
    intros. apply dlst_chgf_aux_height. auto.
  Qed.
  
  (** Width property *)
  Lemma dlst_chgf_aux_width : forall {A} dl ri c ri0 ci f, 
    width dl c ->
    width (@dlst_chgf_aux A dl ri0 ri ci f) c.
  Proof.
    intros A dl; induction dl; auto. 
    induction ri; intros; simpl in *; auto; inversion H; split; auto.
    apply lst_chgf_height; auto.
  Qed.
  
  Lemma dlst_chgf_width : forall {A} dl ri c ci f, 
    width dl c ->
    width (@dlst_chgf A dl ri ci f) c.
  Proof.
    intros. apply dlst_chgf_aux_width; auto.
  Qed.

End SetByFunction.



(* ======================================================================= *)
(** ** Set row with a constant value *)
Section SetRowByConstant.
  
  (** Definition *)
  Fixpoint dlst_chgrow {A} (dl : list (list A)) (ri : nat) (x : list A) 
    : list (list A) :=
    match dl, ri with
    | [], _ => []
    | l :: dl, 0 => x :: dl
    | l :: dl, S ri => l :: (dlst_chgrow dl ri x)
    end. 
  
(*   Compute dlst_chgrow [] 0 [8;9].
  Compute dlst_chgrow [[1;2];[3;4;5]] 0 [8;9].
  Compute dlst_chgrow [[1;2];[3;4;5]] 1 [8;9].
  Compute dlst_chgrow [[1;2];[3;4;5]] 2 [8;9].
 *)  
  (** Height property *)
  Lemma dlst_chgrow_height : forall {A} dl ri r x, 
    length dl = r ->
    length (@dlst_chgrow A dl ri x) = r.
  Proof.
    intros A dl; induction dl; auto. destruct ri; auto; intros; simpl in *.
    destruct r; auto. easy.
  Qed.
  
  (** Width property *)
  Lemma dlst_chgrow_width : forall {A} dl ri c x,
    length x = c ->
    width dl c ->
    width (@dlst_chgrow A dl ri x) c.
  Proof.
    intros A dl; induction dl; auto. 
    induction ri; intros; simpl in *; destruct H0; split; auto.
  Qed.

End SetRowByConstant.



(* ======================================================================= *)
(** ** Set row with a generation function *)
Section SetRowByFunction.
  
  (** Inner version, ri0 is given position, ri is changing every loop *)
  Fixpoint dlst_chgrowf_aux {A} (dl : list (list A)) (ri0 ri : nat) 
    (f : nat -> list A) 
    : list (list A) :=
    match dl, ri with
    | [], _ => []
    | l :: dl, 0 => (f ri0) :: dl
    | l :: dl, S ri => l :: (dlst_chgrowf_aux dl ri0 ri f)
    end. 
  
  (** User version that hide ri0 parameter *)
  Definition dlst_chgrowf {A} (dl : list (list A)) (ri : nat) 
    (f : nat -> list A) 
    : list (list A) :=
    dlst_chgrowf_aux dl ri ri f.
  
(*   Let f_gen := fun (i : nat) => [i+10;i+11;i+12].
  Compute dlst_chgrowf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 0 f_gen.
  Compute dlst_chgrowf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 1 f_gen.
  Compute dlst_chgrowf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 2 f_gen.
  Compute dlst_chgrowf [[1;2;3;4];[4;5;6;7];[8;9;10;11]] 3 f_gen.
 *) 
  
  (** Height property *)
  Lemma dlst_chgrowf_aux_height : forall {A} dl ri r ri0 f, 
    length dl = r ->
    length (@dlst_chgrowf_aux A dl ri0 ri f) = r.
  Proof.
    intros A dl; induction dl; auto. induction ri; auto.
    intros. simpl. destruct r; auto. easy.
  Qed.
  
  Lemma dlst_chgrowf_height : forall {A} dl r ri f, 
    length dl = r ->
    length (@dlst_chgrowf A dl ri f) = r.
  Proof.
    intros. apply dlst_chgrowf_aux_height. auto.
  Qed.
  
  (** Width property *)
  Lemma dlst_chgrowf_aux_width : forall {A} dl ri c ri0 f, 
    length (f ri0) = c ->
    width dl c ->
    width (@dlst_chgrowf_aux A dl ri0 ri f) c.
  Proof.
    intros A dl; induction dl; auto. 
    induction ri; intros; simpl in *; auto; inversion H0; split; auto.
  Qed.
  
  Lemma dlst_chgrowf_width : forall {A} dl ri c f, 
    length (f ri) = c ->
    width dl c ->
    width (@dlst_chgrowf A dl ri f) c.
  Proof.
    intros. apply dlst_chgrowf_aux_width; auto.
  Qed.

End SetRowByFunction.



(* ======================================================================= *)
(** ** Equality Decidability of dlist *)
Section dlist_eq_dec.

  Variable A : Type.
  Variable Aeq_dec : forall a1 a2 : A, {a1 = a2} + {a1 <> a2}.
  
  Lemma dlist_eq_dec : forall (dl1 dl2 : list (list A)),
    {dl1 = dl2} + {dl1 <> dl2}.
  Proof.
    apply list_eq_dec.
    apply list_eq_dec. auto.
  Qed.
  
End dlist_eq_dec.



(* ======================================================================= *)
(** ** Properties of dlist *)
Section props_dlist.

  (** ** Height of a empty dlist *)
  Lemma dlist_h0_iff {A} : forall (dl : list (list A)), 
    length dl = 0 -> dl = nil.
  Proof. destruct dl; simpl; auto. intros H; easy. Qed.
  
  (** Two list list equal iff all nth nth visit equal *)
  Lemma dlist_eq_iff_nth_nth {A A0} : forall r c (dl1 dl2 : list (list A))
    (H1 : length dl1 = r) (H2 : length dl2 = r)
    (H3 : width dl1 c) (H4 : width dl2 c),
    dl1 = dl2 <-> (forall (ri ci : nat), ri < r -> ci < c -> 
      nth ci (nth ri dl1 []) A0 = nth ci (nth ri dl2 []) A0).
  Proof.
    intros; split; intros.
    - subst; auto.
    - apply nth_ext with (d := []) (d' := []).
      + subst; auto.
      + intros. apply nth_ext with (d := A0) (d' := A0).
        * rewrite width_imply_nth_length with (c:=c); auto.
          rewrite width_imply_nth_length with (c:=c); auto. lia.
        * intros. apply H; try lia.
          rewrite width_imply_nth_length with (c:=c) in H5; auto.
  Qed.

End props_dlist.



(* ======================================================================= *)
(** ** a dlist with same element nil *)
Section dnil.
  
  Variable A : Type.
  
  (** a list list that every list is nil, named as dnil *)
  Fixpoint dnil n : list (list A) :=
    match n with
    | O => nil
    | S n' => nil :: (dnil n')
    end.

  (** dnil's length law *)
  Lemma dnil_height : forall n, length (dnil n) = n.
  Proof. induction n; simpl; auto. Qed.

  (** dnil's width law *)
  Lemma dnil_width : forall n, width (dnil n) 0.
  Proof. induction n; simpl; auto. Qed.
  
  (** dnil equal to append two child dnil *)
  Lemma dnil_app : forall n1 n2, 
    dnil (n1 + n2) = dnil n1 ++ dnil n2.
  Proof. induction n1,n2; simpl; auto; rewrite IHn1; auto. Qed.

  (** width dl is zero imply it is a dnil *)
  Lemma dlist_w0_eq_dnil : forall (dl : list (list A)), 
    width dl 0 -> dl = dnil (length dl).
  Proof.
    induction dl; simpl; auto. intros [H1 H2]. f_equal; auto.
    apply length_zero_iff_nil; auto.
  Qed.

  (** rev a dnil is itself *)
  Lemma dnil_rev : forall n, rev (dnil n) = dnil n.
  Proof.
    induction n; simpl; auto. rewrite IHn. clear IHn. induction n; simpl; auto.
    rewrite IHn. auto.
  Qed.

End dnil.

Arguments dnil {A}.



(* ======================================================================= *)
(** ** map2 and dnil *)
Section map2_dnil.

  Variable A B C : Type.
  Variable f2 : A -> B -> C.

  (** map dnil dl = dnil *)
  Lemma map2_dnil_l : forall dl n, 
    length dl = n -> map2 (map2 f2) (dnil n) dl = dnil n.
  Proof.
    intros. gd dl. induction n; auto; intros.
    induction dl. inversion H. simpl. f_equal; auto.
  Qed.
  
  (** map dl dnil = dnil *)
  Lemma map2_dnil_r : forall dl n, 
    length dl = n -> map2 (map2 f2) dl (dnil n) = dnil n.
  Proof.
    intros. gd dl. induction n; simpl; intros.
    - induction dl; simpl; auto.
    - induction dl. inversion H. simpl. f_equal; auto. apply map2_nil_r.
  Qed.

End map2_dnil.



(* ======================================================================= *)
(** ** Convert between row and col. eg, [1;2;3] <-> [[1];[2];[3]] *)
Section convert_row_and_col.
  
  Variable A : Type.
  Variable A0 : A.
  
  (** Convert a list to a dlist, it looks like converting a row to a column. *)
  Fixpoint cvt_row2col (l : list A) : list (list A) :=
    match l with
    | [] => []
    | x :: tl => [x] :: (cvt_row2col tl)
    end.
  
  (** cvt_row2col height law *)
  Lemma cvt_row2col_height : forall l, length (cvt_row2col l) = length l.
  Proof. induction l; simpl; intros; auto. Qed.
  
  (** cvt_row2col width law *)
  Lemma cvt_row2col_width : forall l, width (cvt_row2col l) 1.
  Proof. induction l; simpl; intros; auto. Qed.
  
  (** Convert a dlist to a list which contain head element, it looks like 
    converting a column to a row. *)
  Fixpoint cvt_col2row (dl : list (list A)) : list A :=
    match dl with
    | [] => []
    | l :: tl => (hd A0 l) :: (cvt_col2row tl)
    end.
  
  (** Convert a dlist to list then convert it to a dlist, equal to original 
    dlist. *)
  Lemma cvt_row2col_col2row : forall (dl : list (list A)) r,
    length dl = r ->
    width dl 1 ->
    cvt_row2col (cvt_col2row dl) = dl.
  Proof.
    induction dl; simpl; auto; intros. inversion H. destruct H0. f_equal.
    - destruct a. inversion H0. inversion H0. apply length_zero_iff_nil in H4.
      subst. auto.
    - destruct r. inversion H. inversion H1. apply IHdl with (r:=r); auto.
  Qed.
  
  (** Convert a list to dlist then convert it to a list, equal to original 
    list. *)
  Lemma cvt_col2row_row2col : forall (l : list A), 
    cvt_col2row (cvt_row2col l) = l.
  Proof. induction l; simpl; auto; intros. f_equal; auto. Qed.
  
End convert_row_and_col.

Arguments cvt_row2col {A}.
Arguments cvt_col2row {A}.



(* ======================================================================= *)
(** ** head column of a dlist *)
Section hdc.

  Variable A : Type.
  Variable A0 : A.
  
  (** Get head column of a dlist *)
  Fixpoint hdc (dl : list (list A)) : list A :=
    match dl with
    | [] => []
    | l :: tl => (hd A0 l) :: (hdc tl)
    end.
  
  (** hdc length law *)
  Lemma hdc_length : forall dl, length (hdc dl) = length dl.
  Proof. induction dl; simpl; auto. Qed.
  
End hdc.

Arguments hdc {A}.



(* ======================================================================= *)
(** ** tail columns of a dlist *)
Section tlc.
  
  Variable A : Type.
  Variable A0 : A.
  
  (** Get tail columns of a dlist *)
  Fixpoint tlc (dl : list (list A)) : list (list A) :=
    match dl with
    | [] => []
    | l :: tl => (tail l) :: (tlc tl)
    end.
  
  (** tlc height law *)
  Lemma tlc_height : forall dl, length (tlc dl) = length dl.
  Proof. induction dl; simpl; auto. Qed.
  
  (** tlc width law when width equal to 0 *)
  Lemma tlc_width0 : forall dl, 
    width dl 0 -> width (tlc dl) 0.
  Proof.
    induction dl; simpl; auto. intros. destruct H. split; auto.
    apply length_zero_iff_nil in H. subst. auto. 
  Qed.
  
  (** tlc width law when width not equal to 0 *)
  Lemma tlc_widthS : forall dl c, 
    width dl (S c) -> width (tlc dl) c.
  Proof.
    induction dl; simpl; auto. intros. destruct H. split; auto.
    destruct a. inversion H. simpl in *. inversion H. auto.
  Qed.
  
End tlc.

Arguments tlc {A}.



(* ======================================================================= *)
(** ** construct a dlist with a list and a dlist by column *)
Section consc.

  Variable A : Type.
  Variable A0 : A.
  
  (** Construct a dlist by column with a list and a dlist *)
  Fixpoint consc (l : list A) (dl : list (list A)) : list (list A) :=
    match l, dl with
    | xl :: tl, xdl :: tdl => (xl :: xdl) :: (consc tl tdl)
    | _, _ => []
    end.
  
  (** consc height law *)
  Lemma consc_height : forall l dl r,
    length l = r -> length dl = r ->
    length (consc l dl) = r.
  Proof.
    induction l,dl; simpl; intros; auto. destruct r. inversion H. f_equal.
    inversion H. inversion H0. subst. apply IHl; auto.
  Qed.
  
  (** consc width law *)
  Lemma consc_width : forall l dl c,
    length l = length dl -> width dl c ->
    width (consc l dl) (S c).
  Proof.
    induction l,dl; simpl; intros; auto. inversion H. destruct H0. split; auto.
  Qed.
  
  (** consc with hdc and tlc of a dnil generate lzero *)
  Lemma consc_hdc_tlc_width0 : forall dl r, 
    length dl = r -> width dl 0 -> 
    consc (hdc A0 dl) (tlc dl) = cvt_row2col (repeat A0 r).
  Proof.
    induction dl; simpl; intros; subst; auto. destruct H0.
    rewrite length_zero_iff_nil in H. subst. simpl. f_equal. auto.
  Qed.
  
  (** consc with hdc and tlc of a dlist generate itself *)
  Lemma consc_hdc_tlc_widthS : forall dl c, 
    width dl (S c) ->
    consc (hdc A0 dl) (tlc dl) = dl.
  Proof.
    induction dl; simpl; intros; auto. destruct H. f_equal; auto.
    - destruct a. inversion H. auto.
    - apply IHdl with (c:=c). auto.
  Qed.

  (** consc decompose.
    x1::l1 ++ l2::dl2 = (x::l2) :: (l1 ++ dl2)  *)
  Lemma consc_decompose : forall x1 l1 l2 dl2,
    consc (x1::l1) (l2::dl2) = (x1::l2) :: (consc l1 dl2).
  Proof. intros. simpl. auto. Qed.
  
  (** repeat (x :: l) decomposition *)
  Lemma repeat_consr : forall l x n,
    repeat (x :: l) n = consc (repeat x n) (repeat l n).
  Proof. induction n; simpl; auto. rewrite IHn. auto. Qed.

End consc.

Arguments consc {A}.
Arguments consc_decompose {A}.
Arguments consc_hdc_tlc_widthS {A}.



(* ======================================================================= *)
(** ** Append two objects of dlist type to one object of dlist *)
Section dlist_app.
  
  Variable A : Type.
  
  (** dlist append by row *)
  Definition dlappr := app.
  
  (** dlist apend by column *)
  Fixpoint dlappc (dl1 dl2 : list (list A)) : list (list A) :=
    match dl1, dl2 with
    | l1 :: tl1, l2 :: tl2 => (app l1 l2) :: (dlappc tl1 tl2)
    | _, _ => []
    end.

End dlist_app.

Arguments dlappr {A}.
Arguments dlappc {A}.

Notation "l @@ r" := (dlappc l r) (at level 40) : list_scope.



(* ======================================================================= *)
(** ** Zero dlist *)
Section dlzero.

  Variable A : Type.
  Variable A0 : A.
  
  (** dlist constructed by repeated lzero, named as dlzero *)
  Definition dlzero r c := repeat (lzero A0 c) r.
  
  (** dlzero with S r rows could be splited to two parts *)
  Lemma dlzero_Sr : forall r c, dlzero (S r) c = (lzero A0 c) :: (dlzero r c).
  Proof.
    intros. auto.
  Qed.
  
  (** dlzero with 0 rows equal to dnil *)
  Lemma dlzero_dnil : forall {c}, dlzero c 0 = dnil c.
  Proof. induction c; simpl; auto. rewrite <- IHc. auto. Qed.
  
  (** dlzero heigth law *)
  Lemma dlzero_height : forall {r c}, length (dlzero r c) = r.
  Proof. intros. apply repeat_length. Qed.
  
  (** dlzero width law *)
  Lemma dlzero_width : forall {r c}, width (dlzero r c) c.
  Proof.
    induction r; intros. simpl. auto. simpl. split. apply lzero_length.
    unfold dlzero in IHr. auto.
  Qed.
  
  (** dlzero with 0 rows equal to dnil *)
  Lemma dlzero_w0_eq_dnil : forall r, (dlzero r 0) = dnil r.
  Proof. 
    induction r; auto. unfold dlzero in *. simpl in *. rewrite IHr. auto.
  Qed.
  
  (** append two dlzeros by row equal to whole *)
  Lemma dlzero_app_row : forall r1 r2 c,
    dlzero r1 c ++ dlzero r2 c = dlzero (r1 + r2) c.
  Proof. unfold dlzero. intros. rewrite repeat_app. auto. Qed.
  
  (** append two dlzeros by column equal to whole *)
  Lemma dlzero_app_col : forall r c1 c2,
    dlzero r c1 @@ dlzero r c2 = dlzero r (c1 + c2).
  Proof.
    induction r; intros; simpl; auto. unfold dlzero,lzero in *.
    rewrite IHr. simpl. f_equal. rewrite repeat_app. auto.
  Qed.

End dlzero.

Arguments dlzero {A}.
Arguments dlzero_height {A} A0 {r c}.
Arguments dlzero_width {A} A0 {r c}.



(* ======================================================================= *)
(** ** dlist unit, like a identity matrix *)
Section dlunit.

  Variable A : Type.
  Variable A0 A1 : A.
  
  (** Build a identity matrix with list list. *)
  (* there are 4 parts of a dlunit [n x n]: 
      left top element [1 x 1], 
      right top list [1 x (n-1)], 
      left bottom list [(n-1) x 1],
      right bottom square is another small dlunit [(n-1) x (n-1)] *)
  Fixpoint dlunit (n : nat) : list (list A) :=
    match n with
    | O => []
    | S n0 => (A1 :: (repeat A0 n0)) :: (consc (repeat A0 n0) (dlunit n0))
    end.
  
  (** dlunit height law *)
  Lemma dlunit_height : forall n, length (dlunit n) = n.
  Proof.
    induction n; simpl; auto. f_equal.
    rewrite consc_height with (r:=n); auto. apply repeat_length.
  Qed.
  
  (** dlunit width law *)
  Lemma dlunit_width : forall n, width (dlunit n) n.
  Proof.
    induction n; simpl; auto. split.
    - f_equal. apply repeat_length.
    - apply consc_width; auto. rewrite repeat_length, dlunit_height; auto.
  Qed.
  
End dlunit.

Arguments dlunit {A}.
Arguments dlunit_height {A} A0 A1 {n}.
Arguments dlunit_width {A} A0 A1 {n}.



(* ======================================================================= *)
(** ** transpose a dlist *)
Section dltrans.
  
  Variable A : Type.
  Variable A0 A1 : A.
  
  (** Transposition of a dlist *)
  (* Idea: fetch row as column one bye one, generate a dlist with c rows if 
      given c is <= column of input dlist.
    Note that, we give c to support dlist_0_c situation.
    eg: 
      [] 3 => [[];[];[]]
      [[];[];[]] 0 => []
  *)
  Fixpoint dltrans (dl : list (list A)) (c : nat) : list (list A) :=
    match dl with
    | [] => @dnil A c
    | l :: tl => consc l (dltrans tl c)
    end.
  
  (** dltrans height law *)
  Lemma dltrans_height : forall dl c, 
    width dl c ->
    length (dltrans dl c) = c.
  Proof. induction dl; intros; simpl; auto.
    - rewrite dnil_height. auto.
    - inversion H. rewrite consc_height with (r:=c); auto.
  Qed.
 
  (** dltrans width law *)
  Lemma dltrans_width : forall dl r c, 
    length dl = r -> width dl c -> width (dltrans dl c) r.
  Proof.
    induction dl; intros; simpl in *; auto.
    - induction c; simpl in *; auto.
    - rewrite <- H. destruct H0. apply consc_width.
      2:{ apply IHdl; auto. }
      rewrite dltrans_height; auto.
  Qed.
  
  (** dltrans dnil = [] *)
  Lemma dltrans_nil : forall n, dltrans (dnil n) 0 = [].
  Proof. intros. destruct n; auto. Qed.
  
  (** dltrans consr = consc dltrans *)
  Lemma dltrans_consr : forall dl l c,
    dltrans (l :: dl) c = consc l (dltrans dl c).
  Proof. intros. simpl. auto. Qed.
  
  (** dltrans consc = consr dltrans *)
  Lemma dltrans_consc : forall dl l r c,
    length l = r -> length dl = r -> width dl c ->
    dltrans (consc l dl) (S c) = l :: (dltrans dl c).
  Proof.
    induction dl; simpl; intros; auto.
    - induction l; auto. subst. inversion H0.
    - destruct H1. induction l.
      + subst. inversion H0.
      + rewrite consc_decompose. rewrite <- (consc_decompose a0 a).
        rewrite <- IHdl with (r:=pred r); auto; subst; simpl; auto.
  Qed.
  
  (** dltrans twice return back *)
  Lemma dltrans_trans : forall dl r c,
    length dl = r -> width dl c ->
      dltrans (dltrans dl c) r = dl.
  Proof.
    induction dl; simpl; intros.
    - destruct c; simpl; auto. subst. auto.
    - destruct H0. rewrite <- H. rewrite dltrans_consc with (r:=c); auto.
      + f_equal. auto.
      + rewrite dltrans_height; auto.
      + apply dltrans_width; auto.
  Qed.
    
  (** dltrans dlzero<r,c> = dlzero<c,r> *)
  Lemma dltrans_zero : forall r c,
    dltrans (dlzero A0 r c) c = dlzero A0 c r.
  Proof.
    induction r; intros; simpl; auto. rewrite dlzero_dnil; auto.
    unfold dlzero in *; simpl in *. rewrite IHr.
    rewrite repeat_consr. auto.
  Qed.
    
  (** transpose dlunit keep unchanged *)
  Lemma dltrans_dlunit : forall n, 
    let u := dlunit A0 A1 n in
      dltrans u n = u.
  Proof.
    simpl. induction n; auto. simpl.
    rewrite dltrans_consc with (r:=n); auto; try apply repeat_length; 
    try apply dlunit_height; try apply dlunit_width; auto. rewrite IHn; auto.
  Qed.
  
End dltrans.

Arguments dltrans {A}.
Arguments dltrans_height {A}.
Arguments dltrans_width {A}.
Arguments dltrans_trans {A}.



(* ======================================================================= *)
(** ** map of dlist with f : A -> B *)
Section LLMap_A_B.
  
  Variable A B : Type.
  Variable f : A -> B.
  
  (** map operation to dlist *)
  Definition dmap dl := map (map f) dl.

  (** dmap height law *)
  Lemma dmap_height : forall dl, length (dmap dl) = length dl.
  Proof. induction dl; simpl; auto. Qed.
  
  (** dmap width law *)
  Lemma dmap_width : forall dl n, 
    width dl n <-> width (dmap dl) n.
  Proof. 
    induction dl; simpl; auto; intros; try tauto. split.
    - intros [H1 H2]. split. rewrite map_length; auto. apply IHdl. auto.
    - intros [H1 H2]. rewrite map_length in H1. apply IHdl in H2. tauto.
  Qed.
  
  (** dmap effect equal to map to first head and dmap to tail rows *) 
  Lemma dmap_cons : forall l dl, dmap (l :: dl) = (map f l) :: (dmap dl).
  Proof. intros. simpl. auto. Qed.
  
  (** dmap distributive law by append *)
  Lemma dmap_app : forall dl1 dl2,
    dmap (dl1 ++ dl2) = (dmap dl1) ++ (dmap dl2).
  Proof. induction dl1,dl2; simpl; auto; rewrite IHdl1; auto. Qed.
  
  (** dmap dnil = dnil *)
  Lemma dmap_dnil : forall n, 
    dmap (dnil n) = dnil n.
  Proof. induction n; simpl; auto. rewrite IHn. auto. Qed.
  
End LLMap_A_B.

Arguments dmap {A B}.



(* ======================================================================= *)
(** ** map of dlist with f : A -> A *)
Section LLMap_A_A.
  Variable A : Type.
  Variable A0 : A.
  
  (** dmap (fun x => A0) dl = dlzero A0 r c *)
  Lemma dmap_to0_eq_dlzero : forall {r c} dl (H1 : length dl = r)
    (H2 : width dl c) , 
    @dmap A A (fun x => A0) dl = dlzero A0 r c.
  Proof.
    unfold dmap, dlzero.
    induction r; intros; simpl.
    - apply length_zero_iff_nil in H1.
      subst. compute. auto.
    - destruct dl.
      + simpl in *; lia.
      + simpl. f_equal; auto. destruct H1,H2.
        * rewrite lzero_eq_map_to_zero with (l:=l); auto.
        * apply IHr; auto. destruct H2; auto.
  Qed.
  
End LLMap_A_A.



(* ======================================================================= *)
(** ** map2 of dlist *)
Section dmap2.
  
  Variable A B C : Type.
  Variable f : A -> B -> C.
  
  (** map operation to two dlists *)
  Definition dmap2 dl1 dl2 := map2 (map2 f) dl1 dl2.
  
  (** dmap2 height law *)
  Lemma dmap2_height : forall dl1 dl2,
    length dl1 = length dl2 -> length (dmap2 dl1 dl2) = length dl1.
  Proof. induction dl1,dl2; simpl; auto. Qed.
  
  (** dmap2 width law *)
  Lemma dmap2_width : forall dl1 dl2 n,
    width dl1 n -> width dl2 n -> width (dmap2 dl1 dl2) n.
  Proof. 
    induction dl1,dl2; simpl; auto. intros. destruct H,H0. split.
    - apply map2_length; auto.
    - apply IHdl1; auto.
  Qed.
  
  (** dmap2 and consr *)
  Lemma dmap2_consr : forall dl1 dl2 l1 l2,
    dmap2 (l1 :: dl1) (l2 :: dl2) = 
    (map2 f l1 l2) :: (dmap2 dl1 dl2).
  Proof. intros. simpl. auto. Qed.
  
  (** dmap2 and consc *)
  Lemma dmap2_consc : forall l1 dl1 l2 dl2 r c t,
    length l1 = r -> length dl1 = r -> width dl1 c ->
    length l2 = t -> length dl2 = t -> width dl2 c ->
    dmap2 (consc l1 dl1) (consc l2 dl2) = 
    consc (map2 f l1 l2) (dmap2 dl1 dl2).
  Proof.
    induction l1,dl1,l2,dl2; simpl; intros; auto. f_equal.
    destruct H1,H4. apply IHl1 with (r:=pred r) (c:=c) (t:=pred t); subst; auto.
  Qed.
  
  (** dmap2 and add *)
  Lemma dmap2_app : forall dla1 dla2 dlb1 dlb2,
    length dla1 = length dlb1 ->
    length dla2 = length dlb2 ->
    dmap2 (dla1 ++ dla2) (dlb1 ++ dlb2) = 
    (dmap2 dla1 dlb1) ++ (dmap2 dla2 dlb2).
  Proof. intros. unfold dmap2. apply map2_app; auto. Qed.
  
  (** dmap2 dnil dl = dnil *)
  Lemma dmap2_dnil_l : forall dl n,
    length dl = n ->
    dmap2 (dnil n) dl = dnil n.
  Proof. intros. unfold dmap2. rewrite map2_dnil_l; auto. Qed.
  
  Lemma dmap2_tail : forall dl1 dl2,
    length dl1 = length dl2 ->
    tl (dmap2 dl1 dl2) = dmap2 (tl dl1) (tl dl2).
  Proof. intros. unfold dmap2. apply tail_map2_dlist. Qed.

  (** Relationship between dltrans and dmap2 *)
  Lemma dltrans_dmap2 : forall dl1 dl2 r c,
    length dl1 = r -> length dl2 = r -> width dl1 c -> width dl2 c ->
    dltrans (dmap2 dl1 dl2) c = 
    dmap2 (dltrans dl1 c) (dltrans dl2 c).
  Proof.
    induction dl1,dl2; simpl; intros; auto.
    - rewrite dmap2_dnil_l; auto; apply dnil_height.
    - subst. inversion H0.
    - subst. inversion H0.
    - destruct H1, H2.
      rewrite IHdl1 with (r:=pred r) (c:=c); auto.
      + rewrite dmap2_consc with (r:=c) (c:=pred r) (t:=c); auto;
        try apply dltrans_height; try apply dltrans_width; subst; auto.
      + subst; auto.
      + subst; auto.
  Qed.
  
End dmap2.

Arguments dmap2 {A B C}.



(* ======================================================================= *)
(** ** dmap2 with same base type *)
Section dmap2_sametype.

  Variable A : Type.
  Variable f : A -> A -> A.
  Infix "+" := f.
  Variable f_comm : forall a b, a + b = b + a.
  Variable f_assoc : forall a b c, (a + b) + c = a + (b + c).
  
  (** dl1 . dl2 = dl2 . dl1 *)
  Lemma dmap2_comm : forall (dl1 dl2 : list (list A)),
    dmap2 f dl1 dl2 = dmap2 f dl2 dl1.
  Proof.
    induction dl1,dl2; simpl; auto. f_equal; auto. apply map2_comm. auto. 
  Qed.
  
  (** (dl1 . dl2) . dl3 = dl1 . (dl2 . dl3) *)
  Lemma dmap2_assoc : forall (dl1 dl2 dl3 : list (list A)),
    dmap2 f (dmap2 f dl1 dl2) dl3 = 
    dmap2 f dl1 (dmap2 f dl2 dl3).
  Proof.
    induction dl1,dl2,dl3; simpl; auto. f_equal; auto. apply map2_assoc.
    auto. 
  Qed.
  
  (** dmap2 with dmap of two components *)
  Lemma dmap2_dmap_dmap : forall (f1 f2 g : A -> A) (h : A -> A -> A) 
    (H : forall x, g x = h (f1 x) (f2 x)) l,
    dmap2 h (dmap f1 l) (dmap f2 l) = dmap g l.
  Proof.
    induction l; simpl; auto. rewrite IHl. f_equal. apply map2_map_map.
    auto.
  Qed.
  
  (** dmap2 over dmap is homorphism *)
  Lemma dmap2_dmap_hom : forall (f : A -> A) (g : A -> A -> A) 
    (H : forall x1 x2, f (g x1 x2) = g (f x1) (f x2)) d1 d2,
    dmap2 g (dmap f d1) (dmap f d2) = dmap f (dmap2 g d1 d2).
  Proof.
    induction d1,d2; auto. simpl. rewrite IHd1. f_equal.
    rewrite map2_map_hom; auto.
  Qed.
  
End dmap2_sametype.



(* ======================================================================= *)
(** ** Square Zero dlist *)
Section sdlzero.

  Variable A : Type.
  Variable A0 : A.
  
  (** Square dlist with element zero *)
  Definition sdlzero n := repeat (repeat A0 n) n.
  
  (** dim(sdl0) = rows(dl0) = cols(dl0) -> sdl0 = dl0 *)
  Lemma sdlzero_eq_dlzero_r : forall r c,
    r = c -> sdlzero r = dlzero A0 r c.
  Proof. intros. subst. unfold sdlzero, dlzero. f_equal. Qed.
  
  (** dim(sdl0) = rows(dl0) = cols(dl0) -> sdl0 = dl0 *)
  Lemma sdlzero_eq_dlzero_c : forall r c,
    r = c -> sdlzero c = dlzero A0 r c.
  Proof. intros. subst. unfold sdlzero, dlzero. f_equal. Qed.
  
  (** height(sdl0) = dim(sdl0) *)
  Lemma sdlzero_height : forall n, length (sdlzero n) = n.
  Proof. intros. apply repeat_length. Qed.
  
  (** width(sdl0) = dim(sdl0) *)
  Lemma sdlzero_width : forall n, width (sdlzero n) n.
  Proof.
    intros. unfold sdlzero. induction n. simpl; auto.
    apply repeat_width. apply repeat_length.
  Qed.
  
End sdlzero.



(* ======================================================================= *)
(** ** dmap2 is considered as dladd *)
Section dladd.

  Variable A : Type.
  Variable A0 : A.
  Variable add : A -> A -> A.
  Infix "+" := add.
  Variable add_comm : forall a b, a + b = b + a.
  Variable add_0_l : forall a, A0 + a = a.
  
  (** dl + 0 = dl *)
  Lemma dladd_zero_l : forall dl r c, 
    length dl = r -> width dl c ->
    dmap2 add (dlzero A0 r c) dl = dl.
  Proof.
    induction dl; simpl; intros.
    - unfold dmap2. apply map2_nil_r.
    - induction r. inversion H. inversion H. destruct H0. simpl.
      unfold dlzero in *. f_equal; auto.
      apply ladd_zero_l; auto.
  Qed.
  
  (** 0 + dl = dl *)
  Lemma dladd_zero_r : forall dl r c, 
    length dl = r -> width dl c ->
    dmap2 add dl (dlzero A0 r c) = dl.
  Proof.
    intros. rewrite dmap2_comm; auto. apply dladd_zero_l; auto.
  Qed.

End dladd.



(* ======================================================================= *)
(** ** dmap2 is considered as dlsub *)
Section dlsub.

  Variable A : Type.
  Variable A0 : A.
  Variable opp : A -> A.
  Variable add : A -> A -> A.
  Infix "+" := add.
  Notation "- a" := (opp a).
  Definition sub a b := (a + (-b)).
  Infix "-" := sub.
  
  Variable sub_comm : forall a b, a - b = - (b - a).
  Variable sub_perm : forall a b c, (a - b) - c = (a - c) - b.
  Variable sub_assoc : forall a b c, (a - b) - c = a - (b + c).
  Variable sub_0_l : forall a, A0 - a = - a.
  Variable sub_0_r : forall a, a - A0 = a.
  Variable sub_self : forall a, a - a = A0.
  
  (** dl1 - dl2 = - (dl2 - dl1) *)
  Lemma dlsub_comm : forall dl1 dl2 c, 
    length dl1 = length dl2 ->
    width dl1 c -> width dl2 c ->
    dmap2 sub dl1 dl2 = dmap opp (dmap2 sub dl2 dl1).
  Proof.
    induction dl1,dl2; simpl; intros; auto. f_equal; auto.
    - apply lsub_comm; auto.
    - destruct H0,H1. apply IHdl1 with (c:=c); auto.
  Qed.
  
  (** (dl1 - dl2) - dl3 = dl1 - (dl2 + dl3) *)
  Lemma dlsub_assoc2 : forall dl1 dl2 dl3 r c, 
    length dl1 = r -> length dl2 = r -> length dl3 = r ->
    width dl1 c -> width dl2 c ->
    dmap2 sub (dmap2 sub dl1 dl2) dl3 = 
    dmap2 sub dl1 (dmap2 add dl2 dl3).
  Proof.
    induction dl1,dl2,dl3; simpl; intros; auto. f_equal; auto.
    - apply lsub_assoc2; auto.
    - destruct H2,H3. destruct r; inversion H. 
      apply IHdl1 with (r:=r) (c:=c); auto.
  Qed.
  
  (** 0 - dl = - dl *)
  Lemma dlsub_zero_l : forall dl r c, 
    length dl = r -> width dl c ->
    dmap2 sub (dlzero A0 r c) dl =
    dmap opp dl.
  Proof.
    induction dl; simpl; intros.
    - unfold dmap2. apply map2_nil_r.
    - induction r. inversion H. inversion H. destruct H0. simpl.
      unfold dlzero in *. f_equal; auto.
      apply lsub_zero_l; auto.
  Qed.
  
  (** dl - 0 = dl *)
  Lemma dlsub_zero_r : forall dl r c, 
    length dl = r -> width dl c ->
    dmap2 sub dl (dlzero A0 r c) = dl.
  Proof.
    induction dl; simpl; intros; auto. destruct r; simpl. inversion H.
    inversion H. destruct H0. f_equal; auto.
    apply lsub_zero_r; auto. apply IHdl; auto.
  Qed.
  
  (** dl - dl = 0 *)
  Lemma dlsub_self : forall dl r c, 
    length dl = r -> width dl c ->
    dmap2 sub dl dl = (dlzero A0 r c).
  Proof.
    induction dl; simpl; intros; subst; auto. destruct H0.
    unfold dlzero in *. simpl. f_equal.
    apply lsub_self; auto. apply IHdl; auto.
  Qed.

End dlsub.



(* ======================================================================= *)
(** ** list dot dlist *)
Section ldotdl.

  Variable A : Type.
  Variable A0 A1 : A.
  Variable add mul : A -> A -> A.
  Infix "+" := add.
  Infix "*" := mul.
  Variable add_comm : forall a b, a + b = b + a.
  Variable mul_comm : forall a b, a * b = b * a.
  Variable add_assoc : forall a b c, (a + b) + c = a + (b + c).
  Variable mul_assoc : forall a b c, (a * b) * c = a * (b * c).
  Variable mul_add_distr_l : forall a b1 b2, a * (b1 + b2) = a * b1 + a * b2.
  Variable mul_add_distr_r : forall a1 a2 b, (a1 + a2) * b = (a1 * b) + (a2 * b).
  Variable add_0_l : forall a, A0 + a = a.
  Variable mul_0_l : forall a, A0 * a = A0.
  Variable mul_1_l : forall a, A1 * a = a.
  
  (* a convenient notation in this section *)
  Notation ldot := (ldot A0 add mul).
  
  (** list dot product to dlist *)
  Fixpoint ldotdl (l : list A) (dl : list (list A)) : list A :=
    match dl with
    | h :: t => (ldot l h) :: (ldotdl l t)
    | [] => []
    end.
  
  (** ldotdl length law *)
  Lemma ldotdl_length : forall l dl r c,
    length l = c -> length dl = r -> width dl c ->
    length (ldotdl l dl) = r.
  Proof.
    intros l dl. gd l. induction dl; simpl; intros; auto.
    destruct H1. rewrite IHdl with (r:=pred r) (c:=c); auto; subst; auto.
  Qed.
  
  (** ldotdl left distributve over map2 *)
  Lemma ldotdl_map2_distr_l : forall dl l1 l2 {r c},
    length l1 = r -> length l2 = r -> length dl = c -> width dl r ->
    ldotdl (map2 add l1 l2) dl = 
    map2 add (ldotdl l1 dl) (ldotdl l2 dl).
  Proof.
    induction dl; intros; simpl; auto. f_equal; simpl in *; destruct H2.
    - rewrite ldot_map2_distr_l with (r:=r); auto.
    - apply IHdl with (r:=r) (c:=pred c); auto. subst. auto.
  Qed.
  
  (** ldotdl right distributve over dmap2 *)
  Lemma ldotdl_dmap2_distr_r : forall l dl1 dl2 {r c},
    length l = c -> length dl1 = r -> length dl2 = r -> 
    width dl1 c -> width dl2 c ->
    ldotdl l (dmap2 add dl1 dl2) = 
    map2 add (ldotdl l dl1) (ldotdl l dl2).
  Proof.
    induction dl1,dl2; simpl; intros; auto. destruct H2,H3. f_equal; simpl.
    - rewrite ldot_map2_distr_r with (r:=c); auto.
    - apply IHdl1 with (r:=pred r) (c:=c); subst; auto.
  Qed.
  
  (** ldotdl left with nil *)
  Lemma ldotdl_nil_l : forall dl r,
    length dl = r -> ldotdl [] dl = lzero A0 r.
  Proof.
    induction dl; simpl; intros; auto. subst; auto.
    rewrite ldot_nil_l. rewrite IHdl with (r:=pred r); subst; auto.
  Qed.
  
  (** ldotdl right with nil *)
  Lemma ldotdl_nil_r : forall r l, ldotdl l (dnil r) = lzero A0 r.
  Proof.
    induction r; simpl; intros; auto. rewrite IHr. f_equal.
    rewrite ldot_nil_r; auto.
  Qed.
  
  (** ldotdl left with zero *)
  Lemma ldotdl_zero_l : forall dl r c,
    length dl = r -> width dl c ->
    ldotdl (lzero A0 c) dl = lzero A0 r.
  Proof.
    induction dl; simpl; intros; auto.
    - subst; auto.
    - destruct H0. rewrite IHdl with (r:=pred r); subst; simpl; auto.
      rewrite ldot_zero_l; auto.
  Qed.
  
  (** ldotdl right with zero *)
  Lemma ldotdl_zero_r : forall l r c,
    length l = c ->
    ldotdl l (dlzero A0 r c) = lzero A0 r.
  Proof.
    induction r; simpl; intros; auto. f_equal; try apply IHr; auto.
    apply ldot_zero_r; auto.
  Qed.
  
  (** ldotdl of consr and consc *)
  Lemma ldotdl_consr_consc : forall l2 dl2 l1 x1 r c,
    length l2 = c -> length dl2 = c -> width dl2 r ->
    ldotdl (x1 :: l1) (consc l2 dl2) = 
    ladd add (lcmul mul x1 l2) (ldotdl l1 dl2).
  Proof.
    induction l2, dl2; simpl; intros; auto. destruct H1.
    rewrite <- IHl2 with (r:=r) (c:=pred c); subst; auto.
  Qed.

  (** ldot and ldotdl could swap first two operands.
    l1 . (l2 . dl) = l2 . (l1 . dl^T) *)
  Lemma ldot_ldotdl_swap12 : forall dl l1 l2 r c,
    length l1 = r -> length l2 = c -> length dl = r -> width dl c ->
    ldot l1 (ldotdl l2 dl) = 
    ldot l2 (ldotdl l1 (dltrans dl c)).
  Proof.
    induction dl,l1; simpl; intros; auto.
    - rewrite ldotdl_nil_l with (r:=c); try apply dnil_height.
      rewrite ldot_zero_r; auto.
    - subst. inversion H1.
    - subst. inversion H1.
    - destruct H2. rewrite ldot_cons.
      rewrite IHdl with (r:=pred r) (c:=c); auto;
      [idtac | subst; auto | subst; auto].
      rewrite ldotdl_consr_consc with (r:=pred r) (c:=c); auto;
      [idtac | apply dltrans_height | apply dltrans_width; subst]; auto.
      rewrite ldot_ladd_distr_l with (r:=c); auto.
      + f_equal. apply eq_sym. rewrite ldot_comm; auto.
        rewrite ldot_lcmul_distr_r; auto. f_equal.
        apply ldot_comm; auto.
      + apply lcmul_length; auto.
      + apply ldotdl_length with (c:=pred r); auto;
        [idtac | apply dltrans_height | apply dltrans_width]; subst; auto.
  Qed.

  (** ldotdl with consr at right operend *)
  Lemma ldotdl_consr_r : forall l1 l2 dl2 r c,
    length l1 = r -> length l2 = r -> length dl2 = c -> width dl2 r ->
    ldotdl l1 (l2 :: dl2) = (ldot l1 l2) :: (ldotdl l1 dl2).
  Proof. induction l1,l2,dl2; simpl; intros; auto. Qed.
  
  (** ldotdl right distributive over ladd.
    (l1 + l2) . dl = l1 . dl + l2.dl *)
  Lemma ldotdl_ladd_distr_r : forall l1 l2 dl r c,
    length l1 = r -> length l2 = r -> length dl = c -> width dl r ->
    ldotdl (ladd add l1 l2) dl = 
    ladd add (ldotdl l1 dl) (ldotdl l2 dl).
  Proof.
    induction dl; simpl; intros; auto. destruct H2.
    rewrite IHdl with (r:=r) (c:=pred c); auto.
    - f_equal. rewrite ldot_ladd_distr_r with (r:=r); auto.
    - subst; auto.
  Qed.
  
  (** ldotdl with lcmul is assocociative.
    cmul a (dot l dl) = dot (cmul a l) dl *)
  Lemma ldotdl_lcmul_assoc : forall dl a l r c,
    length l = r -> length dl = c -> width dl r ->
    lcmul mul a (ldotdl l dl) = ldotdl (lcmul mul a l) dl.
  Proof.
    induction dl; simpl; intros; auto. destruct H1.
    rewrite IHdl with (r:=r) (c:=pred c); auto. f_equal.
    rewrite ldot_lcmul_distr_r; auto. subst; auto.
  Qed.
  
  (** a * (x :: l) = (a * x) :: (a * l) *)
  Lemma lcmul_cons : forall a x l,
    lcmul mul a (x :: l) = (mul a x) :: (lcmul mul a l).
  Proof. intros. auto. Qed.
  
  (** a * 0 = 0 *)
  Lemma lcmul_zero_r : forall a n, lcmul mul a (lzero A0 n) = lzero A0 n.
  Proof.
    intros. unfold lcmul. rewrite map_repeat. unfold lzero. f_equal; auto.
    rewrite mul_comm, mul_0_l; auto.
  Qed.
  
  (** l dotdl E = l *)
  Lemma ldotdl_dlunit : forall l {n},
    length l = n -> ldotdl l (dlunit A0 A1 n) = l.
  Proof.
    induction l; simpl; intros; auto.
    - subst. simpl. auto.
    - remember (length l) as m. rewrite <- H. simpl.
      rewrite ldotdl_consr_consc with (r:=m) (c:=m); auto;
      try apply repeat_length; try apply dlunit_height; try apply dlunit_width.
      rewrite IHl; auto. f_equal.
      + rewrite ldot_cons. rewrite ldot_zero_r; auto.
        rewrite mul_comm, mul_1_l, add_comm, add_0_l; auto.
      + rewrite lcmul_zero_r. rewrite ladd_zero_l; auto.
  Qed.
  
End ldotdl.

Arguments ldotdl {A}.



(* ======================================================================= *)
(** ** dlist dot dlist *)
Section dldotdl.

  Variable A : Type.
  Variable A0 A1 : A.
  Variable cmul : A -> A.
  Variable cmul_0 : cmul A0 = A0.
  Variable add mul : A -> A -> A.
  Infix "+" := add.
  Infix "*" := mul.
  
  Variable add_comm : forall a b, a + b = b + a.
  Variable mul_comm : forall a b, a * b = b * a.
  Variable add_assoc : forall a b c, (a + b) + c = a + (b + c).
  Variable mul_assoc : forall a b c, (a * b) * c = a * (b * c).
  Variable mul_add_distr_l : forall a b1 b2, a * (b1 + b2) = a * b1 + a * b2.
  Variable mul_add_distr_r : forall a1 a2 b, (a1 + a2) * b = (a1 * b) + (a2 * b).
  Variable add_0_l : forall a, A0 + a = a.
  Variable add_0_r : forall a, a + A0 = a.
  Variable mul_0_l : forall a, A0 * a = A0.
  Variable mul_0_r : forall a, a * A0 = A0.
  Variable mul_1_l : forall a, A1 * a = a.
  Variable mul_1_r : forall a, a * A1 = a.
  
  (* a convenient notation in this section *)
  Notation ldot := (ldot A0 add mul).
  Notation ldotdl := (ldotdl A0 add mul).
  
  (** dlist dot product *)
  Fixpoint dldotdl (dl1 dl2 : list (list A)) : list (list A) :=
    match dl1 with
    | h1 :: t1 => (ldotdl h1 dl2) :: (dldotdl t1 dl2)
    | [] => []
    end.
  
  (** dldotdl height law *)
  Lemma dldotdl_height : forall dl1 dl2 r1 r2 c,
    length dl1 = r1 -> length dl2 = r2 -> width dl1 c -> width dl2 c ->
    length (dldotdl dl1 dl2) = r1.
  Proof.
    induction dl1; intros; auto. simpl in *. inversion H1.
    rewrite IHdl1 with (r1:=pred r1) (r2:=r2) (c:=c); auto; subst; auto.
  Qed.
  
  (** dldotdl width law *)
  Lemma dldotdl_width : forall dl1 dl2 r1 r2 c,
    length dl1 = r1 -> length dl2 = r2 -> width dl1 c -> width dl2 c ->
    width (dldotdl dl1 dl2) r2.
  Proof.
    induction dl1; intros; auto. simpl in *. destruct H1. split.
    - rewrite ldotdl_length with (r:=r2) (c:=c); auto.
    - apply IHdl1 with (r1:=pred r1) (r2:=r2) (c:=c); auto; subst; auto.
  Qed.
  
  (** dldotdl consr left *)
  Lemma dldotdl_consr_l : forall l1 dl1 dl2,
    dldotdl (l1 :: dl1) dl2 = (ldotdl l1 dl2) :: (dldotdl dl1 dl2). 
  Proof. simpl. auto. Qed.
  
  (** dldotdl consr right *)
  Lemma dldotdl_consr_r : forall dl1 l2 dl2 r c t,
    length dl1 = r -> width dl1 c ->
    length l2 = c ->
    length dl2 = t -> width dl2 c ->
    dldotdl dl1 (l2 :: dl2) = consc (ldotdl l2 dl1) (dldotdl dl1 dl2).
  Proof.
    induction dl1; simpl; intros; auto. destruct H0. f_equal.
    - f_equal. apply ldot_comm; auto.
    - apply IHdl1 with (r:=pred r) (c:=c) (t:=t); subst; auto.
  Qed.
  
  (** dldotdl left distributve over dmap2 *)
  Lemma dldotdl_dmap2_distr_l : forall dl1 dl2 dl3 {r c t},
    length dl1 = r -> length dl2 = r -> length dl3 = t -> 
    width dl1 c -> width dl2 c -> width dl3 c -> 
    dldotdl (dmap2 add dl1 dl2) dl3 = 
    dmap2 add (dldotdl dl1 dl3) (dldotdl dl2 dl3).
  Proof.
    induction dl1,dl2; simpl; intros; auto. f_equal;simpl in *;destruct H2,H3.
    - rewrite ldotdl_map2_distr_l with (r:=c) (c:=t); auto.
    - apply IHdl1 with (r:=pred r) (c:=c) (t:=t); subst; auto.
  Qed.
  
  (** dldotdl right distributve over dmap2 *)
  Lemma dldotdl_dmap2_distr_r : forall dl1 dl2 dl3 {r c t},
    length dl1 = r -> length dl2 = t -> length dl3 = t -> 
    width dl1 c -> width dl2 c -> width dl3 c -> 
    dldotdl dl1 (dmap2 add dl2 dl3) = 
    dmap2 add (dldotdl dl1 dl2) (dldotdl dl1 dl3).
  Proof.
    induction dl1; simpl; intros; auto. destruct H2. f_equal. 
    - apply ldotdl_dmap2_distr_r with (r:=t) (c:=c); auto.
    - apply IHdl1 with (r:=pred r) (c:=c) (t:=t); subst; auto.
  Qed.
  
  (** dldotdl left with nil *)
  Lemma dldotdl_nil_r : forall dl r c, 
    length dl = r -> width dl c -> dldotdl dl [] = dnil r.
  Proof.
    induction dl; simpl; intros; simpl; auto. subst; auto.
    rewrite <- H. simpl. f_equal. destruct H0.
    rewrite IHdl with (r:=pred r) (c:=c); subst; auto.
  Qed.
  
  (** dldotdl left with zero dlist *)
  Lemma dldotdl_zero_l : forall r dl c t,
    length dl = t -> width dl c ->
    dldotdl (dlzero A0 r c) dl = dlzero A0 r t.
  Proof.
    induction r; simpl; intros; auto. unfold dlzero in *. simpl. 
    f_equal; auto. rewrite ldotdl_zero_l with (r:=t); auto.
  Qed.
  
  (** dldotdl right with zero dlist *)
  Lemma dldotdl_zero_r : forall dl r c t,
    length dl = r -> width dl c ->
    dldotdl dl (dlzero A0 t c) = dlzero A0 r t.
  Proof.
    induction dl; simpl; intros; auto.
    - subst; auto.
    - destruct H0. rewrite IHdl with (r:=pred r); auto.
      + rewrite ldotdl_zero_r; auto. unfold dlzero in *. subst. simpl.
        f_equal.
      + subst; auto.
  Qed.
  
  (** dltrans for dldotdl with right decomposition *)
  Lemma dltrans_dldotdl_right : forall d1 d2 l2 r c t,
    length d1 = r -> width d1 c ->
    length l2 = c ->
    length d2 = t -> width d2 c ->
    dltrans (dldotdl d1 (l2 :: d2)) (S t) =
    (ldotdl l2 d1) :: (dltrans (dldotdl d1 d2) t).
  Proof.
    induction d1,d2; simpl; intros; auto.
    - destruct H0. rewrite IHd1 with (r:=pred r) (c:=c); auto. 
      f_equal. f_equal. apply ldot_comm; auto. subst; auto.
    - destruct H0,H3. rewrite IHd1 with (r:=pred r) (c:=c); auto.
      f_equal. f_equal. apply ldot_comm; auto.
      subst; auto. simpl. split; auto.
  Qed. 
  
  (** dldotdl commutation *)
  Lemma dldotdl_comm : forall d1 d2 r c t,
    length d1 = r -> width d1 c ->
    length d2 = t -> width d2 c ->
    dldotdl d1 d2 = dltrans (dldotdl d2 d1) r.
  Proof.
    induction d1; simpl; intros.
    - rewrite dldotdl_nil_r with (r:=t) (c:=c); auto.
      rewrite <- H. rewrite dltrans_nil. auto.
    - destruct H0. rewrite IHd1 with (r:=pred r) (c:=c) (t:=t); auto.
      + rewrite <- H. 
        rewrite dltrans_dldotdl_right with (r:=t) (c:=c); auto.
      + subst; auto.
  Qed.
  
  (** l * (d1 . d2)^T = (l . d1^T) . d2 *)
  (** HARD *)
  Lemma ldotdl_dldotdl_dltrans_assoc : forall d1 d2 l {r c t},
    length l = r ->
    length d1 = r -> width d1 c ->
    length d2 = t -> width d2 c ->
    ldotdl l (dltrans (dldotdl d1 d2) t) =
    ldotdl (ldotdl l (dltrans d1 c)) d2.
  Proof.
    induction d1,d2; intros; auto.
    - subst. auto.
    - simpl. destruct H3. repeat rewrite ldotdl_nil_r. 
      rewrite ldot_zero_l; auto.
      rewrite ldotdl_zero_l with (r:=pred t); subst; auto.
    - simpl dltrans at 2. simpl in H0,H1,H2,H3. destruct H1,H3. destruct l0.
      + rewrite ldotdl_nil_l with (r:=t).
        * rewrite ldotdl_nil_l with (r:=c).
          { rewrite ldotdl_zero_l with (r:=t); simpl; auto. }
          { rewrite consc_height with (r:=c); auto.
            apply dltrans_height; auto. }
        * apply dltrans_height.
          apply dldotdl_width with (r1:=r) (c:=c); simpl; auto.
      + simpl in H. rewrite ldotdl_consr_consc with (r:=pred r) (c:=c); auto.
        (* (l1 + l2):dl = l1:dl + l2:dl *)
        rewrite ldotdl_ladd_distr_r with (r:=c) (c:=t); auto.
        { (* 1/6 *)
          rewrite <- IHd1 with (r:=pred r) (t:=t); auto.
          - rewrite dldotdl_consr_l.
            (* (l :: dl)^T = consc l (dl^T) *)
            replace (dltrans ((ldotdl a (l :: d2)) :: (dldotdl d1 (l :: d2))) t)
            with 
            (consc (ldotdl a (l::d2)) (dltrans (dldotdl d1 (l::d2)) t)); auto.
            rewrite ldotdl_consr_consc with (r:=pred r) (c:=t); auto.
            + f_equal. rewrite ldotdl_lcmul_assoc with (r:=c) (c:=t); auto.
              subst; simpl; auto.
            + rewrite ldotdl_length with (r:=t) (c:=c); simpl; auto.
            + apply dltrans_height.
              apply dldotdl_width with (r1:=pred r)(c:=c); simpl; subst; auto.
            + apply dltrans_width; auto.
              * rewrite dldotdl_height with (r1:=pred r)(r2:=t)(c:=c); 
                simpl; subst; auto.
              * apply dldotdl_width with (r1:=pred r)(c:=c); simpl; subst; auto.
          - subst; auto.
          - subst; auto.
          - simpl; auto. }
        { (* 2/6 *) apply lcmul_length; auto. }
        { (* 3/6 *) apply ldotdl_length with (c:=pred r); simpl; auto.
          - subst; auto.
          - apply dltrans_height; auto.
          - apply dltrans_width; subst; auto. }
        { (* 4/6 *) simpl; auto. }
        { (* 5/6 *) apply dltrans_height; auto. }
        { (* 6/6 *) apply dltrans_width; subst; auto. }
  Qed.
  
  (** dldotdl association *)
  Lemma dldotdl_assoc : forall d1 d2 d3 r c t s,
    length d1 = r -> width d1 c ->
    length d2 = c -> width d2 t ->
    length d3 = s -> width d3 t ->
    dldotdl (dldotdl d1 (dltrans d2 t)) d3 =
    dldotdl d1 (dltrans (dldotdl d2 d3) s).
  Proof.
    induction d1; simpl; intros; auto. destruct H0. f_equal; auto.
    rewrite ldotdl_dldotdl_dltrans_assoc with (r:=c) (c:=t); auto.
    apply IHd1 with (r:=pred r) (c:=c); subst; auto.
  Qed.
  
  (** dldotdl left with dlunit *)
  Lemma dldotdl_dlunit_l : forall (dl : list (list A)) {r c},
    length dl = r -> width dl c -> 
    dldotdl (dlunit A0 A1 c) dl = dltrans dl c.
  Proof.
    induction dl; simpl; intros; auto.
    - rewrite dldotdl_nil_r with (r:=c) (c:=c); auto.
      apply dlunit_height. apply dlunit_width.
    - destruct H0. 
      rewrite dldotdl_consr_r with (r:=c) (c:=c) (t:=pred r); auto;
      try apply dlunit_height; try apply dlunit_width.
      + rewrite IHdl with (r:=pred r); subst; auto.
        f_equal. rewrite ldotdl_dlunit; auto.
      + subst; auto.
  Qed.
  
  (** dldotdl right with dlunit *)
  Lemma dldotdl_dlunit_r : forall (dl : list (list A)) {r c},
    length dl = r -> width dl c -> 
    dldotdl dl (dlunit A0 A1 c) = dl.
  Proof.
    induction dl; simpl; intros; auto. destruct H0.
    rewrite IHdl with (r:=pred r); auto.
    - rewrite ldotdl_dlunit; auto.
    - subst; auto.
  Qed.
  
End dldotdl.

Arguments dldotdl {A}.



(* ======================================================================= *)
(** ** Properties of dlcmul *)
Section dlcmul_properties.

  Variable A : Type.
  Variable A0 A1 : A.
  Variable mul : A -> A -> A.
  Infix "*" := mul.
  Variable mul_comm : forall a b, a * b = b * a.
  Variable mul_0_l : forall a, A0 * a = A0.
  Variable Aeq_dec : forall a1 a2 : A, {a1 = a2} + {a1 <> a2}.
  Variable mul_1_l : forall a : A, A1 * a = a.
  Variable fmul_cancel_r : forall r1 r2 r : A, 
    r <> A0 -> r1 * r = r2 * r -> r1 = r2. 
  
  (** Mapping cmul to dlist keep unchanged imply k = 1 or dlist is zero *)
  Lemma dlcmul_fixpoint_imply_k1_or_dlzero : 
    forall {r c} k (dl : list (list A)) (H1 : length dl = r) (H2 : width dl c),
    map (map (fun x => mul k x)) dl = dl ->
    (k = A1 \/ dl = dlzero A0 r c).
  Proof.
    induction r; intros.
    - rewrite length_zero_iff_nil in H1. subst; auto.
    - destruct dl. easy. simpl in *.
      rewrite dlzero_Sr.
      inversion H1. destruct H2. apply cons_eq_iff in H. destruct H.
      assert (k = A1 \/ dl = dlzero A0 r c). { apply IHr; auto. }
      assert (k = A1 \/ l = lzero A0 c).
      { apply lcmul_fixpoint_imply_k1_or_lzero with (mul:=mul); auto. }
      destruct H5,H6; auto. right. rewrite H3. f_equal; auto.
  Qed.
  
  (** Mapping fmulc to dlist keep unchanged imply k = 1 or dlist is zero *)
  Lemma dlmulc_fixpoint_imply_k1_or_dlzero : 
    forall {r c} k (dl : list (list A)) (H1 : length dl = r) (H2 : width dl c),
    map (map (fun x => mul x k)) dl = dl ->
    (k = A1 \/ dl = dlzero A0 r c).
  Proof.
    (* use functional_extensionality will be easy, if you like! *)
    (* intros. apply dlcmul_fixpoint_imply_k1_or_dlzero; auto.
    rewrite <- H. f_equal; auto. f_equal.
    apply functional_extensionality. intros. auto. *)
    
    (* manually *)
    induction r; intros.
    - rewrite length_zero_iff_nil in H1. subst; auto.
    - destruct dl. easy. simpl in *.
      rewrite dlzero_Sr.
      inversion H1. destruct H2. apply cons_eq_iff in H. destruct H.
      assert (k = A1 \/ dl = dlzero A0 r c). { apply IHr; auto. }
      assert (k = A1 \/ l = lzero A0 c).
      { apply lmulc_fixpoint_imply_k1_or_lzero with (mul:=mul); auto. }
      destruct H5,H6; auto. right. rewrite H3. f_equal; auto.
  Qed.
 
End dlcmul_properties.


