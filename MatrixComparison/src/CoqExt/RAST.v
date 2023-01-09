(*
  purpose   : AST for R.
  author    : ZhengPu Shi
  date      : 2022.08
  
  motivation:
  为了在计算中化简实数表达式。
  比如逆矩阵的运算，得到了正确的结果，但存在冗余。
  所以需要借助一种AST来实现化简。
  
  remark    :
  1. A light-weight AST for R, and named to "T"
  2. it is inspired by Marisa Kirisame<lolisa@marisa.moe>.
*)


Require Export BasicConfig.

Require Export RExt.
Require Import String.


(* ######################################################################### *)
(** * AST for R *)

(** 实数运算化简自动化 *)
Global Hint Rewrite
  Rplus_0_l  (* 0 + r = r *)
  Rplus_0_r  (* r + 0 = r *)
  Rmult_0_l  (* 0 * r = 0 *)
  Rmult_0_r  (* r * 0 = 0 *)
  Rmult_1_l  (* 1 * r = r *)
  Rmult_1_r  (* r * 1 = r *)
  : real.

(** 新的作用域 *)
Declare Scope T_scope.
Delimit Scope T_scope with T.
Open Scope T_scope.


(** 定义实数的AST *)
Inductive T :=
| T0 | T1
| TLit (r : R)
| Tadd (r1 r2 : T) | Topp (r : T)
| Tmul (r1 r2 : T) | Tinv (r : T)
| Tfunc (f : string) (args : list T).

(* 邦定以后的好处是，如果在其他作用域中遇到 T 类型的变量，会自动使用上面的Notation *)
Bind Scope T_scope with T.

(** 利用基本定义实现的函数 *)
Definition Tsub a b := Tadd a (Topp b).
Definition Tdiv a b := Tmul a (Tinv b).

Notation "0" := T0 : T_scope.
Notation "1" := T1 : T_scope.
Infix "+" := Tadd : T_scope.
Infix "-" := Tsub : T_scope.
Infix "*" := Tmul : T_scope.
Infix "/" := Tdiv : T_scope.
Notation "- a" := (Topp a) : T_scope.
Notation "/ a" := (Tinv a) : T_scope.

(* 公理 *)
Axiom Tadd_0_l : forall x : T, 0 + x = x.
Axiom Tadd_comm : forall x y : T, x + y = y + x.
Axiom Tadd_assoc : forall x y z : T, x + (y + z) = (x + y) + z.
Axiom Tmul_1_l : forall x : T, 1 * x = x.
Axiom Tmul_comm : forall x y : T, x * y = y * x.
Axiom Tmul_assoc : forall x y z : T, x * (y * z) = (x * y) * z.
Axiom Tdistr_l : forall x y z : T, (x + y) * z = x * z + y * z.
Axiom Topp_def : forall x : T, x + (- x) = 0.
Axiom Tinv_l : forall x : T, x <> 0 -> (/ x) * x = 1.

(** 构造 ring，为了和其他数域保持同一个接口 *)
Definition T_ring : ring_theory T0 T1 Tadd Tmul Tsub Topp eq.
  constructor; auto.
  apply Tadd_0_l. apply Tadd_comm. apply Tadd_assoc.
  apply Tmul_1_l. apply Tmul_comm. apply Tmul_assoc.
  apply Tdistr_l. apply Topp_def.
Defined.

Add Ring Ring_thy_inst : T_ring.

Definition T_field : field_theory T0 T1 Tadd Tmul Tsub Topp Tdiv Tinv eq.
  constructor; auto.
  apply T_ring. intro. easy.
  apply Tinv_l.
Defined.

Add Field Field_thy_inst : T_field.

(** AST的语义 *)
Fixpoint T2R (t : T) : R :=
  match t with
  | 0 => R0 | 1 => R1 | TLit r => r
  | t1 + t2 => Rplus (T2R t1) (T2R t2) | Topp t => Ropp (T2R t)
  | t1 * t2 => Rmult (T2R t1) (T2R t2) | Tinv t => Rinv (T2R t)
  | Tfunc f args => match f with
    | _ => R0
    end
  end.

(** 化简一步 *)
Fixpoint simp (t : T) : T :=
  match t with
  | 0 + x => x 
  | x + 0 => x
  | a + (b + c) => a + b + c      (* 加法结合律 *)
  | a + b => (simp a) + (simp b)
  | - 0 => 0
  | - - a => a                    (* 双重取负消去 *)
  | - (a + b) => - a + - b        (* 取负对加法的分配 *)
  | - (a * b) => (-a) * b         (* 取负对乘法的分配，随意分配给其中一个 *)
  | - x => - (simp x)
  | 0 * _ => 0
  | _ * 0 => 0
  | 1 * x => x
  | (- T1) * x => (-x)
  | x * (- T1) => (-x)
  | x * 1 => x
  | a * (b + c) => (a * b) + (a * c)    (* 乘对加的左分配律 *)
  | (a + b) * c => (a * c) + (b * c)    (* 乘对加的右分配律 *)
  | a * (b * c) => a * b * c            (* 乘法结合律 *)
  | a * b => (simp a) * (simp b)
  | / 1 => 1
  | / (a * b) => /a * /b          (* 取逆对乘法的分配 *) 
  | / x => / (simp x)
  | _ => t
  end.

(** 化简多步 *)
Fixpoint nsimp (t : T) (n : nat) : T :=
  match n with
  | O => t
  | S n' => nsimp (simp t) n'
  end.


(** 测试 *)
Section test.
(* 
  (* simp 测试 *)
  Compute  simp (1 * 1 * (0 + 0)).
  Compute nsimp (1 * 1 * (0 + 0)) 2.
  Compute  simp (1 * 1 + 1 + (0 + 0 + 0)).
  Compute nsimp (1 * 1 + 1 + (0 + 0 + 0)) 3.
  
  (* T2R 测试 *)
  Let f (t : T) : T := 1 * 1 * (t + 0 + 0).
  Compute T2R (f T0).
  Compute f T0.
  Compute T2R (simp (f T0)). *)

(* 行列式及逆矩阵有关的 测试 *)
  Variable r11 r12 r13 r21 r22 r23 r31 r32 r33 : R.
  Let a11 := TLit r11. Let a12 := TLit r12. Let a13 := TLit r13.
  Let a21 := TLit r21. Let a22 := TLit r22. Let a23 := TLit r23.
  Let a31 := TLit r31. Let a32 := TLit r32. Let a33 := TLit r33.
  
  Let t1 := / (TLit r11 * TLit r22 + - TLit r12 * TLit r21) * - (1) * TLit r12.
(*   Eval cbv in (T2R (nsimp t1 25)). *)
  
End test.

(** T上的相等关系是可判定的 *)
Theorem Teqdec : forall t1 t2 : T, {t1 = t2} + {t1 <> t2}.
Proof.
  induction t1; induction t2; auto;
  try (left; easy); try (right; easy).
  - destruct (Req_EM_T r r0); subst; auto. right. intro. inversion H. auto.
  - destruct (IHt1_1 t2_1),(IHt1_2 t2_2); subst; auto.
    + right. intro. inversion H. easy.
    + right. intro. inversion H. easy.
    + right. intro. inversion H. easy.
  - destruct (IHt1 t2); subst; auto. right. intro H; inversion H. easy.
  - destruct (IHt1_1 t2_1),(IHt1_2 t2_2); subst; auto.
    + right. intro. inversion H. easy.
    + right. intro. inversion H. easy.
    + right. intro. inversion H. easy.
  - destruct (IHt1 t2); subst; auto. right. intro H; inversion H. easy.
  - destruct (string_dec f f0); subst; auto.
    2:{ right. intro. inversion H. easy. }
    { assert ({args = args0} + {args <> args0}).
      2:{ destruct H; subst; auto. right. intro H; inversion H; auto. }
      apply List.list_eq_dec.
      (* 为什么没有这个归纳假设？ *)
Admitted.

(** 下面用到 R 比较多，故改变作用域 *)
Open Scope R.

(** 证明simp不改变语义 *)
Theorem simp_ok : forall (t : T), T2R (simp t) = T2R t.
Proof.
(*   induction t; auto.
  - simpl. destruct (Teqdec t1 0), (Teqdec t2 0).
    + subst. simpl. ring.
    + subst. simpl. ring.
    + subst.
      replace (match t1 with 0 => 0 | _ => t1 end)%T with t1.
      * simpl. ring.
      * destruct t1; auto.
    + replace (match t2 with 0 => t1 | b + c => t1 + b + c | 
        _ => simp t1 + simp t2 end)%T
      with (match t2 with b + c => t1 + b + c | 
        _ => simp t1 + simp t2 end)%T.
      * replace (match t1 with 0 => t2 | _ => simp t1 + simp t2 end)%T
        with (simp t1 + simp t2)%T.
        { simpl. rewrite IHt1, IHt2. auto. }
        { destruct t1; auto. easy. }
      * destruct t2; auto. easy.
  - simpl. destruct (Teqdec t 0); subst; simpl; try ring.
    replace (match t with 0 => 0 | _ => - simp t end)%T with (- simp t)%T.
    + simpl. rewrite IHt. auto.
    + destruct t; auto. easy.
  - simpl. destruct (Teqdec t1 0), (Teqdec t2 0).
    + subst. simpl. ring.
    + subst. simpl. ring.
    + subst. destruct t1; simpl; try ring.
    + destruct (Teqdec t1 1); subst; auto.
      * replace (match t2 with 0 => 0 | _ => t2 end)%T with t2.
        simpl; try ring. destruct t2; auto.
      * destruct (Teqdec t2 1); subst.
        { replace (match t1 with 0 => 0 | 1 => 1 | _ => t1 end)%T with t1.
          simpl; ring. destruct t1; auto. }
        { replace (match t2 with 0 => 0 | _ => t2 end)%T with t2.
          { replace (match t2 with 0=>0 | 1=>t1 | _=> simp t1 * simp t2
            end)%T with (simp t1 * simp t2)%T.
            { replace (match t1 with 0=>0 | 1=>t2 | _=> simp t1 * simp t2
              end)%T with (simp t1 * simp t2)%T.
              { simpl; rewrite IHt1,IHt2. auto. }
              { destruct t1; auto; try easy. } }
            { destruct t2; auto; try easy. } }
          { destruct t2; auto. }}
  - simpl. destruct (Teqdec t 0); subst; simpl; try ring.
    destruct (Teqdec t 1); subst. simpl. field.
    replace (match t with 1 => 1 | _ => / simp t end)%T with (/ simp t)%T.
    + simpl. rewrite IHt. auto.
    + destruct t; auto. easy.
Qed. *)
Admitted.


(** 证明nsimp不改变语义 *)
Theorem nsimp_ok : forall (n : nat) (t : T), T2R (nsimp t n) = T2R t.
Proof.
  induction n; auto. simpl. intros. rewrite IHn. apply simp_ok.
Qed.

(** 定义布尔相等 *)
Definition Teqb (t1 t2 : T) : bool :=
  let r1 := T2R t1 in
  let r2 := T2R t2 in
    if Req_EM_T r1 r2 then true else false.

Infix     "=?"          := Teqb           : T_scope.

