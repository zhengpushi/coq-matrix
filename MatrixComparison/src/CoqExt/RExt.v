(*
  purpose   : extension for Coq.Reals.
  author    : ZhengPu Shi
  date      : 2021.05
  
  remark    :
  1. possible reason of "field" failure
    a. notation "/", need unfold Rdiv first.
    b. unknown variable name, need be rewrite first.
  2. why need this library?
    (1). lots of properties are lack in standard library.
    (2). more automation, especially inequality.
    (3). We want to solve any problem of equality or inequality in one step.
  3. why auto fail? and how to better naming a term?
    (1). use two lemmas like A -> B and B -> A instead of A <-> B
    (2). x * x and x² are mixed, and x² is defined as x * x, and Coq Standard 
      Library prefer x², so we'd better choose x². But, notice that we should 
      rewrie x² to x * x before using ring or field, it's a bit annoying.
    (3). 1 and R1 are mixed, and 1 is (IZR (Zpos xH)), and will be reduced to R1
      finally, and Coq Standard Library prefer 1, so we choose 1 as well.
    (4). x - y and x + (-y) is same, but we prefer x - y.
    (5). x / y and x * (-y), we prefer x / y as well.
*)


Require Export BasicConfig.

Require Export ZExt.
Require Export Reals.
Open Scope R_scope.

Require Export Psatz.
Require Export Lra.


(* ######################################################################### *)
(** * Comparison with PI *)

(** 如何证明有关 PI 的不等式？可否先构造PI的一个区间？*)
Goal 2 < PI.
Proof.
  Abort.

(** upper bound & lower bound of PI *)
Definition PI_ub : R := 3.14159266.
Definition PI_lb : R := 3.14159265.
Axiom PI_lt : PI < PI_ub.
Axiom PI_gt : PI_lb < PI.

Goal 2 < PI.
Proof.
  apply Rlt_trans with PI_lb; unfold PI_lb,PI_ub;
  try lra; try apply PI_lt; try apply PI_gt.
Qed.


(* ######################################################################### *)
(** * Conversion between R and other types *)
Definition Z2R (z : Z) : R := IZR z.
Definition R2Z_floor (r : R) : Z := (up r).
Definition R2Z_ceiling (r : R) : Z := (up r - 1)%Z.

(** 该引理的使用常常需要显式提供 z，取值为 r 的地板 *)
Lemma R2Z_floor_correct : forall (r:R) (z:Z), 
  IZR z <= r -> r < IZR (z + 1) -> (z + 1)%Z = R2Z_floor r.
Proof. apply up_tech. Qed.

(** 该引理的使用常常需要显式提供 z，取值为 r 的地板 *)
Lemma R2Z_ceiling_correct : forall (r:R) (z:Z), 
  IZR z <= r -> r < IZR (z + 1) -> z = R2Z_ceiling r.
Proof.
  intros. apply up_tech in H; auto.
  unfold R2Z_ceiling. rewrite <- H. auto with zarith.
Qed.

Definition nat2R (n : nat) : R := Z2R (nat2Z n).
Definition R2nat_floor (r : R) : nat := Z2nat (R2Z_floor r).
Definition R2nat_ceiling (r : R) : nat := Z2nat (R2Z_ceiling r).


(* ######################################################################### *)
(** * Properties for Reqb and Req *)

Definition Reqb (r1 r2 : R) : bool :=
  if Req_EM_T r1 r2 then true else false.

Infix     "=?"          := Reqb           : R_scope.


(** Reflection of (=) and (=?) *)
Lemma Reqb_true_iff : forall x y, x =? y = true <-> x = y.
Proof.
  intros r1 r2. split; unfold Reqb; intros; destruct Req_EM_T; try easy.
Qed.

Lemma Reqb_false_iff : forall x y, x =? y = false <-> x <> y.
Proof.
  intros r1 r2. split; unfold Reqb; intros; destruct Req_EM_T; try easy.
Qed.


(* ######################################################################### *)
(** * Boolean comparison of R *)


Definition Rleb (r1 r2 : R) : bool :=
  if Rle_lt_dec r1 r2 then true else false.
Infix "<=?" := (Rleb) : R_scope.

Definition Rltb (r1 r2 : R) : bool :=
  if Rlt_le_dec r1 r2 then true else false.
Infix "<?" := (Rltb) : R_scope.


Lemma Reqb_comm : forall r1 r2, (r1 =? r2) = (r2 =? r1).
Proof.
  intros r1 r2. unfold Reqb.
  destruct (Req_EM_T r1 r2), (Req_EM_T r2 r1); auto. subst. easy.
Qed.

Lemma Reqb_true_refl : forall r, r =? r = true.
Proof. intros. unfold Reqb. destruct Req_EM_T; auto. Qed.

Lemma Reqb_trans : forall r1 r2 r3, r1 =? r2 = true -> 
  r2 =? r3 = true -> r1 =? r3 = true.
Proof.
  intros. apply Reqb_true_iff in H,H0. apply Reqb_true_iff. rewrite H,H0. easy.
Qed.



(* ######################################################################### *)
(** * Other properties *)

(* ==================================== *)
(** ** Extend properties of R *)

(* 参考以下两个引理，给出变形的形式 :
Rmult_eq_reg_l: forall r r1 r2 : R, r * r1 = r * r2 -> r <> 0 -> r1 = r2
Rmult_eq_reg_r: forall r r1 r2 : R, r1 * r = r2 * r -> r <> 0 -> r1 = r2
*)

(* 若k左乘两个数相等，但这两个数不相等，则k必为 0 *)
Lemma Rmult_eq_imply_eq0_l : forall r r1 r2 : R, 
  r * r1 = r * r2 -> r1 <> r2 -> r = 0.
Proof.
  intros.
  (* 转换到 r1 = r2 的证明 *)
  destruct (Req_EM_T r 0); auto. destruct H0.
  apply (Rmult_eq_reg_l r); auto.
Qed.

(* 若k右乘两个数相等，但这两个数不相等，则k必为 0 *)
Lemma Rmult_eq_imply_eq0_r : forall r r1 r2 : R, 
  r1 * r = r2 * r -> r1 <> r2 -> r = 0.
Proof.
  intros.
  (* 转换到 r1 = r2 的证明 *)
  destruct (Req_EM_T r 0); auto. destruct H0.
  apply (Rmult_eq_reg_r r); auto.
Qed.

(** 若 k 被等于自身，则要么自身为0，要么自身不为0但k必为1 *)
Lemma Rmult_eq_self_imply_0_or_k1 :
  forall k, (forall x, k * x = x -> x = 0 \/ (x <> 0 /\ k = R1)).
Proof.
  intros.
  destruct (Req_EM_T x 0); auto. right. split; auto.
  (* 库里有 a * x = b * x 类似的结论，所以利用1来构造 *)
  replace x with (R1*x) in H at 2; try ring.
  apply Rmult_eq_reg_r in H; auto.
Qed.

 
(* ==================================== *)
(** ** Extend Hint database with name R *)

(** autounfold is usually used before the ring tactic *)
Global Hint Unfold
  Rminus        (* a - b = a + - b *)
  Rdiv          (* a / b = a * / b *)
  Rsqr          (* r² = r * r *)
  : R.

Global Hint Rewrite
  pow1                (* 1 ^ n = 1 *)
  pow_O               (* x ^ 0 = 1 *)
  pow_1               (* x ^ 1 = x *)
  Ropp_0              (* - 0 = 0 *)
  Rminus_0_r          (* r - 0 = r *)
  Rplus_0_l           (* 0 + r = r *)
  Rplus_0_r           (* r + 0 = r *)
  Rmult_0_l           (* 0 * r = 0 *)
  Rmult_0_r           (* r * 0 = 0 *)
  Rmult_1_l           (* 1 * r = r *)
  Rmult_1_r           (* r * 1 = r *)
  Ropp_involutive     (* - - r = r *)
  Rsqr_mult           (* (x * y)² = x² * y² *)
  Rsqr_sqrt           (* 0 <= x -> (sqrt x)² = x *)
  sqrt_Rsqr           (* 0 <= x -> sqrt x² = x *)
  Rplus_opp_r         (* r + - r = 0 *)
  Rplus_opp_l         (* - r + r = 0 *)
(*   Ropp_mult_distr_r_reverse     (* r1 * - r2 = - (r1 * r2) *) *)
(*   Ropp_mult_distr_l_reverse     (* - r1 * r2 = - (r1 * r2) *) *)
  : R.

Global Hint Resolve
  sqrt_0              (* sqrt 0 = 0 *)
  Rlt_0_1             (* 0 < 1 *)
  PI_RGT_0            (* PI > 0 *)
  sqrt_pos            (* 0 <= sqrt x *)
  Rle_0_sqr           (* 0 <= r² *)
(*   Rsqr_inj            (* 0 <= x -> 0 <= y -> x² = y² -> x = y *) *)
  sin2_cos2           (* (sin x)² + (cos x)² = 1 *)
  Rplus_le_le_0_compat  (* 0 <= r1 -> 0 <= r2 -> 0 <= r1 + r2 *)
  Rplus_lt_le_0_compat  (* 0 < r1 -> 0 <= r2 -> 0 < r1 + r2 *)
  Rplus_le_lt_0_compat  (* 0 <= r1 -> 0 < r2 -> 0 < r1 + r2 *)
  Rplus_lt_0_compat   (* 0 < r1 -> 0 < r2 -> 0 < r1 + r2 *)
  Rmult_lt_0_compat   (* 0 < r1 -> 0 < r2 -> 0 < r1 * r2 *)
  Rinv_0_lt_compat    (* 0 < r -> 0 < / r *)
  Rlt_gt              (* r1 < r2 -> r2 > r1 *)  (* THIS IS ALWAYS NEED! *)
  Rgt_lt              (* r1 > r2 -> r2 < r1 *)  (* THIS ONE, slow but useful *)
  Rgt_not_eq          (* r1 > r2 -> r1 <> r2 *)
  Rge_le              (* r1 >= r2 -> r2 <= r1 *)
  Rle_ge              (* r1 <= r2 -> r2 >= r1 *)
  Rsqr_eq_0           (* x² = 0 -> x = 0 *)
  Rlt_le              (* r1 < r2 -> r1 <= r2 *)
  Rsqr_pos_lt         (* x <> 0 -> 0 < x² *)
  Rlt_not_eq          (* r1 < r2 -> r1 <> r2 *)
  Rgt_not_eq          (* r1 > r2 -> r1 <> r2 *)
(*   sqrt_sqrt           (* 0 <= x -> sqrt x * sqrt x = x *) *)
  Rsqr_sqrt           (* 0 <= x -> (sqrt x)² = x *)
  sqrt_Rsqr           (* 0 <= x -> sqrt x² = x *)
  : R.


(** ** Control Opaque / Transparent *)
Global Opaque 
  PI 
  sqrt
  Rpower 
  sin 
  cos
  tan
  asin
  atan
  acos.



(* ==================================== *)
(** ** Equality of R *)

(* --------------------------------------------------------------------- *)
(** *** Rsqr *)

(** We always prefer x², an exception is when using ring or field tactic. *)
Lemma xx_Rsqr x : x * x = x².
Proof. auto. Qed.

(** So, there are two typical situations:
<<
  autounfold with R; ring.    (* for ring *)
  autorewrite with xx_Rsqr; auto with R.    (* for auto *)
>>
*)
Global Hint Rewrite xx_Rsqr : R.


(* --------------------------------------------------------------------- *)
(** *** R1 and 1 *)

(** We always prefer 1 *)
Lemma R1_eq_1 : R1 = 1.
Proof. auto. Qed.
Global Hint Rewrite R1_eq_1 : R.

Lemma Rsqr_1 : 1² = 1.
Proof. unfold Rsqr; ring. Qed.
Global Hint Rewrite Rsqr_1 : R.
Global Hint Resolve Rsqr_1 : R.

Lemma Rinv_1 : /1 = 1.
Proof. auto with real. Qed.
Global Hint Rewrite Rinv_1 : R.
Global Hint Resolve Rinv_1 : R.

Lemma zero_le_1 : 0 <= 1.
Proof. auto with real. Qed.
Global Hint Resolve zero_le_1 : R.

Lemma zero_neq_1 : 0 <> 1.
Proof. auto with real. Qed.
Global Hint Resolve zero_neq_1 : R.

Module TEST_R1_and_1.
  Goal 1 = R1. auto with R. Qed.
  Goal R1² = 1. auto with R. Qed.
  Goal 1² = R1. auto with R. Qed.
  Goal /R1 = R1. auto with R. Qed.
  Goal /R1 = 1. auto with R. Qed.
  Goal /1 = R1. auto with R. Qed.
  Goal 0 <= R1. auto with R. Qed.

End TEST_R1_and_1.



(* ==================================== *)
(** ** Rplus, Rpop, Rsub, Rmult, Rinv, Rdiv *)

Lemma Rsub_opp r1 r2 : r1 - (- r2) = r1 + r2.
Proof. ring. Qed.
Global Hint Rewrite Rsub_opp : R.


(** ** Rsqrt *)
Lemma sqrt_1 : sqrt 1 = 1.
Proof. apply Rsqr_inj; autorewrite with R; auto with R. Qed.
Global Hint Rewrite sqrt_1 : R.

Lemma sqrt_le0_eq_0 r (H : r <= 0) : sqrt r = 0.
Proof.
  Transparent sqrt. unfold sqrt. destruct (Rcase_abs r); auto.
  assert (r = 0); try lra. subst. compute. 
  destruct (Rsqrt_exists). destruct a.
  symmetry in H1. auto with R.
Qed.
Global Hint Resolve sqrt_le0_eq_0 : R.

Lemma sqrt_lt0_eq_0 r (H : r < 0) : sqrt r = 0.
Proof. apply sqrt_le0_eq_0. auto with R. Qed.
Global Hint Resolve sqrt_lt0_eq_0 : R.

Lemma le0_imply_sqrt_eq0 : forall (x : R), x < 0 -> sqrt x = 0.
Proof.
  intros. Transparent sqrt. unfold sqrt. destruct (Rcase_abs x). auto.
  (* although, x < 0, x >= 0, all appear, lra fail to solve it. *)
  exfalso. lra.
Qed.
Global Hint Resolve le0_imply_sqrt_eq0 : R.

Lemma sqrt_gt0_imply_gt0 : forall (x : R), 0 < sqrt x -> 0 < x.
Proof.
  intros. replace 0 with (sqrt 0) in H; auto with R.
  apply sqrt_lt_0_alt in H. auto.
Qed.
Global Hint Resolve sqrt_gt0_imply_gt0 : R.

Lemma sqrt_gt0_imply_ge0 : forall (x : R), 0 < sqrt x -> 0 <= x.
Proof. intros. auto with R. Qed.
Global Hint Resolve sqrt_gt0_imply_ge0 : R.

Lemma sqrt_eq1_imply_eq1 : forall (x : R), sqrt x = 1 -> x = 1.
Proof.
  intros.
  assert ((sqrt x)² = 1). rewrite H. autounfold with R in *; ring.
  rewrite <- H0.
  apply eq_sym. apply Rsqr_sqrt.
  assert (0 < sqrt x). rewrite H; auto with R.
  apply sqrt_gt0_imply_gt0 in H1. auto with R.
Qed.
Global Hint Resolve sqrt_eq1_imply_eq1 : R.

(** ( √ r1 * √ r2)^2 = r1 * r2 *)
Lemma Rsqr_sqrt_sqrt r1 r2 : 0 <= r1 -> 0 <= r2 ->
  ((sqrt r1) * (sqrt r2))² = r1 * r2.
Proof.
  destruct (Rcase_abs r1), (Rcase_abs r2); try lra.
  autorewrite with R; auto with R.
Qed.
Global Hint Resolve Rsqr_sqrt_sqrt : R.
Global Hint Rewrite Rsqr_sqrt_sqrt : R.

(** ( √ r1 * √ r2)^2 = r1 * r2 *)
Lemma sqrt_mult_sqrt : forall (r1 r2 : R), 
  0 <= r1 -> 0 <= r2 ->
  ((sqrt r1) * (sqrt r2)) * ((sqrt r1) * (sqrt r2)) = r1 * r2.
Proof.
  intros. ring_simplify. repeat rewrite pow2_sqrt; auto.
Qed.
Global Hint Resolve sqrt_mult_sqrt : R.
Global Hint Rewrite sqrt_mult_sqrt : R.


Module TEST_Rsqrt.
  Goal sqrt R1 = R1. autorewrite with R; auto with R. Qed.
  
End TEST_Rsqrt.


(* ==================================== *)
(** ** sin,cos,tan *)
Lemma cos2_sin2 x : (cos x)² + (sin x)² = 1.
Proof. rewrite Rplus_comm; auto with R. Qed.
Global Hint Resolve cos2_sin2 : R.
Global Hint Rewrite cos2_sin2 : R.

Module TEST_sin_cos_tan.
  Goal forall x, cos x * cos x + sin x * sin x = R1.
  intros; autorewrite with R; auto with R. Qed.
  
  Goal forall x, sin x * sin x + cos x * cos x = R1.
  intros; autorewrite with R; auto with R. Qed.

End TEST_sin_cos_tan.


(* ==================================== *)
(** ** Rpower *)

(**
Rpower rules:
<<
  1. Definition of Rpower
  a^n       = a * a * ... * a    (* there are n numbers *)
  a^0       = 1 (a ≠ 0)
  a^(-n)    = 1 / a^n (a ≠ 0)
  a^(m/n)   = n√ a^m  (a > 0)
  a^(-m/n)  = 1 / n√ a^m  (a > 0)
>>
*)
Lemma Rpower_neq0 x y : x <> 0 -> Rpower x y <> 0.
Proof.
  Admitted.


(* ==================================== *)
(** ** Inequality of R *)

(** ** x = 0 *)

Lemma Req0_imply_Rsqr_eq0 r : r = 0 -> r² = 0.
Proof. intros. subst; unfold Rsqr; ring. Qed.
Global Hint Resolve Req0_imply_Rsqr_eq0 : R.

(* Lemma Rsqr_eq0_iff_eq0 r : r² = 0 <-> r = 0.
Proof. split; auto with R. Qed.
Global Hint Resolve Rsqr_eq0_iff_eq0 : R. *)


(* ==================================== *)
(** ** 0 <= x *)

Lemma zero_le_Rsqr r : 0 <= r².
Proof. auto with R. Qed.
Global Hint Resolve zero_le_Rsqr : R.

Lemma Rplus_Rsqr_Rsqr_ge0 r1 r2 : 0 <= r1² + r2².
Proof. auto with R. Qed.
Global Hint Resolve Rplus_Rsqr_Rsqr_ge0 : R.

Ltac tac_zero_le :=
  intros; autorewrite with R;
  repeat (match goal with
  | |- 0 <= ?r1 * ?r2 => apply Rmult_le_pos
  | |- _ => idtac
  end;
  auto with R; try lra).

Module TEST_zero_le.

  Goal forall r, 0 <= r * r. tac_zero_le. Qed.
  Goal forall r, 0 <= r². tac_zero_le. Qed.
  Goal forall r1 r2, 0 <= r1 * r1 + r2 * r2. tac_zero_le. Qed.
  Goal forall r1 r2, 0 <= r1² + r2². tac_zero_le. Qed.
  Goal forall r1 r2, 0 <= r1 * r1 + r2². tac_zero_le. Qed.
  Goal forall r1 r2, 0 <= r1² + r2 * r2. tac_zero_le. Qed.
  Goal forall r, 0 <= r -> 0 <= r * 5. tac_zero_le. Qed.
  Goal forall r, 0 <= r -> 0 <= r * 5 * 10. tac_zero_le. Qed.
  Goal forall r, 0 <= r -> 0 <= r * (/5) * 10. tac_zero_le. Qed.
  
End TEST_zero_le.


(* ==================================== *)
(** ** 0 < x *)

Lemma Rneq0_imply_Rplus_gt0_2_1 r1 r2 : r1 <> 0 -> 0 < r1² + r2².
Proof. auto with R. Qed.
Global Hint Resolve Rneq0_imply_Rplus_gt0_2_1 : R.

Lemma Rneq0_imply_Rplus_gt0_2_2 r1 r2 : r2 <> 0 -> 0 < r1² + r2².
Proof. auto with R. Qed.
Global Hint Resolve Rneq0_imply_Rplus_gt0_2_2 : R.

Lemma Rneq0_imply_Rplus_gt0_3_1 r1 r2 r3 : r1 <> 0 -> 0 < r1² + r2² + r3².
Proof. auto with R. Qed.
Global Hint Resolve Rneq0_imply_Rplus_gt0_3_1 : R.

Lemma Rneq0_imply_Rplus_gt0_3_2 r1 r2 r3 : r2 <> 0 -> 0 < r1² + r2² + r3².
Proof. auto with R. Qed.
Global Hint Resolve Rneq0_imply_Rplus_gt0_3_2 : R.

Lemma Rneq0_imply_Rplus_gt0_3_3 r1 r2 r3 : r3 <> 0 -> 0 < r1² + r2² + r3².
Proof. auto with R. Qed.
Global Hint Resolve Rneq0_imply_Rplus_gt0_3_3 : R.

Lemma Rgt0_imply_Rplus_gt0_2_1 r1 r2 : 0 < r1 -> 0 < r1² + r2².
Proof. auto with R. Qed.
Global Hint Resolve Rgt0_imply_Rplus_gt0_2_1 : R.

Lemma Rgt0_imply_Rplus_gt0_2_2 r1 r2 : 0 < r2 -> 0 < r1² + r2².
Proof. auto with R. Qed.
Global Hint Resolve Rgt0_imply_Rplus_gt0_2_2 : R.

Lemma Rgt0_imply_Rplus_gt0_3_1 r1 r2 r3 : 0 < r1 -> 0 < r1² + r2² + r3².
Proof. auto with R. Qed.
Global Hint Resolve Rgt0_imply_Rplus_gt0_3_1 : R.

Lemma Rgt0_imply_Rplus_gt0_3_2 r1 r2 r3 : 0 < r2 -> 0 < r1² + r2² + r3².
Proof. auto with R. Qed.
Global Hint Resolve Rgt0_imply_Rplus_gt0_3_2 : R.

Lemma Rgt0_imply_Rplus_gt0_3_3 r1 r2 r3 : 0 < r3 -> 0 < r1² + r2² + r3².
Proof. auto with R. Qed.
Global Hint Resolve Rgt0_imply_Rplus_gt0_3_3 : R.


(** Some times, auto cannot solve, we need customized tactic *)
Ltac tac_zero_lt :=
  intros; autorewrite with R;
  match goal with
  | H : ?r1 <> 0 |- 0 < ?r1² + ?r2² => apply Rneq0_imply_Rplus_gt0_2_1
  | H : ?r2 <> 0 |- 0 < ?r1² + ?r2² => apply Rneq0_imply_Rplus_gt0_2_2
  | H : 0 < ?r1  |- 0 < ?r1² + ?r2² => apply Rgt0_imply_Rplus_gt0_2_1
  | H : 0 < ?r2  |- 0 < ?r1² + ?r2² => apply Rgt0_imply_Rplus_gt0_2_2
  | H : 0 < ?r1  |- 0 < ?r1 * ?r2 => apply Rmult_lt_0_compat
  (* these methods are too ugly, but could work now *)
  | |- (0 < ?r1 + ?r2)%R => apply Rplus_lt_0_compat
  | |- (0 < ?r1 * ?r2)%R => apply Rmult_lt_0_compat
  | |- (0 < ?r1²)%R => apply Rlt_0_sqr
  | |- _ => idtac
  end;
  auto with R; try lra.
  
Module TEST_zero_lt.

  Goal forall r, 0 <> r -> 0 < r * r. tac_zero_lt. Qed.
  Goal forall r, 0 <> r -> 0 < r². tac_zero_lt. Qed.
  Goal forall r, 0 < r -> 0 < r * r. tac_zero_lt. Qed.
  Goal forall r, 0 < r -> 0 < r². tac_zero_lt. Qed.
  Goal forall r1 r2, r1 <> 0 -> 0 < r1 * r1 + r2 * r2. tac_zero_lt. Qed.
  Goal forall r1 r2, r1 <> 0 -> 0 < r1² + r2 * r2. tac_zero_lt. Qed.
  Goal forall r1 r2, r1 <> 0 -> 0 < r1 * r1 + r2². tac_zero_lt. Qed.
  Goal forall r1 r2, r1 <> 0 -> 0 < r1² + r2². tac_zero_lt. Qed.
  
  Goal forall r1 r2, r2 <> 0 -> 0 < r1 * r1 + r2 * r2. tac_zero_lt. Qed.
  Goal forall r1 r2, r2 <> 0 -> 0 < r1² + r2 * r2. tac_zero_lt. Qed.
  Goal forall r1 r2, r2 <> 0 -> 0 < r1 * r1 + r2². tac_zero_lt. Qed.
  Goal forall r1 r2, r2 <> 0 -> 0 < r1² + r2². tac_zero_lt. Qed.
  
  Goal forall r1 r2, 0 < r1 -> 0 < r1 * r1 + r2 * r2. tac_zero_lt. Qed.
  Goal forall r1 r2, 0 < r2 -> 0 < r1 * r1 + r2 * r2. tac_zero_lt. Qed.
  
  Goal forall r, 0 < r -> 0 < r * 10. tac_zero_lt. Qed.
  Goal forall r, 0 < r -> 0 < r + 10. tac_zero_lt. Qed.
  Goal forall r, 0 < r -> 0 < r * 100 + 23732. tac_zero_lt. Qed.
  
End TEST_zero_lt.


(* ==================================== *)
(** ** x <> 0 *)


(* (* we prefer the form of : r <> 0 *)
Lemma zero_neq_R_imply_Rneq0 r : 0 <> r -> r <> 0.
Proof. auto. Qed.
Global Hint Resolve zero_neq_R_imply_Rneq0 : R. *)

Lemma zero_lt_imply_Rneq0 r : 0 < r -> r <> 0.
Proof. auto with R. Qed.
Global Hint Resolve zero_lt_imply_Rneq0 : R.


(** r² <> 0 <-> r <> 0 *)

Lemma Rneq0_imply_Rsqr_neq0 r : r <> 0 -> r² <> 0.
Proof. intros. auto with R. Qed.
Global Hint Resolve Rneq0_imply_Rsqr_neq0 : R.

Lemma Rsqr_neq0_imply_Rneq0 r : r² <> 0 -> r <> 0.
Proof. intros. auto with R. Qed.
Global Hint Resolve Rsqr_neq0_imply_Rneq0 : R.


Lemma Rplus_neq0_imply_Rneq0_2_1 r1 r2 : 
  r1 + r2 <> 0 -> r1 = 0 -> r2 <> 0.
Proof. intros. subst; autorewrite with R in H; auto with R. Qed.
Global Hint Resolve Rplus_neq0_imply_Rneq0_2_1 : R.

Lemma Rplus_neq0_imply_Rneq0_2_2 r1 r2 : 
  r1 + r2 <> 0 -> r2 = 0 -> r1 <> 0.
Proof. intros. subst; autorewrite with R in H; auto with R. Qed.
Global Hint Resolve Rplus_neq0_imply_Rneq0_2_2 : R.


Lemma Rneq0_imply_Rplus_Rsqr_neq0_2_1 r1 r2 : 
  r1 <> 0 -> r1² + r2² <> 0.
Proof. intros. auto with R. Qed.
Global Hint Resolve Rneq0_imply_Rplus_Rsqr_neq0_2_1 : R.

Lemma Rneq0_imply_Rplus_Rsqr_neq0_2_2 r1 r2 : 
  r2 <> 0 -> r1² + r2² <> 0.
Proof. intros. auto with R. Qed.
Global Hint Resolve Rneq0_imply_Rplus_Rsqr_neq0_2_2 : R.

Lemma Rneq0_imply_Rplus_Rsqr_neq0_2 r1 r2 : 
  r1 <> 0 \/ r2 <> 0 -> r1² + r2² <> 0.
Proof. intros. destruct H; auto with R. Qed.
Global Hint Resolve Rneq0_imply_Rplus_Rsqr_neq0_2 : R.

Lemma Rplus_neq0_imply_Rneq0_2 r1 r2 : 
  r1² + r2² <> 0 -> r1 <> 0 \/ r2 <> 0.
Proof.
  intro H. destruct (Req_EM_T r1² 0) as [E1|E1]; auto with R.
  right. rewrite E1 in H. autorewrite with R in H; auto with R.
Qed.
Global Hint Resolve Rplus_neq0_imply_Rneq0_2 : R.

Lemma Rplus_Rsqr_neq0_imply_gt0 r1 r2 : 
  r1² + r2² <> 0 -> 0 < r1² + r2².
Proof. 
  intros. apply Rplus_neq0_imply_Rneq0_2 in H. destruct H; auto with R.
Qed.
Global Hint Resolve Rplus_Rsqr_neq0_imply_gt0 : R.

Lemma Rneq0_imply_Rplus_neq0_3 r1 r2 r3 :
  r1 <> 0 \/ r2 <> 0 \/ r3 <> 0 -> r1² + r2² + r3² <> 0.
Proof. intros. repeat (destruct H; auto with R).  Qed.
Global Hint Resolve Rneq0_imply_Rplus_neq0_3 : R.

Lemma Rplus_neq0_imply_Rneq0_3 r1 r2 r3 : 
  r1² + r2² + r3² <> 0 -> r1 <> 0 \/ r2 <> 0 \/ r3 <> 0.
Proof.
  intro H. destruct (Req_EM_T r1² 0) as [E1|E1]; auto with R.
  right. rewrite E1 in H. autorewrite with R in H; auto with R.
Qed.
Global Hint Resolve Rplus_neq0_imply_Rneq0_3 : R.

Lemma Rneq0_imply_Rplus_neq0_4 r1 r2 r3 r4 :
  r1 <> 0 \/ r2 <> 0 \/ r3 <> 0 \/ r4 <> 0 -> r1² + r2² + r3² + r4² <> 0.
Proof. intros. repeat (destruct H; auto with R). Qed.
Global Hint Resolve Rneq0_imply_Rplus_neq0_4 : R.

Lemma Rplus_neq0_imply_Rneq0_4 r1 r2 r3 r4: 
  r1² + r2² + r3² + r4² <> 0 -> r1 <> 0 \/ r2 <> 0 \/ r3 <> 0 \/ r4 <> 0.
Proof.
  intro H. destruct (Req_EM_T r1² 0) as [E1|E1]; auto with R.
  right. rewrite E1 in H. autorewrite with R in H; auto with R.
Qed.
Global Hint Resolve Rplus_neq0_imply_Rneq0_4 : R.


Ltac tac_neq_zero :=
  intros; autorewrite with R in *;
  repeat match goal with
  (* symmetry *)
  | H : 0 <> ?a |- ?b <> 0 => apply not_eq_sym in H
  | H : 0 <> ?a |- 0 <> ?b => apply not_eq_sym in H; apply not_eq_sym
  (* normal *)
  | _ : 0 < ?r |- ?r <> 0 => apply zero_lt_imply_Rneq0
  | _ : ?r1 <> 0 |- ?r1² <> 0 => apply Rneq0_imply_Rsqr_neq0
  | _ : ?r1² <> 0 |- ?r1 <> 0 => apply Rsqr_neq0_imply_Rneq0
  | _ : ?r1 + ?r2 <> 0, _ : ?r1 = 0 |- ?r2 <> 0 => 
    apply Rplus_neq0_imply_Rneq0_2_1
  | _ : ?r1 + ?r2 <> 0, _ : ?r2 = 0 |- ?r1 <> 0 => 
    apply Rplus_neq0_imply_Rneq0_2_2
  (* default *)
(*   | |- ?b <> 0 => apply zero_lt_imply_Rneq0 *)
  | |- _ => idtac
  end;
  auto with R.

Module TEST_tac_neq_zero.
  Goal forall r, r² <> 0 <-> r <> 0. split; tac_neq_zero. Qed.
  Goal forall r, r² <> 0 -> r <> 0. tac_neq_zero. Qed.
  Goal forall r, r <> 0 -> r * r <> 0. tac_neq_zero. Qed.
  Goal forall r, r <> 0 -> r² <> 0. tac_neq_zero. Qed.

  Goal forall r, 0 <> r * r -> r <> 0. tac_neq_zero. Qed.
  Goal forall r, r * r <> 0 -> 0 <> r. tac_neq_zero. Qed.
  Goal forall r, 0 <> r * r -> 0 <> r. tac_neq_zero. Qed.
  
  Goal forall r1 r2 r3 r4 : R,
    r1 <> 0 \/ r2 <> 0 \/ r3 <> 0 \/ r4 <> 0 <-> 
    r1 * r1 + r2 * r2 + r3 * r3 + r4 * r4 <> 0.
  Proof. split; tac_neq_zero. Qed.

End TEST_tac_neq_zero.


(* ==================================== *)
(** ** a < b *)

Lemma Rdiv_le_imply_Rmul_gt a b c : b > 0 -> a * /b < c -> a < b * c.
Proof.
  intros.
  apply (Rmult_lt_compat_l b) in H0; auto.
  replace (b * (a * /b)) with a in H0; auto.
  field. auto with R.
Qed.
Global Hint Resolve Rdiv_le_imply_Rmul_gt : R.

Lemma Rmul_gt_imply_Rdiv_le a b c : b > 0 -> a < b * c -> a * /b < c.
Proof.
  intros.
  apply (Rmult_lt_compat_l (/b)) in H0; auto with R.
  autorewrite with R in *.
  replace (/b * a) with (a / b) in *; try field; auto with R.
  replace (/b * (b * c)) with c in *; try field; auto with R.
Qed.
Global Hint Resolve Rmul_gt_imply_Rdiv_le : R.


  
Global Hint Resolve 
    Rminus_gt_0_lt  (* 0 < b - a -> a < b *)
    Rlt_Rminus      (* a < b -> 0 < b - a *)
    Rlt_minus       (* r1 < r2 -> r1 - r2 < 0 *)
    : R.
    
Ltac tac_le :=
  autounfold with R;
  match goal with
  | |- 0 < ?a + - ?b => apply Rlt_Rminus
  | |- ?a * (?b * /?c) < ?e => replace (a * (b * /c)) with ((a * b) * /c)
  | |- ?a * /?b < ?c => assert (a < b * c); assert (0 < b)
  | |- _ => idtac
  end; try lra; auto with R.
  
Module TEST_tac_le.
  
  Section sec1.
    Variable h T : R.
    Hypothesis Hh1 : 0 < h.
    Hypothesis Hh2 : h < 9200.
    Hypothesis HT1 : -60 < T.
    Hypothesis HT2 : T < 60.
    
    Lemma aux1 : h * 0.0065 < 273.15 + T.
    Proof. lra. Qed.
    
    Lemma aux2 : h / (273.15 + T) < 153.
    Proof.
      autounfold with R.
      assert (273.15 + T > 0). lra. auto with R.
      assert (h < (273.15 + T) * 153). lra. auto with R.
    Qed.
    
    Lemma aux3 : h / (273.15 + T) < 1 / 0.0065.
    Proof.
      autounfold with R.
      assert (273.15 + T > 0). lra. auto with R.
      assert (h < (273.15 + T) * (1/0.0065)). lra. auto with R.
    Qed.
    
    (** auto proof of aux3 *)
    Lemma aux3' : h / (273.15 + T) < 1 / 0.0065.
    Proof. tac_le. Qed.
    
    Lemma ex1 : 0 < 1 - (0.0065 * (h * / (273.15 + T))).
    Proof.
      (* construct condition manually, then try to automate *)
      assert (h / (273.15 + T) < 1/0.0065).
      (* apply aux3. *) tac_le.
      lra.
    Qed.
    
    (** auto proof of ex1 *)
    Lemma ex1' : 0 < 1 - (0.0065 * (h * / (273.15 + T))).
    Proof.
      do 5 tac_le.
    Qed.
    
  End sec1.

End TEST_tac_le.


(* ==================================== *)
(** ** 这些是早期的实现，虽然自动化程度高，但有些转换不完善，需要进一步整合。*)

(** a + b <> 0 *)
Ltac plus_neq0 :=
  match goal with
  | |- ?a + ?b <> 0 => apply Rgt_not_eq,Rlt_gt,Rplus_lt_0_compat; 
    auto with R fcs
  end.

(** 0 < a *)
Ltac zero_lt :=
  repeat match goal with
  (* 0 *)
  | H: ?a <> 0 |- 0 < ?a * ?a => apply Rlt_0_sqr; apply H
  | |- 0 < ?a + ?b => apply Rplus_lt_0_compat
  | |- 0 < ?a * ?b => apply Rmult_lt_0_compat
  | |- 0 < sqrt ?a => apply sqrt_lt_R0
  | |- 0 < ?a / ?b => unfold Rdiv
  | |- 0 < / ?a => apply Rinv_0_lt_compat
  | |- 0 < ?a ^ _ => simpl
  | |- 0 < (?a)² => unfold Rsqr
  | |- 0 < ?a => auto with R fcs; try lra
  (* R0 *)
  | |- R0 < ?a * ?b => apply Rmult_lt_0_compat; try lra; auto with R fcs
  | |- R0 < sqrt ?a => apply sqrt_lt_R0
  | |- R0 < ?a / ?b => unfold Rdiv
  | |- R0 < / ?a => apply Rinv_0_lt_compat
  | |- R0 < ?a ^ _ => simpl
  | |- R0 < (?a)² => unfold Rsqr
  | |- R0 < ?a => auto with R fcs; try lra
  end.


(** simplify expression has sqrt and pow2 *)
Ltac simpl_sqrt_pow2 :=
  repeat (
  (* (_²) -> x * x *)
  unfold Rsqr;
  (* (sqrt r1 * sqrt r2)^2 = r1 * r2 *)
  try rewrite sqrt_mult_sqrt;
  (* (sqrt x) ^ 2 = x *)
  try rewrite pow2_sqrt;
  (* sqrt (x ^ 2) = x *)
  try rewrite sqrt_pow2;
  (* (sqrt x * sqrt x) = x *)
  try rewrite sqrt_sqrt
  ).

(** 0 <= a *)
Ltac zero_le :=
  (* simplify sqrt+pow2 *)
  repeat (
  try simpl_sqrt_pow2;
  try match goal with
  (* 0 <= sqrt x *)
  | |- 0 <= sqrt _ => apply sqrt_pos
  (* 0 <= a * a *)
  | |- 0 <= ?a * ?a => apply Rle_0_sqr
  (* 0 <= a -> 0 <= b -> 0 <= a + b *) 
  | |- 0 <= ?a + ?b => apply Rplus_le_le_0_compat
  (* 0 <= a -> 0 <= b -> 0 <= a * b *)
  | |- 0 <= ?a * ?b => apply Rmult_le_pos
  (* if fail, proof < again *)
(*   | |- 0 <= ?a => apply Rlt_le; zero_le
  | |- R0 <= ?a => apply Rlt_le; zero_le *)
  end).

(** a * b <> 0 *)
Ltac mult_neq0 :=
  match goal with
  | |- ?a * ?b <> 0 => apply Rgt_not_eq,Rlt_gt;zero_le
  end.

(** a <> 0 *)
Ltac neq0 :=
  repeat match goal with
  | |- ?a /\ ?b => repeat split
  | |- ?a <> 0 => apply Rgt_not_eq,Rlt_gt; zero_le
  end.


(** Simplification for trigonometric functions *)

Lemma xx_sqr : forall x:R, x * x = Rsqr x.
Proof. auto. Qed.

Lemma cos2_sin2' : forall x:R, Rsqr (cos x) + Rsqr (sin x) = 1.
Proof. intros. rewrite Rplus_comm. apply sin2_cos2. Qed.

Lemma cos_sin : forall x:R, cos x * sin x = sin x * cos x.
Proof. intros. lra. Qed.

Lemma x_neg_x : forall x:R, x + - x = 0.
Proof. intros. lra. Qed.

Lemma neg_x_x : forall x:R, -x + x = 0.
Proof. intros. lra. Qed.

Lemma x_mul_neg_x : forall x y : R, y * -x = - (x * y).
Proof. intros. lra. Qed.

Lemma neg_x_mul_x : forall x y : R, -y * x = - (y * x).
Proof. intros. lra. Qed.

Lemma sqrR1_R1 : R1² = R1.
Proof. unfold Rsqr. ring. Qed.

Lemma one_R1 : 1 = R1.
Proof. ring. Qed.

Lemma inv1_R1 : /1 = R1.
Proof. field. Qed.

Lemma invR1_R1 : /R1 = R1.
Proof. field. Qed.

Lemma sqrtR1_R1 : sqrt R1 = R1.
Proof. apply Rsqr_inj. zero_le. lra. rewrite Rsqr_sqrt.
  rewrite sqrR1_R1. auto. lra.
Qed.

Lemma sqrt1_R1 : sqrt 1 = R1.
Proof. rewrite one_R1. apply sqrtR1_R1. Qed.

Lemma coscos_sinsin : forall x : R, (cos x * cos x + sin x * sin x) = 1.
Proof. intros. rewrite ?xx_sqr. rewrite ?cos2_sin2. auto. Qed.

Lemma sinsin_coscos : forall x : R, (sin x * sin x + cos x * cos x) = 1.
Proof. intros. rewrite ?xx_sqr. rewrite ?sin2_cos2. auto. Qed.

(** r1 - (-r2) = r1 + r2 *)
Lemma Rsub_Rneg : forall (r1 r2 : R), r1 - (- r2) = r1 + r2.
Proof. intros. ring. Qed.

(** Simplify trigonometric function and expression of real number *)
Ltac trigo_simp := 
  rewrite ?Rmult_opp_opp;   (* -x * -x = x * x *)
(*   rewrite ?xx_sqr;          (* x * x = Rsqr x  *) *)
  rewrite ?Rsub_Rneg,       (* r1 - (-r2) = r1 + r2 *)
          ?sin2_cos2,       (* sin^2 + cos^2 = 1 *)
          ?cos2_sin2,       (* cos^2 + sin^2 = 1 *)
          ?coscos_sinsin,   (* cos*cos + sin*sin = 1 *)
          ?sinsin_coscos,   (* sin*sin + cos*cos = 1 *)
          ?cos_sin,         (* cos * sin = sin * cos *)
          ?x_mul_neg_x,     (* y * -x = - (x * y) *)
          ?neg_x_mul_x,     (* -y * x = - (x * y) *)
          ?x_neg_x,         (* x + -x = 0 *)
          ?neg_x_x,         (* -x + x = 0 *)
          ?sqrtR1_R1,       (* sqrt R1 = R1 *)
          ?sqrt1_R1,        (* sqrt 1 = 1 *)
          ?sqrR1_R1,        (* R1² = R1 *)
(*           ?Rinv_1,           (* /1 = 1 *) *)
          ?inv1_R1,         (* /1 = R1 *)
          ?invR1_R1,        (* /R1 = R1 *)
          ?one_R1           (* 1 = R1 *)
  ;
  autorewrite with R;       (* +0, 0+, *0, 0*, *1, 1* *)
  try field;
  auto.

(** Properties about sqrt *)

(* sqrt x = R1 -> x = R1 *)
Lemma sqrt_eqR1_imply_R1 : forall (x : R), sqrt x = R1 -> x = R1.
Proof.
  intros.
  assert ((sqrt x)² = R1). rewrite H. unfold Rsqr. lra. rewrite <- H0.
  rewrite Rsqr_sqrt; auto.
  assert (0 < sqrt x). rewrite H. lra. 
  apply sqrt_gt0_imply_gt0 in H1. lra.
Qed.


(* ==================================== *)
(** ** Other properties *)

(** r * r = 0 <-> r = 0 *)
Lemma Rmult_eq0_iff_eq0 : forall r, r * r = 0 <-> r = 0.
Proof.
  intros. split; intros.
  - apply Rmult_integral in H. lra. 
  - rewrite H. ring.
Qed.

Global Hint Resolve Rmult_eq0_iff_eq0 : R.

(** r * r <> 0 <-> r <> 0 *)
Lemma Rsqr_neq0_iff_neq0 : forall r, r * r <> 0 <-> r <> 0.
Proof.
  intros. split; intros; intro.
  - rewrite H0 in H. lra.
  - apply Rmult_integral in H0. lra. 
Qed.

Global Hint Resolve Rsqr_neq0_iff_neq0 : R.

(** 0 <= r1*r1 + r2*r2 *)
Lemma Rplus_sqr_sqr_ge0 : forall r1 r2 : R, 0 <= r1 * r1 + r2 * r2.
Proof.
  intros. apply Rplus_le_le_0_compat; zero_le.
Qed.

(** r1 <> 0 \/ r2 <> 0 <-> r1 * r1 + r2 * r2 <> 0 *)
Lemma Rplus_sqr_neq0_iff2 : forall r1 r2 : R,
  r1 <> 0 \/ r2 <> 0 <-> r1 * r1 + r2 * r2 <> 0.
Proof.
  intros. split; intro H.
  - destruct H.
    + rewrite Rplus_comm. apply tech_Rplus; zero_le; zero_lt.
    + apply tech_Rplus; zero_le; zero_lt.
  - destruct (Req_EM_T (r1 * r1) 0) as [E1|E1].
    + rewrite Rmult_eq0_iff_eq0 in E1. right. subst.
      ring_simplify (0 * 0 + r2 * r2) in H. intro. subst. lra.
    + rewrite Rsqr_neq0_iff_neq0 in E1. auto.
Qed.


(** r1*r1 + r2*r2 <> 0 -> 0 < r1*r1 + r2*r2 *)
Lemma Rplus_sqr_sqr_neq0_iff_Rplus_sqr_sqr_gt0 : forall r1 r2 : R,
  r1 * r1 + r2 * r2 <> 0 <-> 0 < r1 * r1 + r2 * r2.
Proof.
  intros. split; intros.
  - apply Rplus_sqr_neq0_iff2 in H. destruct H.
    + apply Rplus_lt_le_0_compat. zero_lt. zero_le.
    + apply Rplus_le_lt_0_compat. zero_le. zero_lt.
  - lra.
Qed.

Global Hint Resolve Rplus_sqr_sqr_neq0_iff_Rplus_sqr_sqr_gt0 : R.

(** r1 <> 0 \/ r2 <> 0 \/ r3 <> 0 <-> r1 * r1 + r2 * r2 + r3 * r3 <> 0 *)
Lemma Rplus_sqr_neq0_iff3 : forall r1 r2 r3 : R,
  r1 <> 0 \/ r2 <> 0 \/ r3 <> 0 <-> r1 * r1 + r2 * r2 + r3 * r3 <> 0.
Proof.
  intros. split; intros.
  - destruct H.
    + rewrite Rplus_assoc. rewrite Rplus_comm. apply tech_Rplus.
      * zero_le.
      * zero_lt.
    + rewrite Rplus_sqr_neq0_iff2 in H.
      rewrite Rplus_assoc. apply tech_Rplus. zero_le.
      auto with R. (* why fail? *)
      apply Rplus_sqr_sqr_neq0_iff_Rplus_sqr_sqr_gt0; auto.
  - rewrite Rplus_sqr_neq0_iff2.
    destruct (Req_EM_T r1 0),(Req_EM_T r2 0),(Req_EM_T r3 0); subst; 
    auto; try lra.
Qed.

(** r1 <> 0 \/ r2 <> 0 \/ r3 <> 0 \/ r4 <> 0 <-> 
    r1 * r1 + r2 * r2 + r3 * r3 + r4 * r4 <> 0 *)
Lemma Rplus_sqr_neq0_iff4 : forall r1 r2 r3 r4 : R,
  r1 <> 0 \/ r2 <> 0 \/ r3 <> 0 \/ r4 <> 0 <-> 
  r1 * r1 + r2 * r2 + r3 * r3 + r4 * r4 <> 0.
Proof.
  intros. split; intro H.
  - destruct H.
    + rewrite Rplus_comm. rewrite Rplus_comm with (r1 := r1*r1).
      rewrite Rplus_assoc. rewrite Rplus_comm with (r1 := r1*r1).
      repeat rewrite <- Rplus_assoc. apply tech_Rplus; zero_le; zero_lt.
    + destruct H.
      * rewrite Rplus_comm. rewrite Rplus_assoc. 
        rewrite Rplus_comm with (r1 := r2 * r2).
        repeat rewrite <- Rplus_assoc. apply tech_Rplus; zero_le; zero_lt.
      * destruct H.
        { repeat rewrite Rplus_assoc. rewrite Rplus_comm with (r2 := r4 * r4).
          repeat rewrite <- Rplus_assoc. apply tech_Rplus; zero_le; zero_lt. }
        { apply tech_Rplus; zero_le; zero_lt. }
  - destruct (r1 * r1 =? 0) eqn : E1.
    + apply Reqb_true_iff in E1. destruct (r2 * r2 =? 0) eqn : E2.
      * apply Reqb_true_iff in E2. destruct (r3 * r3 =? 0) eqn : E3.
        { apply Reqb_true_iff in E3. rewrite E1,E2,E3 in H.
          repeat rewrite Rplus_0_l in H. right;right;right.
          apply Rsqr_neq0_iff_neq0; auto. }
        { apply Reqb_false_iff in E3. right; right; left.
          apply Rsqr_neq0_iff_neq0; auto. }
      * apply Reqb_false_iff in E2. right; left.
          apply Rsqr_neq0_iff_neq0; auto.
    + apply Reqb_false_iff in E1. left. apply Rsqr_neq0_iff_neq0; auto.
Qed.


(* ==================================== *)
(** ** Approximate of two real numbers *)

(** r1 ≈ r2, that means |r1 - r2| <= diff *)
Definition Rapprox (r1 r2 diff : R) : Prop := Rabs (r1 - r2) <= diff.

(** boolean version of approximate function *)
Definition Rapproxb (r1 r2 diff : R) : bool := Rleb (Rabs (r1 - r2)) diff.
