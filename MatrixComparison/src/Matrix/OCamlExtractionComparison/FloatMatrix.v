(*
  purpose   : 在 FloatMatrix 上的OCaml程序抽取测试
  author    : ZhengPu Shi
  date      : Nov 1, 2022

  remark    :
  1. Coq中的R类型映射为OCaml中的float
  2. 矩阵操作有
     从list生成矩阵，用于结构化输入
     将矩阵转为list，用于结构化输出
     从函数生成矩阵，用于动态输入
     将矩阵转为函数，用于动态输出
     矩阵加法、乘法
     获取矩阵元素，读取单个元素
     修改矩阵元素，修改单个元素
  3. 对“矩阵的构造、运算、读取、修改等”功能进行测试，
     从时间和空间复杂度两方面测试矩阵模型的差异。
 *)

(** 使用 Matlab 做矩阵运算的例子，用于正确性测试的对照：
>> mat1 = [1,2,3; 4,5,6]

mat1 =

     1     2     3
     4     5     6

>> mat2 = mat1'

mat2 =

     1     4
     2     5
     3     6

>> mat3 = mat1 * mat2

mat3 =

    14    32
    32    77

>> mat4 = mat2 * mat1

mat4 =

    17    22    27
    22    29    36
    27    36    45

*)

Require Import Extraction.
Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlR.
Require Import Reals MatrixAll.
Require Import List. Import ListNotations.

(** 实数矩阵的接口 *)
Module Type FloatMatrixSig.
  
  (** 矩阵类型 *)
  Parameter mat : nat -> nat -> Type.
  (** 矩阵加法 *)
  Parameter madd : forall r c, mat r c -> mat r c -> mat r c.
  (** 矩阵乘法 *)
  Parameter mmul : forall r c s, mat r c -> mat c s -> mat r s.
  (** 与 list 的转换 *)
  Parameter l2m : forall r c, list (list R) -> mat r c.
  (* nat -> nat -> (forall r c, mat r c). *)
  Parameter m2l : forall r c, mat r c -> (nat * nat * list (list R)).
  (** 与 函数 的转换 *)
  (* Parameter f2m : forall r c, (nat -> nat -> R) -> mat r c. *)
  (* Parameter m2f : forall r c, mat r c -> (nat * nat * (nat -> nat -> R)). *)
  (** 取出元素 *)
  (* Parameter mget : forall r c, mat r c -> nat -> nat -> R. *)
  (** 修改元素 *)
  (* Parameter mset : forall r c, mat r c -> nat -> nat -> R -> mat r c. *)

End FloatMatrixSig.

(** 实数矩阵的各种实现 *)
Module FloatMatrix_DL <: FloatMatrixSig.
  Import MatrixR_DL.

  Definition mat := @mat R.
  Definition madd := @madd.
  Definition mmul := @mmul.
  Definition l2m := @l2m.
  Definition m2l {r c} (m : mat r c) := (r, c, @m2l _ _ m).
  Definition mget := @mget.
  Definition mset := @mset.
  
End FloatMatrix_DL.


(*   Import (M FieldR). *)
(*   Check M.mat. *)
(*   Definition mat := M @mat nat. *)
(*   (** 矩阵加法 *) *)
(*   Definition madd {r c} := @madd nat Nat.add r c. *)
(*   (** 矩阵乘法 *) *)
(*   Definition mmul {r c s} := @mmul nat 0 Nat.add Nat.mul r c s. *)
(*   (** 矩阵转置 *) *)
(*   Definition mtrans {r c} := @mtrans nat r c. *)
(*   (** 与 list 的转换 *) *)
(*   Definition l2m := @l2m nat 0. *)
(*   Definition m2l := @m2l nat. *)
(*   (** 取出元素 *) *)
(*   Locate mnth. *)
(*   Definition mnth := @mnth nat  *)
(*     (** 修改元素 *) *)

(*   Example mat1 : mat 2 3 := l2m [[1;2;3];[4;5;6]] 2 3. *)
(*   Example mat2 : mat 3 2 := mtrans mat1. *)
(*   Example mat3 : mat 2 2 := mmul mat1 mat2. *)
(*   Example mat4 : mat 3 3 := mmul mat2 mat1. *)

(* End MatrixNat. *)

Extraction "matrix.ml" FloatMatrix_DL.
(* mat madd mmul mat1 mat2 mat3 mat4. *)
