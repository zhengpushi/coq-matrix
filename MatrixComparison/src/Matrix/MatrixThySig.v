(*
 Copyright 2022 ZhengPu Shi
  This file is part of coq-matrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Signature of Matrix Theory
  author    : ZhengPu Shi
  date      : 2021.12
  
  remark    :
  1. This is an inteface of different matrix implementation.
*)

Require Export BasicConfig FieldStruct TuplesExt ListListExt.

(* ######################################################################### *)
(** * Signature of matrix theory *)
Module Type MatrixThySig (F : FieldSig).
  
  (* ==================================== *)
  (** ** Base type *)
  Export F.
  Open Scope X_scope.
  Open Scope mat_scope.
  
  (* ==================================== *)
  (** ** Matrix type *)
  Parameter mat : Type -> nat -> nat -> Type.
  
  (** 简短记号 *)
  Notation M r c := (mat X r c).

  (* ==================================== *)
  (** ** Equality of two matrices *)
  Parameter meq_dec : forall {r c} (m1 m2 : M r c), {m1 = m2} + {m1 <> m2}.
  
  
  (* ==================================== *)
  (** ** Convert between list list and matrix *)
  Parameter l2m : forall {r c} (dl : list (list X)), M r c.
  
  Parameter m2l : forall {r c}, M r c -> list (list X).
  Parameter m2l_length : forall {r c} (m : M r c), length (m2l m) = r.
  Parameter m2l_width : forall {r c} (m : M r c), width (m2l m) c.
  
  Parameter m2l_l2m_id : forall {r c} (dl : list (list X)),
    length dl = r -> width dl c -> m2l (@l2m r c dl) = dl.
  Parameter l2m_m2l_id : forall {r c} (m : M r c), 
    l2m (m2l m) = m.
  
  Parameter l2m_inj : forall {r c} (d1 d2 : list (list X)),
    length d1 = r -> width d1 c -> 
    length d2 = r -> width d2 c -> 
    d1 <> d2 -> @l2m r c d1 <> l2m d2.
  Parameter l2m_surj : forall {r c} (m : M r c), 
    (exists d, l2m d = m). 
  Parameter m2l_inj : forall {r c} (m1 m2 : M r c),
    m1 <> m2 -> m2l m1 <> m2l m2.
  Parameter m2l_surj : forall {r c} (d : list (list X)), 
    length d = r -> width d c -> 
    (exists m, @m2l r c m = d).
  
  (* ==================================== *)
  (** ** Get n-th element *)
  Parameter mnth : forall {r c}, M r c -> nat -> nat -> X.
  Parameter meq_iff_mnth : forall {r c : nat} (m1 m2 : M r c),
    m1 = m2 <-> 
    (forall ri ci, ri < r -> ci < c -> mnth m1 ri ci = mnth m2 ri ci).
  
  
  (* ==================================== *)
  (** ** Specific matrix *)
  Parameter mk_mat_1_1 : forall (a11 : X), M 1 1.
  Parameter mk_mat_3_1 : forall (a1 a2 a3 : X), M 3 1.
  Parameter mk_mat_3_3 : forall (a11 a12 a13 a21 a22 a23 a31 a32 a33 : X), 
    M 3 3.

  (** Zero matrix *)
  Parameter mat0 : forall r c, M r c.

  (** Unit matrix *)
  Parameter mat1 : forall n, M n n.
  
  
  (* ==================================== *)
  (** ** Mapping of matrix *)
  Parameter mmap : forall {r c} (f : X -> X) (m : M r c), M r c.
  Parameter mmap2 : forall {r c} (f: X->X->X) (m1 m2 : M r c), M r c.
  Parameter mmap2_comm : forall {r c} (f : X -> X -> X)
    (f_comm : forall a b, f a b = f b a)  (m1 m2 : M r c), 
    mmap2 f m1 m2 = mmap2 f m2 m1.
  Parameter mmap2_assoc : forall {r c} (f : X -> X -> X)
    (f_assoc : forall a b c, f a (f b c) = f (f a b) c) (m1 m2 m3 : M r c), 
    mmap2 f (mmap2 f m1 m2) m3 = mmap2 f m1 (mmap2 f m2 m3).
    
    
  (* ==================================== *)
  (** ** Matrix addition *)
  Parameter madd : forall {r c}, M r c -> M r c -> M r c.
  Infix "+" := madd : mat_scope.
  Parameter madd_comm : forall {r c} (m1 m2 : M r c), 
    m1 + m2 = m2 + m1.
  Parameter madd_assoc : forall {r c} (m1 m2 m3 : M r c), 
    (m1 + m2) + m3 = m1 + (m2 + m3).
  Parameter madd_0_l : forall {r c} (m : M r c), (mat0 r c) + m = m.
  
  
  (* ==================================== *)
  (** ** Matrix subtraction *)
  Parameter mopp : forall {r c}, M r c -> M r c.
  Notation "- m" := (mopp m) : mat_scope.
  Parameter msub : forall {r c}, M r c -> M r c -> M r c.
  Infix "-" := msub : mat_scope.
  
  Parameter mopp_opp : forall {r c} (m : M r c), - - m = m.
  Parameter msub_comm : forall {r c} (m1 m2 : M r c), m1 - m2 = - (m2 - m1).
  Parameter msub_assoc : forall {r c} (m1 m2 m3 : M r c), 
    (m1 - m2) - m3 = m1 - (m2 + m3).
  Parameter msub_0_l : forall {r c} (m : M r c), (mat0 r c) - m = - m.
  Parameter msub_0_r : forall {r c} (m : M r c), m - (mat0 r c) = m.
  Parameter msub_self : forall {r c} (m : M r c), m - m = (mat0 r c).
  Parameter madd_opp : forall {r c} (m : M r c), m + (-m) = (mat0 r c).
  
  (* ==================================== *)
  (** ** Matrix scalar multiplication *)
  Parameter mcmul : forall {r c} (a : X) (m : M r c), M r c.
  Parameter mmulc : forall {r c} (m : M r c) (a : X), M r c.
  Infix " 'c*' " := mcmul.
  Infix " '*c' " := mmulc.
  
  Parameter mmulc_eq_mcmul : forall {r c} (a : X) (m : M r c), 
    m *c a = a c* m.
  Parameter mcmul_assoc : forall {r c} (a b : X) (m : M r c), 
    a c* (b c* m) = (a * b) c* m.
  Parameter mcmul_perm : forall {r c} (a b : X) (m : M r c), 
    a c* (b c* m) = b c* (a c* m).
  Parameter mcmul_add_distr_l : forall {r c} (a : X) (m1 m2 : M r c), 
    a c* (m1 + m2) = (a c* m1) + (a c* m2).
  Parameter mcmul_add_distr_r : forall {r c} (a b : X) (m : M r c), 
    (a + b) c* m = (a c* m) + (b c* m).
  Parameter mcmul_1_l : forall {r c} (m : M r c), X1 c* m = m.
  Parameter mcmul_0_l : forall {r c} (m : M r c), X0 c* m = (mat0 r c).
  
  
  (* ==================================== *)
  (** ** Matrix transposition *)
  Parameter mtrans : forall {r c} (m : M r c), M c r.
  Notation "m 'ᵀ'" := (mtrans m) : mat_scope.
  Parameter mtrans_trans : forall {r c} (m : M r c), m ᵀ ᵀ = m.
  
  
  (* ==================================== *)
  (** ** Matrix multiplicaiton *)
  Parameter mmul : forall {r c s}, M r c -> M c s -> M r s.
  Infix "*" := mmul : mat_scope.
  Parameter mmul_add_distr_l : forall {r c s} (m1 : M r c) 
    (m2 m3 : M c s), m1 * (m2 + m3) = (m1 * m2) + (m1 * m3).
  Parameter mmul_add_distr_r : forall {r c s} (m1 m2 : M r c) 
    (m3 : M c s), (m1 + m2) * m3 = (m1 * m3) + (m2 * m3).
  Parameter mmul_assoc : forall {r c s t} (m1 : M r c) (m2 : M c s) 
    (m3 : M s t), (m1 * m2) * m3 = m1 * (m2 * m3).
  Parameter mmul_0_l : forall {r c s} (m : M c s), (mat0 r c) * m = mat0 r s.
  Parameter mmul_0_r : forall {r c s} (m : M r c), m * (mat0 c s) = mat0 r s.
  Parameter mmul_1_l : forall {r c} (m : M r c), (mat1 r) * m = m.
  Parameter mmul_1_r : forall {r c} (m : M r c), m * (mat1 c) = m. 
  
  
  (* ==================================== *)
  (** ** Other OPs and PROPs *)
  
  (** Convert between tuples and matrix *)
  Parameter t2m_3x3 : @T_3x3 X -> M 3 3.
  Parameter m2t_3x3 : M 3 3 -> @T_3x3 X.
  
  (** 取出1x1矩阵的第 0,0 个元素 *)
  Parameter scalar_of_mat : forall (m : M 1 1), X.
  
End MatrixThySig. 
