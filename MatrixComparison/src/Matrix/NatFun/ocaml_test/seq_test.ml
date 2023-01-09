(*
 Copyright 2022 ZhengPu Shi
  This file is part of coq-matrix. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

	2022/06/23 12:15
	usage
	#use "seq.ml";;
	#use "seq_test.ml";;
*)

(* get odd number sequence：1,3,5,... *)
let f1 = fun (i : int) -> Float.of_int (2 * i + 1);;

(* get even number sequence: 0,2,4,... *)
let f2 = fun (i : int) -> Float.of_int (2 * i);;

(* chek two sequences equal: top n items are both equal *)
let b = SequenceR.seqeqb 10 f1 f2;;

(* sum of a sequence：1 + 3 + 5 = 9 *)
let x = SequenceR.seqsum f1 3;;

(* get a sequence with two indexes：(i,j) *)
let g1 = fun (i : int) (j : int) -> (Float.of_int i, Float.of_int j);;
