(*
  purpose   : Test matrix ocaml program which extracted from Coq
  author    : ZhengPu Shi
  date      : Nov 1, 2022

 *)

(** These lines only for REPL, should be commented for compile *)
(* #use "topfind";; *)
(* #require "unix";; *)
(* #use "mymatrix.ml";; *)
(* #load "mymatrix.cmo";; *)

open Mymatrix;;
open Unix;;

(** 精度为秒的当前时间的整数 *)

let current_time_get = Float.to_int (Unix.time ())

(** 更新随机数生成器 *)
let random_update = Random.init (current_time_get)

(** 生成 m * n 的列表 *)
let dl_gen (m:int) (n:int) : float list list =
  let max = Float.of_int (m * n * 10) in
  random_update;
  List.init m (fun _ -> List.init n (fun _ -> Random.float max));;

(** matrix model types *)
(* type matmodel = *)
(*   | DL | DP | DR | NF | FF *)

(** 打印嵌套列表到字符串 *)
let dl2str (dl:'a list list) (a2str:'a -> string) : string =
  let l2str l = List.fold_left (fun s i -> s^(a2str i)) "" l in
  List.fold_left (fun s l -> s^(l2str l)^"\n") "" dl;;

(** 打印嵌套实数列表到字符串 *)
let float_dl2str (dl:float list list) : string =
  dl2str dl (Printf.sprintf "%10.2f");;

(** 测试 *)
let float_dl2str_test =
  let l1 : float list list = [[1.2;3.5];[4.234;234.234324]] in
  print_endline (float_dl2str l1);;

(* #show_type Matrix.RbaseSymbolsImpl.coq_R;; *)
(* #show_type coq_R;; *)
(* let _ : Matrix.RbaseSymbolsImpl.coq_R = 3.1;; *)
(* let _ : Matrix.FieldR.FieldDefR.coq_X = 3.1;; *)

(** 矩阵相乘 *)
let test =
  let r = 5 in
  let c = 4 in
  let s = 6 in
  let l1 = dl_gen r c in
  let l2 = dl_gen c s in
  let m1 = DL.l2m r c l1 in
  let m2 = DL.l2m c s l2 in
  let m3 = DL.mmul r c s m1 m2 in
  let l3 = DL.m2l r c m3 in
  print_endline (Printf.sprintf "A_%dx%d:\n" r c);
  print_endline (float_dl2str l1);
  print_endline (Printf.sprintf "B_%dx%d:\n" c s);
  print_endline (float_dl2str l1);
  print_endline (Printf.sprintf "AxB_%dx%d:\n" r s);
  print_endline (float_dl2str l3);;


(** command option processing *)

(* global variables for command options. *)
let cmdopt_matrix_size : int ref = ref 10

(* global variable setting functions. *)
let set_matrix_size (i:int)   = cmdopt_matrix_size := i

let read_options () : string =
  let speclist =
    [
      ("-matrix_size", Arg.Int set_matrix_size, "Matrix size");
    ]
  in
  let usage_msg = "Usage: ./test [option] where options are:" in
  let _ = Arg.parse speclist (fun s -> ()) usage_msg in
  ""

let main () =
  let _ = read_options () in
  (* let matrix_size = !cmdopt_matrix_size in *)
  print_endline "ok";
  ();;
  
main ();;

