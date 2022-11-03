(*
  purpose   : Test matrix ocaml program which extracted from Coq
  author    : ZhengPu Shi
  date      : Nov 1, 2022

 *)

(** These lines only for REPL, should be commented for compile *)
#use "topfind";;
#require "unix";;
#use "deplist.ml";;
(* #load "deplist.cmo";; *)

open Unix
open Deplist
open MatrixNat

(* 精度为秒的当前时间的整数 *)
let current_time_get = Float.to_int (Unix.time ());;

(* 更新随机数生成器 *)
let random_update = Random.init (current_time_get);;

(* 生成 m * n 的二重列表 *)
let gen_dlist (m:int) (n:int) : int list list =
  let max = m * n * 10 in
  random_update;
  List.init m (fun _ -> List.init n (fun _ -> Random.int max))

let _ = l2m (gen_dlist 5 4) 5 4;;
let _ = gen_dlist 5 4;;

let _ = gen_dlist 5 3;;


(** matrix model types *)
type matmodel =
  | DL | DP | DR | NF | FF

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

