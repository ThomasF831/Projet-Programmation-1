open Format
open X86_64

type exp = I of int
         | F of float
         | P of exp
         | Pos of int
         | Neg of exp
         | Int of exp
         | Float of exp
         | Add of exp * exp
         | Sub of exp * exp
         | Div of exp * exp
         | Mul of exp * exp
         | Mod of exp * exp
         | AddF of exp * exp
         | SubF of exp * exp
         | MulF of exp * exp
;;

exception Argument_non_I of exp;;

let conversion_entier e = match e with
  | I x -> x
  | x -> raise (Argument_non_I x)
;;

let cdc = String.make 1;; (* Convertit un char en string *)

let analyseur_lexical s =
  let l = ref [] in
  let n = String.length s in
  let i = ref 0 in
  let w = ref "" in
  while !i < n do
    (if cdc s.[!i] = " " then (l := (!w)::(!l); w := "")
    else w := (!w)^(cdc s.[!i]));
    incr i
  done;
  l := (!w)::(!l);
  List.rev !l
;;

let rec analyseur_syntaxique l = match l with
    | x::"+"::y::l -> Add(I (int_of_string x),I (int_of_string y))
    | _ -> failwith "..."
;;

let add e1 e2 =
  let x = conversion_entier e1 in
  let y = conversion_entier e2 in
  let code = { text =
                 globl "main"
                 ++ label "main"
                 ++ movq (imm x) (reg rsi)
                 ++ movq (imm y) (reg rdi)
                 ++ call "print_int"
                 ++ ret
                 ++ label "print_int"
                 ++ movq (reg rdi) (reg rsi)
                 ++ movq (ilab "message") (reg rdi)
                 ++ call "printf";
               data =
                 label "message"
                 ++ string "%d"
             }
  in code
;;

let eval s =
  let a = analyseur_syntaxique( analyseur_lexical s) in
  let aux a = match a with
    | Add(e1,e2) -> add e1 e2
    | _ -> failwith "Erreur eval"
  in let c = open_out "print.s" in
     let fmt = formatter_of_out_channel c in
     X86_64.print_program fmt (aux a);
     close_out c
;;

eval "5 + 9";;
