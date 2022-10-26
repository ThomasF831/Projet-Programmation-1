open Format
open X86_64
;;

(*
   Fait : +, -, *, /, %, neg
   À faire: +., -., *., /., int, float
*)

type exp = I of int
         | F of float
         | P of exp
         | Neg of exp
         | Int of exp
         | Float of exp
         | Add0 of exp * exp
         | Add of exp
         | Sub0 of exp * exp
         | Sub of exp
         | Div0 of exp * exp
         | Div of exp
         | Mul0 of exp * exp
         | Mul of exp
         | Mod0 of exp * exp
         | Mod of exp
         | AddF of exp * exp
         | SubF of exp * exp
         | MulF of exp * exp
         | Parenthese of exp list
;;

type mon_code = { mutable mon_texte: text; mutable mon_data: data};;

exception Argument_non_I of exp;;


let cdc = String.make 1;; (* Convertit un char en string *)

let simplifie s =
  let t = ref "" in
  for i = 0 to (String.length s -1) do
    if s.[i] != ' ' then t := !t ^ (cdc s.[i]);
    if s.[i] ='.' && (s.[i-1] = '+' || s.[i-1] = '*' || s.[i-1] = '-') then t := !t ^ ",";
  done;
  !t
;;

let conversion_entier e = match e with
  | I x -> x
  | x -> raise (Argument_non_I x)
;;

let est_operation c = match c with
  | "+" | "-" | "*" | "/" | "%" | "," | "f" | "l" | "o" | "a" | "t" | "i" | "n" -> true
  | _ -> false
;;

let est_separe s i =
  if i = (String.length s)-1 || s.[i] = '(' || s.[i] = ')' then true
  else let f = est_operation in (f (cdc s.[i]) && (not (f (cdc s.[i+1])) ) || (not (f (cdc s.[i])) && f (cdc s.[i+1])) )
;;

let analyseur_lexical s0 =
  let s = simplifie s0 in
  let l = ref [] in
  let n = String.length s in
  let i = ref 0 in
  let w = ref "" in
  while !i < n-1 do
    (if (est_separe s (!i)) then (w := (!w)^(cdc s.[!i]);l := (!w)::(!l); w := "")
    else w := (!w)^(cdc s.[!i]));
    incr i
  done;
  if s.[n-1] = ')' then l := ")"::(!w)::(!l) else l := (!w)::(!l);
  List.rev !l
;;

exception Code_mal_parenthese;;
exception Code_mal_parenthese2;;

let rec parenthesage l = match l with
    | x::"+"::y::l -> let a,b = parenthesage l in Add0(I (int_of_string x),I (int_of_string y))::a,b
    | "+"::x::l -> let a,b = parenthesage l in Add(I (int_of_string x))::a,b
    | x::"-"::y::l -> let a,b = parenthesage l in Sub0(I (int_of_string x),I (int_of_string y))::a,b
    | "-"::x::l -> let a,b = parenthesage l in Sub(I (int_of_string x))::a,b
    | x::"*"::y::l -> let a,b = parenthesage l in Mul0(I (int_of_string x),I (int_of_string y))::a,b
    | "*"::x::l -> let a,b = parenthesage l in Mul(I (int_of_string x))::a,b
    | x::"/"::y::l -> let a,b = parenthesage l in Div0(I (int_of_string x),I (int_of_string y))::a,b
    | "/"::x::l -> let a,b = parenthesage l in Div(I (int_of_string x))::a,b
    | x::"%"::y::l -> let a,b = parenthesage l in Mod0(I (int_of_string x),I (int_of_string y))::a,b
    | "%"::x::l -> let a,b = parenthesage l in Mod(I (int_of_string x))::a,b
    | "("::x::")"::l -> parenthesage (x::l)
    | "("::l -> let a,b = parenthesage l in let c,d = parenthesage b in Parenthese(a)::c,d
    | ")"::l -> [],l
    | x::l -> let a,b = parenthesage l in I (int_of_string x)::(a),b
    | [] -> raise Code_mal_parenthese2
;;

let rec analyseur_syntaxique l = match l with
    | x::"+"::y::l -> Add0(I (int_of_string x),I (int_of_string y))::(analyseur_syntaxique l)
    | "+"::x::l -> Add(I (int_of_string x))::(analyseur_syntaxique l)
    | x::"-"::y::l -> Sub0(I (int_of_string x),I (int_of_string y))::(analyseur_syntaxique l)
    | "-"::x::l -> Sub(I (int_of_string x))::(analyseur_syntaxique l)
    | x::"*"::y::l -> Mul0(I (int_of_string x),I (int_of_string y))::(analyseur_syntaxique l)
    | "*"::x::l -> Mul(I (int_of_string x))::(analyseur_syntaxique l)
    | x::"/"::y::l -> Div0(I (int_of_string x),I (int_of_string y))::(analyseur_syntaxique l)
    | "/"::x::l -> Div(I (int_of_string x))::(analyseur_syntaxique l)
    | x::"%"::y::l -> Mod0(I (int_of_string x),I (int_of_string y))::(analyseur_syntaxique l)
    | "%"::x::l -> Mod(I (int_of_string x))::(analyseur_syntaxique l)
    | "("::x::")"::l -> analyseur_syntaxique (x::l)
    | "("::l -> let a,b = parenthesage l in Parenthese(a)::(analyseur_syntaxique b)
    | ")"::l -> raise Code_mal_parenthese
    | x::l -> I (int_of_string x)::(analyseur_syntaxique l)
    | [] -> []
;;

let add0 code e1 e2 =
  let x = conversion_entier e1 in
  let y = conversion_entier e2 in
  let c = { mon_texte = code.mon_texte; mon_data = code.mon_data} in
  c.mon_texte <- c.mon_texte
               ++ movq (imm x) (reg rsi)
               ++ movq (imm y) (reg rdi)
               ++ addq (reg rsi) (reg rdi);
  c
;;

let add code e1 =
  let y = conversion_entier e1 in
  let c = { mon_texte = code.mon_texte; mon_data = code.mon_data} in
  c.mon_texte <- c.mon_texte
                 ++ movq (reg r15) (reg rsi)
                 ++ movq (imm y) (reg rdi)
                 ++ addq (reg rsi) (reg rdi);
  c
;;

let sub0 code e1 e2 =
  let x = conversion_entier e1 in
  let y = conversion_entier e2 in
  let c = { mon_texte = code.mon_texte; mon_data = code.mon_data} in
  c.mon_texte <- c.mon_texte
                 ++ movq (imm x) (reg rdi)
                 ++ movq (imm y) (reg rsi)
                 ++ subq (reg rsi) (reg rdi);
  c
;;

let sub code e1 =
  let y = conversion_entier e1 in
  let c = { mon_texte = code.mon_texte; mon_data = code.mon_data} in
  c.mon_texte <- c.mon_texte
                 ++ movq (reg r15) (reg rdi)
                 ++ movq (imm y) (reg rsi)
                 ++ subq (reg rsi) (reg rdi);
  c
;;

let mul0 code e1 e2 =
  let x = conversion_entier e1 in
  let y = conversion_entier e2 in
  let c = { mon_texte = code.mon_texte; mon_data = code.mon_data} in
  c.mon_texte <- c.mon_texte
                 ++ movq (imm x) (reg rdi)
                 ++ movq (imm y) (reg rsi)
                 ++ imulq (reg rsi) (reg rdi);
  c
;;

let mul code e1 =
  let x = conversion_entier e1 in
  let c = { mon_texte = code.mon_texte; mon_data = code.mon_data} in
  c.mon_texte <- c.mon_texte
                 ++ movq (reg r15) (reg rdi)
                 ++ movq (imm x) (reg rsi)
                 ++ imulq (reg rsi) (reg rdi);
  c
;;

let div0 code e1 e2 =
  let x = conversion_entier e1 in
  let y = conversion_entier e2 in
  let c = { mon_texte = code.mon_texte; mon_data = code.mon_data} in
  c.mon_texte <- c.mon_texte
                 ++ movq (imm x) (reg rax)
                 ++ movq (imm 0) (reg rdx)
                 ++ movq (imm y) (reg rcx)
                 ++ idivq (reg rcx)
                 ++ movq (reg rax) (reg rdi);
  c
;;

let div code e1 =
  let x = conversion_entier e1 in
  let c = { mon_texte = code.mon_texte; mon_data = code.mon_data} in
  c.mon_texte <- c.mon_texte
                 ++ movq (reg r15) (reg rax)
                 ++ movq (imm 0) (reg rdx)
                 ++ movq (imm x) (reg rcx)
                 ++ idivq (reg rcx)
                 ++ movq (reg rax) (reg rdi);
  c
;;

let modl0 code e1 e2 =
  let x = conversion_entier e1 in
  let y = conversion_entier e2 in
  let c = { mon_texte = code.mon_texte; mon_data = code.mon_data} in
  c.mon_texte <- c.mon_texte
                 ++ movq (imm x) (reg rax)
                 ++ movq (imm 0) (reg rdx)
                 ++ movq (imm y) (reg rcx)
                 ++ idivq (reg rcx)
                 ++ movq (reg rdx) (reg rdi);
  c
;;

let modl code e1 =
  let x = conversion_entier e1 in
  let c = { mon_texte = code.mon_texte; mon_data = code.mon_data} in
  c.mon_texte <- c.mon_texte
                 ++ movq (reg r15) (reg rax)
                 ++ movq (imm 0) (reg rdx)
                 ++ movq (imm x) (reg rcx)
                 ++ idivq (reg rcx)
                 ++ movq (reg rdx) (reg rdi);
  c
;;

let eval s =
  let a = List.rev (analyseur_syntaxique( analyseur_lexical s)) in
  let rec aux a = match a with
    | Add0(e1,e2)::l -> let c = add0 (aux l) e1 e2 in
                    c.mon_texte <- c.mon_texte ++ movq (reg rdi) (reg r15);
                    c
    | Add(e1)::l -> let c = aux l in let c2 = (add c e1) in
                                     c2.mon_texte <- c2.mon_texte ++  movq (reg rdi) (reg r15);
                                     c2
    | Sub0(e1,e2)::l ->  let c = sub0 (aux l) e1 e2 in
                    c.mon_texte <- c.mon_texte ++ movq (reg rdi) (reg r15);
                    c
    | Sub(e1)::l -> let c = aux l in let c2 = (sub c e1) in
                                     c2.mon_texte <- c2.mon_texte ++  movq (reg rdi) (reg r15);
                                     c2
    | Mul0(e1,e2)::l ->  let c = mul0 (aux l) e1 e2 in
                    c.mon_texte <- c.mon_texte ++ movq (reg rdi) (reg r15);
                    c
    | Mul(e1)::l -> let c = aux l in let c2 = (mul c e1) in
                                     c2.mon_texte <- c2.mon_texte ++  movq (reg rdi) (reg r15);
                                     c2
    | Div0(e1,e2)::l ->   let c = div0 (aux l) e1 e2 in
                    c.mon_texte <- c.mon_texte ++ movq (reg rdi) (reg r15);
                    c
    | Div(e1)::l -> let c = aux l in let c2 = (div c e1) in
                                     c2.mon_texte <- c2.mon_texte ++  movq (reg rdi) (reg r15);
                                     c2
    | Mod0(e1,e2)::l ->   let c = modl0 (aux l) e1 e2 in
                    c.mon_texte <- c.mon_texte ++ movq (reg rdi) (reg r15);
                    c
    | Mod(e1)::l -> let c = aux l in let c2 = (modl c e1) in
                                     c2.mon_texte <- c2.mon_texte ++  movq (reg rdi) (reg r15);
                                     c2
    | Parenthese(ll)::l -> let c1 = aux ll in let c2 = aux l in
                                              c2.mon_texte <- c2.mon_texte ++ c1.mon_texte;
                                              c2
    | [] -> { mon_texte = nop;
              mon_data = nop}
    | [e1] -> { mon_texte = movq (imm (conversion_entier e1)) (reg r15); mon_data = nop }
    | _ -> failwith "Erreur eval"
  in let c = open_out "print.s" in
     let fmt = formatter_of_out_channel c in
     let code = aux a in
     code.mon_texte <- globl "main"
                       ++ label "main"
                       ++ movq (imm 0) (reg r15)
                       ++ code.mon_texte
                       ++ movq (reg r15) (reg rdi)
                       ++ call "print_int"
                       ++ ret
                       ++ label "print_int"
                       ++ movq (reg rdi) (reg rsi)
                       ++ movq (ilab "message") (reg rdi)
                       ++ call "printf";
     code.mon_data <- label "message" ++ string "%d\n";
     let codefinal = {text = code.mon_texte; data = code.mon_data} in
     X86_64.print_program fmt (codefinal);
     close_out c
;;

eval "12 + (5 * 3)";;
