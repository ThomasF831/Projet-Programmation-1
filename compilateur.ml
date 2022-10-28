open Format
open X86_64
open Analyse
;;

type mon_code = { mutable mon_texte: text; mutable mon_data: data};;

let empile x code =
  let c = { mon_texte = code.mon_texte ; mon_data = code.mon_data } in
  c.mon_texte <- pushq (imm x);
  c
;;

let addition code =
  let c = { mon_texte = code.mon_texte; mon_data = code.mon_data} in
  c.mon_texte <- c.mon_texte
                 ++ popq rsi
                 ++ popq rdi
                 ++ addq (reg rsi) (reg rdi)
                 ++ pushq (reg rdi);
  c
;;

let soustraction code =
  let c = { mon_texte = code.mon_texte; mon_data = code.mon_data} in
  c.mon_texte <- c.mon_texte
                 ++ popq rsi
                 ++ popq rdi
                 ++ subq (reg rsi) (reg rdi)
                 ++ pushq (reg rdi);
  c
;;

let multiplication code =
  let c = { mon_texte = code.mon_texte; mon_data = code.mon_data} in
  c.mon_texte <- c.mon_texte
                 ++ popq rsi
                 ++ popq rdi
                 ++ imulq (reg rsi) (reg rdi)
                 ++ pushq (reg rdi);
  c
;;

let division code =
  let c = { mon_texte = code.mon_texte; mon_data = code.mon_data} in
  c.mon_texte <- c.mon_texte
                 ++ popq rcx
                 ++ popq rax
                 ++ movq (imm 0) (reg rdx)
                 ++ idivq (reg rcx)
                 ++ pushq (reg rax);
  c
;;

let modulo code =
  let c = { mon_texte = code.mon_texte; mon_data = code.mon_data} in
  c.mon_texte <- c.mon_texte
                 ++ popq rcx
                 ++ popq rax
                 ++ movq (imm 0) (reg rdx)
                 ++ idivq (reg rcx)
                 ++ pushq (reg rdx);
  c
;;

exception Erreur_evaluation;;

let rec evaluation arbre = match arbre with
  | Entier x -> empile x { mon_texte = nop ; mon_data = nop }
  | Addition(x,y) -> let c1 = evaluation x in
                       let c2 = evaluation y in
                       let c = { mon_texte = c1.mon_texte ++ c2.mon_texte; mon_data = nop } in
                       addition c
  | Soustraction(x,y) -> let c1 = evaluation x in
                       let c2 = evaluation y in
                       let c = { mon_texte = c1.mon_texte ++ c2.mon_texte; mon_data = nop } in
                       soustraction c
  | Multiplication(x,y) -> let c1 = evaluation x in
                       let c2 = evaluation y in
                       let c = { mon_texte = c1.mon_texte ++ c2.mon_texte; mon_data = nop } in
                       multiplication c
  | Division(x,y) -> let c1 = evaluation x in
                       let c2 = evaluation y in
                       let c = { mon_texte = c1.mon_texte ++ c2.mon_texte; mon_data = nop } in
                       division c
  | Modulo(x,y) ->  let c1 = evaluation x in
                       let c2 = evaluation y in
                       let c = { mon_texte = c1.mon_texte ++ c2.mon_texte; mon_data = nop } in
                       modulo c
  | _ -> raise Erreur_evaluation
;;

let print_code code0 =
  let code = { mon_texte = code0.mon_texte ; mon_data = code0.mon_data } in
  let c = open_out "print.s" in
  let fmt = formatter_of_out_channel c in
  code.mon_texte <- globl "main"
                    ++ label "main"
                    ++ movq (imm 0) (reg rax)
                    ++ code.mon_texte
                    ++ popq rdi
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

let interprete s =
  let a = Analyse.arbre_syntaxique s in
  let c = evaluation a in
  print_code c
;;

interprete "2 + 3";;
