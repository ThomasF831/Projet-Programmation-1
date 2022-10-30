open Format
open X86_64
open Analyse
;;

type mon_code = { mutable mon_texte: text; mutable mon_data: data};;

let nbr_float = ref 0;;

let declare_float = ref "";;

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

let pushfloat () = inline "        movsd %xmm0, -8(%rsp)\n        subq $8, %rsp\n";;
let popfloat reg = inline ("        movsd (%rsp), "^reg^"\n        addq $8, %rsp\n");;

let empileF x code =
  let c = { mon_texte = code.mon_texte ; mon_data = code.mon_data } in
  c.mon_texte <-  c.mon_texte
	          ++ inline ("        movsd float"^(string_of_int (!nbr_float))^" (%rip), %xmm0\n")
                  ++ pushfloat ();
                  declare_float := (!declare_float)^"\nfloat"^(string_of_int !nbr_float)^":\n        .double "^(string_of_float x)^"\n\n";
  incr nbr_float;
  c
;;

let additionF code =
  let c = { mon_texte = code.mon_texte; mon_data = code.mon_data} in
  c.mon_texte <- c.mon_texte
                 ++ popfloat "%xmm0"
                 ++ popfloat "%xmm1"
                 ++ inline "        addsd %xmm1, %xmm0\n"
                 ++ pushfloat();
  c;;

let soustractionF code =
  let c = { mon_texte = code.mon_texte; mon_data = code.mon_data} in
  c.mon_texte <- c.mon_texte
                 ++ popfloat "%xmm1"
                 ++ popfloat "%xmm0"
                 ++ inline "        mulsd %xmm1, %xmm0\n"
                 ++ pushfloat();
  c;;

let multiplicationF code =
  let c = { mon_texte = code.mon_texte; mon_data = code.mon_data} in
  c.mon_texte <- c.mon_texte
                 ++ popfloat "%xmm0"
                 ++ popfloat "%xmm1"
                 ++ inline "        mulsd %xmm1, %xmm0\n"
                 ++ pushfloat();
  c;;

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
  | Flottant x -> empileF x { mon_texte = nop ; mon_data = nop }
  | AdditionF(x,y) -> let  c1 = evaluation x in
                       let c2 = evaluation y in
                       let c = { mon_texte = c1.mon_texte ++ c2.mon_texte; mon_data = nop } in
                       additionF c
  | SoustractionF(x,y) -> let  c1 = evaluation x in
                       let c2 = evaluation y in
                       let c = { mon_texte = c1.mon_texte ++ c2.mon_texte; mon_data = nop } in
                       soustractionF c
  | MultiplicationF(x,y) ->  let  c1 = evaluation x in
                       let c2 = evaluation y in
                       let c = { mon_texte = c1.mon_texte ++ c2.mon_texte; mon_data = nop } in
                       multiplicationF c
;;

let print_code_entier code0 =
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

let print_code_flottant code0 =
  let code = { mon_texte = code0.mon_texte ; mon_data = code0.mon_data } in
  let c = open_out "print.s" in
  let fmt = formatter_of_out_channel c in
  code.mon_texte <- globl "main"
                    ++ inline !declare_float
                    ++ label "main"
                    ++ code.mon_texte
                    ++ popfloat "%xmm0"
                    ++ call "print_float"
                    ++ movq (imm 0) (reg rax)
                    ++ inline "        ret\n\n"
                    ++ label"print_float"
                    ++ inline
"        movl $message, %edi\n        movq $1, %rax\n        call printf\n        ret\n\n        .data\n        message:\n        .string \"%f\\n\"\n";
  let codefinal = {text = code.mon_texte; data = nop} in
  X86_64.print_program fmt (codefinal);
  close_out c
;;

let rec typ arbre = match arbre with
  | Addition(x,y) | Soustraction(x,y) | Multiplication(x,y) | Division(x,y) | Modulo(x,y) -> true
  | _ -> false
;;

let interprete s =
  let a = Analyse.arbre_syntaxique s in
  let t = typ a in
  let c = evaluation a in
  if t then print_code_entier c else print_code_flottant c;;
;;

interprete "(2.3 +. 8.4)*. 8.2";;
