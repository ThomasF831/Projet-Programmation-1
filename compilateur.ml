open Format
open X86_64
open Analyse
open Lecture_fichier
;;

(* On crée un type identique au type code de x86_64.ml mais dont les champs sont mutables *)
type mon_code = { mutable mon_texte: text; mutable mon_data: data};;


(* Compte le nombre de flottants utilisés jusqu'à présent (pour pouvoir les appeler float"i" *)
let nbr_float = ref 0;;

(* Partie du code où on déclare tous les flottants. On la garde  à l'extérieur du code car on doit la placer avant le main et donc ce ne serait pas pratique *)
let declare_float = ref "";;

(* Modifie le code assembleur pour que x soit placé sur la pile *)
let empile x code =
  let c = { mon_texte = code.mon_texte ; mon_data = code.mon_data } in
  c.mon_texte <- pushq (imm x);
  c
;;

(* Modifie le code assembleur pour faire l'addition des deux éléments les plus bas dans la pile *)
let addition code =
  let c = { mon_texte = code.mon_texte; mon_data = code.mon_data} in
  c.mon_texte <- c.mon_texte
                 ++ popq rsi
                 ++ popq rdi
                 ++ addq (reg rsi) (reg rdi)
                 ++ pushq (reg rdi);
  c
;;

(* Pareil pour la soustraction *)
let soustraction code =
  let c = { mon_texte = code.mon_texte; mon_data = code.mon_data} in
  c.mon_texte <- c.mon_texte
                 ++ popq rsi
                 ++ popq rdi
                 ++ subq (reg rsi) (reg rdi)
                 ++ pushq (reg rdi);
  c
;;

(* Pareil pour la multiplication *)
let multiplication code =
  let c = { mon_texte = code.mon_texte; mon_data = code.mon_data} in
  c.mon_texte <- c.mon_texte
                 ++ popq rsi
                 ++ popq rdi
                 ++ imulq (reg rsi) (reg rdi)
                 ++ pushq (reg rdi);
  c
;;

(* Pareil pour la division *)
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

(* Pareil pour le modulo *)
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

(* Code pour utiliser facilement les opérations sur les piles avec la fausse pile utilisée pour les flottants *)
let pushfloat () = inline "        movsd %xmm0, -8(%rsp)\n        subq $8, %rsp\n";;
let popfloat reg = inline ("        movsd (%rsp), "^reg^"\n        addq $8, %rsp\n");;

(* Modifie le code pour que x soit placé sur la fausse pile utilisée pour les flottants *)
let empileF x code =
  let c = { mon_texte = code.mon_texte ; mon_data = code.mon_data } in
  c.mon_texte <-  c.mon_texte
	          ++ inline ("        movsd float"^(string_of_int (!nbr_float))^" (%rip), %xmm0\n")
                  ++ pushfloat ();
                  declare_float := (!declare_float)^"\nfloat"^(string_of_int !nbr_float)^":\n        .double "^(string_of_float x)^"\n\n";
  incr nbr_float;
  c
;;

(* Modifie le code pour faire l'addition des deux éléments les plus bas sur la fausse pile des flottants *)
let additionF code =
  let c = { mon_texte = code.mon_texte; mon_data = code.mon_data} in
  c.mon_texte <- c.mon_texte
                 ++ popfloat "%xmm0"
                 ++ popfloat "%xmm1"
                 ++ inline "        addsd %xmm1, %xmm0\n"
                 ++ pushfloat();
  c;;

(* Pareil pour la soustraction *)
let soustractionF code =
  let c = { mon_texte = code.mon_texte; mon_data = code.mon_data} in
  c.mon_texte <- c.mon_texte
                 ++ popfloat "%xmm1"
                 ++ popfloat "%xmm0"
                 ++ inline "        subsd %xmm1, %xmm0\n"
                 ++ pushfloat();
  c;;

(* Pareil pour la multiplication *)
let multiplicationF code =
  let c = { mon_texte = code.mon_texte; mon_data = code.mon_data} in
  c.mon_texte <- c.mon_texte
                 ++ popfloat "%xmm0"
                 ++ popfloat "%xmm1"
                 ++ inline "        mulsd %xmm1, %xmm0\n"
                 ++ pushfloat();
  c;;

exception Erreur_evaluation;;

(* Parcourt l'arbre de sorte que les bouts de code assembleur correspondant aux opérations soient écrites dans le bon ordre *)
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

(* Modifie le code assembleur pour qu'il affiche l'élément le plus bas de la pile et l'écrit dans le fichier print.s *)
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
  let codefinal = {text = code.mon_texte; data = code.mon_data} in (* On doit revenir à un élément de type code pour pouvoir écrire dans le fichier *)
  X86_64.print_program fmt (codefinal);
  close_out c
;;

(* Modifie le code assembleur pour qu'il affiche l'élément le plus bas de la fausse pile des flottants et l'écrit dans le fichier print.s *)
let print_code_flottant code0 =
  let code = { mon_texte = code0.mon_texte ; mon_data = code0.mon_data } in
  let c = open_out "print.s" in
  let fmt = formatter_of_out_channel c in
  code.mon_texte <- globl "main"
                    ++ inline !declare_float (* Ici on ajoute toutes les déclarations de flottants avant le main *)
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

(* Permet de savoir si on doit afficher un flottant ou un entier *)
let rec typ arbre = match arbre with
  | Addition(x,y) | Soustraction(x,y) | Multiplication(x,y) | Division(x,y) | Modulo(x,y) -> true
  | _ -> false
;;

(* Écrit le code assembleur correspondant à s dans le fichier print.s *)
let interprete s =
  let a = Analyse.arbre_syntaxique s in
  let t = typ a in
  let c = evaluation a in
  if t then print_code_entier c else print_code_flottant c;;
;;

(* Écrit le code assembleur correspondant au contenu de fichier.exp dans le fichier print.s où fichier.exp est le nom de fichier passé en argument de ./Aritha *)
interprete (extraire_string ());;
