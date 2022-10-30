(* lorsqu'on appelle ./Aritha "fichier.exp", t = [|"./Aritha","fichier.exp" *)
let t = Sys.argv;;

(* extraire_string ouvre fichier.exp.txt et renvoie le texte qu'il contient *)
let extraire_string () =
  let f = open_in (t.(1)^".txt") in
  let s = input_line f in
  close_in f;
  s
;;
