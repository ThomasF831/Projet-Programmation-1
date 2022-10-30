let t = Sys.argv;;

let extraire_string () =
  let f = open_in (t.(1)^".txt") in
  let s = input_line f in
  close_in f;
  s
;;
