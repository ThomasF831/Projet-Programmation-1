type exp = I of int
         | F of float
         | P of exp
         (* | In of exp
          * | Fl of exp *)
         | Add0 of exp * exp
         | Add of exp
         | AddF0 of exp * exp
         | AddF of exp
         | Sub0 of exp * exp
         | Sub of exp
         | SubF0 of exp * exp
         | SubF of exp
         | Div0 of exp * exp
         | Div of exp
         | Mul0 of exp * exp
         | Mul of exp
         | MulF0 of exp * exp
         | MulF of exp
         | Mod0 of exp * exp
         | Mod of exp
         | Parenthese of exp list
;;

type arbre = Entier of int
           | Flottant of float
           | Addition of arbre * arbre
           | Soustraction of arbre * arbre
           | Multiplication of arbre * arbre
           | Division of arbre * arbre
           | Modulo of arbre * arbre
           | AdditionF of arbre * arbre
           | SoustractionF of arbre * arbre
           | MultiplicationF of arbre * arbre
           (* | Int of abre
            * | Float of arbre *)
;;

exception Argument_non_I of exp;;


let cdc = String.make 1;; (* Convertit un char en string *)

let simplifie s =
  let t = ref "" in
  let suppr = ref 0 in 
  for i = 0 to (String.length s -1) do
    if !suppr > 0 then decr suppr else
    begin
      if s.[i] = 'f' then suppr := 4;
      if s.[i] = 'i' then suppr := 2;
      if s.[i] != ' ' && s.[i] != '.' then t := !t ^ (cdc s.[i]);
      if s.[i] ='.' then (if (s.[i-1] = '+' || s.[i-1] = '*' || s.[i-1] = '-') then t := !t ^ "," else t := !t ^ ".");
    end;
  done;
  !t
;;

let conversion_entier e = match e with
  | I x -> x
  | x -> raise (Argument_non_I x)
;;

let est_operation c = match c with
  | "+" | "-" | "*" | "/" | "%" | "," -> true
  | _ -> false
;;

let est_separe s i =
  if i = (String.length s)-1 || s.[i] = '(' || s.[i] = ')' || s.[i+1] = '(' || s.[i+1] = ')' || s.[i] = 'f' || s.[i] = 'i' then true
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
  if n >= 2 && (est_separe s (n-2)) then l := (cdc s.[n-1]::(!l)) else l := ((!w)^(cdc s.[n-1]))::(!l);
  List.rev (!l)
;;

exception Code_mal_parenthese;;
exception Code_mal_parenthese2;;

let cdr_a_exp x = try (I (int_of_string x)) with Failure _ -> (F (float_of_string x));;

let rec parenthesage l = match l with
    | "("::x::")"::l -> parenthesage (x::l)
    | "("::l -> let a,b = parenthesage l in let c,d = parenthesage b in Parenthese(a)::c,d
    | ")"::l -> [],l
    | x::"+"::y::l -> let a,b = parenthesage l in Add0(I (int_of_string x),I (int_of_string y))::a,b
    | "+"::x::l -> let a,b = parenthesage l in Add(I (int_of_string x))::a,b
    | x::"+,"::y::l -> let a,b = parenthesage l in AddF0(F (float_of_string x),F (float_of_string y))::a,b
    | "+,"::x::l -> let a,b = parenthesage l in AddF(F (float_of_string x))::a,b                                    
    | x::"-"::y::l -> let a,b = parenthesage l in Sub0(I (int_of_string x),I (int_of_string y))::a,b
    | "-"::x::l -> let a,b = parenthesage l in Sub(I (int_of_string x))::a,b
    | x::"-,"::y::l -> let a,b = parenthesage l in SubF0(F (float_of_string x),F (float_of_string y))::a,b
    | "-,"::x::l -> let a,b = parenthesage l in SubF(F (float_of_string x))::a,b                               
    | x::"*"::y::l -> let a,b = parenthesage l in Mul0(I (int_of_string x),I (int_of_string y))::a,b
    | "*"::x::l -> let a,b = parenthesage l in Mul(I (int_of_string x))::a,b
    | x::"*,"::y::l -> let a,b = parenthesage l in MulF0(F (float_of_string x),F (float_of_string y))::a,b
    | "*,"::x::l -> let a,b = parenthesage l in MulF(F (float_of_string x))::a,b
    | x::"/"::y::l -> let a,b = parenthesage l in Div0(I (int_of_string x),I (int_of_string y))::a,b
    | "/"::x::l -> let a,b = parenthesage l in Div(I (int_of_string x))::a,b
    | x::"%"::y::l -> let a,b = parenthesage l in Mod0(I (int_of_string x),I (int_of_string y))::a,b
    | "%"::x::l -> let a,b = parenthesage l in Mod(I (int_of_string x))::a,b
    (* | "f"::x::l -> let a,b = parenthesage l in Fl(I (int_of_string x))::a,b
     * | "i"::x::l -> let a,b = parenthesage l in In(F (float_of_string x))::a,b *)
    | x::l -> let a,b = parenthesage l in (cdr_a_exp x)::(a),b
    | [] -> raise Code_mal_parenthese2
;;

let rec analyseur_syntaxique l = match l with
    | "("::x::")"::l -> analyseur_syntaxique (x::l)
    | "("::l -> let a,b = parenthesage l in Parenthese(a)::(analyseur_syntaxique b)
    | ")"::l -> raise Code_mal_parenthese
    | x::"+"::"("::l -> let a,b = parenthesage l in Add0(I (int_of_string x),Parenthese(a))::(analyseur_syntaxique b)
    | x::"+"::y::l -> Add0(I (int_of_string x),I (int_of_string y))::(analyseur_syntaxique l)
    | "+"::"("::l -> let a,b = parenthesage l in  Add(Parenthese a)::(analyseur_syntaxique b)
    | "+"::x::l -> Add(I (int_of_string x))::(analyseur_syntaxique l)
    | x::"+,"::"("::l -> let a,b = parenthesage l in AddF0(F (float_of_string x),Parenthese(a))::(analyseur_syntaxique b)
    | x::"+,"::y::l -> AddF0(F (float_of_string x),F (float_of_string y))::(analyseur_syntaxique l)
    | "+,"::"("::l -> let a,b = parenthesage l in  AddF(Parenthese a)::(analyseur_syntaxique b)
    | "+,"::x::l -> AddF(F (float_of_string x))::(analyseur_syntaxique l)
    | x::"-"::"("::l -> let a,b = parenthesage l in Sub0(I (int_of_string x),Parenthese(a))::(analyseur_syntaxique b)
    | x::"-"::y::l -> Sub0(I (int_of_string x),I (int_of_string y))::(analyseur_syntaxique l)
    | "-"::"("::l -> let a,b = parenthesage l in  Sub(Parenthese a)::(analyseur_syntaxique b)
    | "-"::x::l -> Sub(I (int_of_string x))::(analyseur_syntaxique l)
    | x::"-,"::"("::l -> let a,b = parenthesage l in SubF0(F (float_of_string x),Parenthese(a))::(analyseur_syntaxique b)
    | x::"-,"::y::l -> SubF0(F (float_of_string x),F (float_of_string y))::(analyseur_syntaxique l)
    | "-,"::"("::l -> let a,b = parenthesage l in  SubF(Parenthese a)::(analyseur_syntaxique b)
    | "-,"::x::l -> SubF(F (float_of_string x))::(analyseur_syntaxique l)
    | x::"*"::"("::l -> let a,b = parenthesage l in Mul0(I (int_of_string x),Parenthese(a))::(analyseur_syntaxique b)
    | x::"*"::y::l -> Mul0(I (int_of_string x),I (int_of_string y))::(analyseur_syntaxique l)
    | "*"::"("::l -> let a,b = parenthesage l in  Mul(Parenthese a)::(analyseur_syntaxique b)
    | "*"::x::l -> Mul(I (int_of_string x))::(analyseur_syntaxique l)
    | x::"*,"::"("::l -> let a,b = parenthesage l in MulF0(F (float_of_string x),Parenthese(a))::(analyseur_syntaxique b)
    | x::"*,"::y::l -> MulF0(F (float_of_string x),F (float_of_string y))::(analyseur_syntaxique l)
    | "*,"::"("::l -> let a,b = parenthesage l in  MulF(Parenthese a)::(analyseur_syntaxique b)
    | "*,"::x::l -> MulF(F (float_of_string x))::(analyseur_syntaxique l)
    | x::"/"::"("::l -> let a,b = parenthesage l in Div0(I (int_of_string x),Parenthese(a))::(analyseur_syntaxique b)
    | x::"/"::y::l -> Div0(I (int_of_string x),I (int_of_string y))::(analyseur_syntaxique l)
    | "/"::"("::l -> let a,b = parenthesage l in  Div(Parenthese a)::(analyseur_syntaxique b)
    | "/"::x::l -> Div(I (int_of_string x))::(analyseur_syntaxique l)
    | x::"%"::"("::l -> let a,b = parenthesage l in Mod0(I (int_of_string x),Parenthese(a))::(analyseur_syntaxique b)
    | x::"%"::y::l -> Mod0(I (int_of_string x),I (int_of_string y))::(analyseur_syntaxique l)
    | "%"::"("::l -> let a,b = parenthesage l in  Mod(Parenthese a)::(analyseur_syntaxique b)
    | "%"::x::l -> Mod(I (int_of_string x))::(analyseur_syntaxique l)
    (* | "f"::"("::l -> let a,b = parenthesage l in Fl(Parenthese a)::(analyseur_syntaxique b)
     * | "f"::x::l -> Fl(I (int_of_string x))::(analyseur_syntaxique l)
     * | "i"::"("::l -> let a,b = parenthesage l in In(Parenthese a)::(analyseur_syntaxique b)
     * | "i"::x::l -> In(F (float_of_string x))::(analyseur_syntaxique l) *) 
    | x::l -> (cdr_a_exp x)::(analyseur_syntaxique l)
    | [] -> []
;;

let analyser x = analyseur_syntaxique(analyseur_lexical x);;

let rec exp_a_arbre exp = match exp with
  | (I x) -> Entier x
  | (F x) -> Flottant x
  | Add0(x,y) -> Addition(exp_a_arbre x,exp_a_arbre y)
  | Sub0(x,y) -> Soustraction(exp_a_arbre x, exp_a_arbre y)
  | Mul0(x,y) -> Multiplication(exp_a_arbre x,exp_a_arbre y)
  | Div0(x,y) -> Division(exp_a_arbre x,exp_a_arbre y)
  | Mod0(x,y) -> Modulo(exp_a_arbre x,exp_a_arbre y)
  | AddF0(x,y) -> AdditionF(exp_a_arbre x,exp_a_arbre y)
  | SubF0(x,y) -> SoustractionF(exp_a_arbre x, exp_a_arbre y)
  | MulF0(x,y) -> MultiplicationF(exp_a_arbre x,exp_a_arbre y)
  | Parenthese(l) -> fabrique_arbre l
  (* | Fl x -> Float(exp_a_arbre x)
   * | In x -> Int(exp_a_arbre x) *)
  | _ -> Entier 0
and fabrique_arbre l =
  let a = ref (Entier 0) in
  let rec aux l = match l with
    | Parenthese(l)::ll -> a := fabrique_arbre l; aux ll
    | (Add e)::l -> a := Addition(!a, exp_a_arbre e); aux l
    | (Sub e)::l -> a := Soustraction(!a, exp_a_arbre e); aux l
    | (Mul e)::l -> a := Multiplication(!a, exp_a_arbre e); aux l
    | (Div e)::l -> a := Division(!a, exp_a_arbre e); aux l
    | (Mod e)::l -> a := Modulo(!a, exp_a_arbre e); aux l
    | (AddF e)::l -> a := AdditionF(!a, exp_a_arbre e); aux l
    | (SubF e)::l -> a := SoustractionF(!a, exp_a_arbre e); aux l
    | (MulF e)::l -> a := MultiplicationF(!a, exp_a_arbre e); aux l
    | e::l -> a := exp_a_arbre e; aux l
    | [] -> !a
  in aux l
;;


let arbre_syntaxique s = fabrique_arbre (analyser s);;
