(*ESPRESSIONI*)
type ide = string;;
type exp = 
    (* tipi *)
    |Eint of int
    |Ebool of bool 
    |Estring of string
    |Edict of (ide * exp) list
    |Den of ide 
    (* operazioni numeriche *)
    |Prod of exp * exp 
    |Sum of exp * exp 
    |Diff of exp * exp
    |Eq of exp * exp
    |Minus of exp
    |IsZero of exp
    (* operazioni dizionari *)
    |Insert of ide * exp * exp
    |Delete of exp * ide
    |Has_Key of ide * exp
    |Iterate of exp * exp
    |Fold of exp * exp
    |Filter of (ide list) * exp
    (* operazioni booleane *)
    |Or of exp * exp 
    |And of exp * exp 
    |Not of exp 
    (* funzioni / flow control *)
    |Ifthenelse of exp * exp * exp 
    |Let of ide * exp * exp
    |Fun of ide * exp 
    |FunCall of exp * exp 
    |Letrec of ide * exp * exp


(*AMBIENTE POLIMORFO*)
type 't env = ide -> 't;;
let emptyenv (v : 't) = function x -> v;;
let applyenv (r : 't env) (i : ide) = r i;;
let bind (r : 't env) (i : ide) (v : 't) = function x -> if x = i then v else applyenv r x;;

(*TIPI ESPRIMIBILI*)
type evT = 
    |Int of int 
    |Bool of bool 
    |Unbound
    |String of string
    |DictVal of (ide * evT) list
    |FunVal of evFun 
    |RecFunVal of ide * evFun
and evFun = ide * exp * evT env

(*RTS*)
(*TYPE CHECKING*)
let typecheck (s : string) (v : evT) : bool = 
  match s with
    |"int" -> (match v with
                |Int(_) -> true
                |_ -> false)
    |"bool" -> (match v with
                 |Bool(_) -> true
                 |_ -> false) 
    |_ -> failwith("not a valid type");;

(*FUNZIONI PRIMITIVE*)
let prod x y = if (typecheck "int" x) && (typecheck "int" y)
  then (match (x,y) with
         |(Int(n),Int(u)) -> Int(n*u)
         |(_,_) -> failwith("Type error"))
  else failwith("Type error");;

let sum x y = if (typecheck "int" x) && (typecheck "int" y)
  then (match (x,y) with
         |(Int(n),Int(u)) -> Int(n+u)
         |(_,_) -> failwith("Type error"))
  else failwith("Type error");;

let diff x y = if (typecheck "int" x) && (typecheck "int" y)
  then (match (x,y) with
         |(Int(n),Int(u)) -> Int(n-u)
         |(_,_) -> failwith("Type error"))
  else failwith("Type error");;

let eq x y = if (typecheck "int" x) && (typecheck "int" y)
  then (match (x,y) with
         |(Int(n),Int(u)) -> Bool(n=u)
         |(_,_) -> failwith ("Type error"))
  else failwith("Type error");;

let minus x = if (typecheck "int" x) 
  then (match x with
         |Int(n) -> Int(-n)
         |_ -> failwith ("Type error"))
  else failwith("Type error");;

let iszero x = if (typecheck "int" x)
  then (match x with
         |Int(n) -> Bool(n=0)
         |_ -> failwith("Type error"))
  else failwith("Type error");;

let vel x y = if (typecheck "bool" x) && (typecheck "bool" y)
  then (match (x,y) with
         |(Bool(b),Bool(e)) -> (Bool(b||e))
         |(_,_) -> failwith("Type error"))
  else failwith("Type error");;

let et x y = if (typecheck "bool" x) && (typecheck "bool" y)
  then (match (x,y) with
         |(Bool(b),Bool(e)) -> Bool(b&&e)
         |(_,_) -> failwith("Type error"))
  else failwith("Type error");;

let non x = if (typecheck "bool" x)
  then (match x with
         |Bool(true) -> Bool(false)
         |Bool(false) -> Bool(true)
         |_ -> failwith("Type error"))
  else failwith("Type error");;

(*FUNZIONI DIZIONARI*)

(* restituisce true se la chiave è contenuta nella lista di coppie chiave-valore *)
let rec keyPresent (l: (ide * 'a) list) (c: ide) : bool = match l with
  |[] -> false
  |(i,e)::ls -> if i=c then true else keyPresent ls c;;

(* restituisce true se la chiave è contenuta nella lista di chiavi *)
let rec keyPresent2 (l: ide list) (c: ide) : bool = match l with
  |[] -> false
  |i::ls -> if i=c then true else keyPresent2 ls c;;

(* restituisce true se il dizionario rispetta l'unicità delle chiavi *)
let rec keyCheck (l: (ide * exp) list) : bool = match l with
  |[] -> true
  |(i,e)::ls -> if keyPresent ls i then false else keyCheck ls;;


(*EVAL(e)*)
let rec eval (e : exp) (r : evT env) : evT = 
  match e with
    |Eint n -> Int n
    |Ebool b -> Bool b
    |Estring s -> String s
    |Den i -> applyenv r i
    |IsZero a -> iszero (eval a r)
    |Eq(a, b) -> eq (eval a r) (eval b r)
    |Prod(a, b) -> prod (eval a r) (eval b r)
    |Sum(a, b) -> sum (eval a r) (eval b r)
    |Diff(a, b) -> diff (eval a r) (eval b r)
    |Minus a -> minus (eval a r)
    |And(a, b) -> et (eval a r) (eval b r)
    |Or(a, b) -> vel (eval a r) (eval b r)
    |Not a -> non (eval a r)
    |Ifthenelse(a, b, c) -> 
        let g = (eval a r) in
          if (typecheck "bool" g) 
          then (if g = Bool(true) then (eval b r) else (eval c r))
          else failwith ("nonboolean guard")
    |Let(i, e1, e2) -> eval e2 (bind r i (eval e1 r))
    |Fun(i, a) -> FunVal(i, a, r)
    |FunCall(f, eArg) -> let fClosure = (eval f r) in
          (match fClosure with
            |FunVal(arg, fBody, fDecEnv) -> 
                eval fBody (bind fDecEnv arg (eval eArg r))
            |RecFunVal(g, (arg, fBody, fDecEnv)) -> 
                let aVal = (eval eArg r) in
                let rEnv = (bind fDecEnv g fClosure) in
                let aEnv = (bind rEnv arg aVal) in
                  eval fBody aEnv
            |_ -> failwith("non functional value"))
    |Letrec(f, funDef, letBody) -> 
        (match funDef with
          |Fun(i, fBody) -> let r1 = (bind r f (RecFunVal(f, (i, fBody, r)))) in
                eval letBody r1
          |_ -> failwith("non functional def"))
    |Edict d -> if keyCheck d then DictVal(dictEval d r)
        else failwith ("keys must be unique")
    |Insert(i,e,d) -> let v = eval e r in
          (match (eval d r) with
            |DictVal(l) -> if keyPresent l i then failwith("key already present")
                else DictVal(insertKey l i v)
            |_ -> failwith("invalid dictionary"))
    |Delete(d,i) -> (match (eval d r) with
                      |DictVal(l) -> DictVal(deleteKey l i)
                      |_ -> failwith ("invalid dictionary"))
    |Has_Key(i,d) -> (match (eval d r) with
                       |DictVal(l) -> Bool(keyPresent l i)
                       |_ -> failwith("invalid dictionary"))
    |Iterate(f,d) -> (match (eval f r, eval d r) with
                       |(f,DictVal(l)) -> DictVal(apply f l)
                       |_ -> failwith("invalid dictionary"))
    |Fold(f,d) -> (match (eval f r, eval d r) with
                    |(f,DictVal(l)) -> let v = apply f l in
                          foldAux v
                    |_ -> failwith("invalid dictionary"))
    |Filter(kl,d) -> (match (eval d r) with
                       |DictVal(l) -> DictVal(filterKey l kl)
                       |_ -> failwith ("invalid dictionary"))

(* funzione ausiliaria per valutare tutti i valori associati agli identificatori del dizionario *)
and dictEval (l: (ide * exp) list) (r: evT env) : (ide * evT) list =
  match l with
    |[] -> []
    |(i,e)::ls -> let v= (eval e r) in (i,v)::(dictEval ls r)

(* funzione ausiliaria per inserire la nuova coppia chiave-valore (i,e) in un dizionario *)
and insertKey (l: (ide * evT) list) (i :ide) (v: evT) : (ide * evT) list = 
  l @ [(i,v)]

(* funzione ausiliaria per eliminare la chiave (i) da un dizionario *)
and deleteKey (l: (ide * evT) list) (i: ide) : (ide * evT) list =
  match l with
    |[] -> []
    |(i1,e1)::ls -> if i1=i then ls else (i1,e1)::(deleteKey ls i)

(* funzione ausiliaria per il metodo Iterate*)
and apply (f : evT) (l : (ide * evT) list) : (ide * evT) list = 
  match (f,l) with
    |(f1,[]) -> []
    |(FunVal(arg,body,r),(i,v)::ls) -> let v1 = try (eval body (bind r arg v)) 
                                         with error -> v in
          (i,v1)::(apply f ls)
    |(RecFunVal(g, (arg, body, r)),(i,v)::ls) -> let v1 = try (let rEnv = (bind r g f) in
                                                               let aEnv = (bind rEnv arg v) in
                                                                 eval body aEnv)
                                                   with error -> v in
          (i,v1)::(apply f ls)
    |_ -> failwith("invalid function")

(* funzione ausiliaria per il metodo Fold *)
and foldAux (l: (ide * evT) list) : evT = 
  match l with
    |[] -> Int(0)
    |(i,e)::ls -> if typecheck "int" e then sum e (foldAux ls)
        else (foldAux ls)

(* funzione ausiliaria per il metodo Filter *)
and filterKey (l: (ide * evT) list) (li: ide list) : (ide * evT) list =
  match l with
    |[] -> []
    |(i1,e1)::ls -> if keyPresent2 li i1 then (i1,e1)::(filterKey ls li)
        else filterKey ls li
;;
		
(* ==================== TESTS ==================== *)
(* basico: no let *)
let env0 = emptyenv Unbound;;

let e1 = FunCall(Fun("y", Sum(Den "y", Eint 2)), Eint 3);;
(** e1 = 5 **)
eval e1 env0;;

let e2 = FunCall(Let("x", Eint 4, Fun("y", Sum(Den "y", Den "x"))), Eint 3);;
(** e2 = 7 **)
eval e2 env0;;

(* ==================== TEST DICTIONARIES ==================== *)
let env0 = emptyenv Unbound;;

(* Dict *)
let d1 = Edict[("Angurie", Eint 5);("Pompelmi", Eint 3);("Ananas", Eint 4)];;
(** d1 = [(Angurie,5);(Pompelmi,3);(Ananas,4)] **)
eval d1 env0;;

let d2= Edict[("Mele", Estring "rosse");("Pere", Eint 2);("Meloni", Eint 7)];;
(** d2= [(Mele,rosse);(Pere,2);(Meloni,7)] **)
eval d2 env0;;

(* Dict Insert *)
let d3 = Insert("Banane", Eint 1, d1);;
(** d3 = [(Angurie,5);(Pompelmi,3);(Ananas,4);(Banane,1)] **)
eval d3 env0;;

(* Dict Delete *)
let d4 = Delete(d3,"Pompelmi");;
(** d4 = [(Angurie,5);(Ananas,4);(Banane,1)] **)
eval d4 env0;;

(* Dict Has_Key *)
let found1 = Has_Key("Ananas",d4);;
(** found1 = true **)
eval found1 env0;;

let found2 = Has_Key("Kiwi",d4);;
(** found2 = false **)
eval found2 env0;;

(* Dict Iterate *)
let incr = Fun("x",Sum(Den "x",Eint 1));;
let d5 = Iterate(incr,d4);;
(** d5 = [(Angurie,6);(ANanas,5);(Banane,2)] **)
eval d5 env0;;

let d6 = Iterate(incr,d2);;
(** d6 = [(Mele,rosse);(Pere,3);(Meloni,8)] **)
eval d6 env0;;

(* Dict Iterate - Rec *)
let sumx = Ifthenelse(Eq(Den "x",Eint 0),Eint 0,Sum(Den "x",FunCall(Den "f",Diff(Den "x",Eint 1))));;
let d7 = Letrec("f",Fun("x",sumx),Iterate(Den "f",d4));;
(** d7 = [(Angurie,15);(Ananas,10);(Banane,1)] **)
eval d7 env0;;

(* Dict Fold *)
let val1 = Fold(incr, d4);;
(** val1 = 13 **)
eval val1 env0;;

let val2= Fold(incr,d2);;
(** val2 = 11 **)
eval val2 env0;;

(* Dict Filter *)
let d8 = Filter(["Angurie"],d5);;
(** d8 = [(Angurie,6)] **)
eval d8 env0;;

let d9 = Filter([],d5);;
(** d9 = [] **)
eval d9 env0;;

let d10 = Filter(["Kiwi"],d5);;
(** d10 = [] **)
eval d10 env0;;
