open CTreeDefinitions;;
open ExtrOcamlIntConv;;
open ImpBrEx;;
open Datatypes;;
open Printf;;

let choose2 () =
  if Random.int 2 = 1 then Coq_true else Coq_false;;

let rec run t =
  match observe t with
  | RetF r -> print_int (int_of_nat r)
  | VisF (_e, _k) -> failwith "Vis (unreachable)"
  | BrF (_b, c, k) ->
    match c with
    | (* B0 *) Coq_inl _ -> failwith "Stuck"
    | (* B1 *) Coq_inr (Coq_inl _) -> run (k (Obj.magic Coq_tt))
    | (* B2 *) Coq_inr (Coq_inr _) -> run (k (Obj.magic choose2()));;

let rec collect t =
  match observe t with
  | RetF r -> [int_of_nat r]
  | VisF (_e, _k) -> failwith "Vis (unreachable)"
  | BrF (_b, c, k) ->
    match c with
    | (* B0 *) Coq_inl _ -> []
    | (* B1 *) Coq_inr (Coq_inl _) -> collect (k (Obj.magic Coq_tt))
    | (* B2 *) Coq_inr (Coq_inr _) -> collect (k (Obj.magic Coq_true)) @ collect (k (Obj.magic Coq_false));;

Random.self_init ();;
print_string "Possible return values:";;
let results = collect (Obj.magic ex_prog');;
List.iter (printf " %d") results;;
print_string "\nRandom execution: ";;
run (Obj.magic ex_prog');;
print_newline ()
