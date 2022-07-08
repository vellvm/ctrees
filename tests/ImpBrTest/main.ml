open CTreeDefinitions;;
open ExtrOcamlIntConv;;
open ImpBrEx;;

let rec run t =
  match observe t with
  | RetF r -> print_int (int_of_nat r)
  | VisF (e, k) -> failwith "Vis (unreachable)"
  | BrF (b, n, k) ->
    if int_of_nat n = 0 then failwith "Stuck" else
    let choice = Random.int (int_of_nat n) in
    match Fin.of_nat (nat_of_int (choice)) n with
    | Coq_inleft x -> run (k x)
    | Coq_inright -> failwith "unreachable";;

Random.self_init ();;
run ex_prog';;
print_newline ();;
