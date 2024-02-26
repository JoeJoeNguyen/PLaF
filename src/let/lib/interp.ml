(*
Son [Joe] Nguyen
Harris Hamid
I pledge my Honor that I have abided by the Stevens Honor System
*)

open Parser_plaf.Ast
open Parser_plaf.Parser
open Ds
    
(** [eval_expr e] evaluates expression [e] *)
let rec eval_expr : expr -> exp_val ea_result =
  fun e ->
  match e with
  | Int(n) ->
    return (NumVal n)
  | Var(id) ->
    apply_env id
  | Add(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return (NumVal (n1+n2))
  | Sub(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return (NumVal (n1-n2))
  | Mul(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return (NumVal (n1*n2))
  | Div(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    if n2==0
    then error "Division by zero"
    else return (NumVal (n1/n2))
  (*abs value*)
  | Let(id,def,body) ->
    eval_expr def >>= 
    extend_env id >>+
    eval_expr body 
  | ITE(e1,e2,e3) ->
    eval_expr e1 >>=
    bool_of_boolVal >>= fun b ->
    if b 
    then eval_expr e2
    else eval_expr e3
  | IsZero(e) ->
    eval_expr e >>=
    int_of_numVal >>= fun n ->
    return (BoolVal (n = 0))
  | Pair(e1,e2) ->
    eval_expr e1 >>= fun ev1 ->
    eval_expr e2 >>= fun ev2 ->
    return (PairVal(ev1,ev2))
  | Fst(e) ->
    eval_expr e >>=
    pair_of_pairVal >>= fun (l,_) ->
    return l
  | Snd(e) ->
    eval_expr e >>=
    pair_of_pairVal >>= fun (_,r) ->
    return r
(*  | Unpair(id1, id2, e1, e2) ->
    eval_expr e1 >>=
    pair_of_pairVal >>+ fun (l,r) ->
    (*extend the env*)
    extend_env id1 l >>+
    extend_env id2 r >>+
    eval_expr e2
    (*unpair (x,y) = pair(1+1,2) in x+y *)
*)
  | IsEmpty ( e ) ->
    eval_expr e >>= fun ev ->
    (*evaluate the expression e*)
    (match ev with
    | TreeVal Empty -> return (BoolVal true)
    (*
    return True if
    the result of the evaluation is an empty tree
    *)
    | TreeVal _ -> return (BoolVal false)
    (*
    return False if
    the result of the evaluation has a Value "_"
    *)
    | _ -> error "Expression does not evaluate to a binary tree")
    (*
    the case where it is neither an empty tree or has a value
    *)
  | EmptyTree ( _t ) -> return (TreeVal Empty)
  (*
  the _t is a placeholder for the type of tree, which is not used in this case.
  when the patter is matched, return an empty tree (TreeVal Empty)
  always return an empty tree, no matter the type of the tree.
  *)
  | Node ( e1 , e2 , e3 ) ->
    eval_expr e1 >>= fun ev1 ->
    eval_expr e2 >>= fun ev2 ->
    eval_expr e3 >>= fun ev3 ->
    (*
    evaluating the epxression e1, e2, and e3
    *)

    (match (ev2,ev3) with
    | (TreeVal t2, TreeVal t3) -> return (TreeVal (Node(ev1, t2, t3)))
    | _ -> error "Second and third arguments must be trees")
    (*
    match the results of the evaluations ev2 and ev3.
    if both are trees
    return a new tree node with the value ev1 and the two subtrees t2 and t3.
    if one of them is not a tree
    -> return the an error
    *)

  | CaseT ( e1 , e2 , id1 , id2 , id3 , e3 ) ->

    eval_expr e1 >>= fun ev1 ->
    (match ev1 with
    (* evaluating the expression e1*)
    | TreeVal Empty -> eval_expr e2
    (*
    if the evaluation is an empty tree
    -> evaluate the expression e2 (which is the expression for the empty tree case)
    *)
    | TreeVal (Node(ev1', t2, t3)) ->
    (*if the evaluation is a tree node*)
        extend_env id1 ev1' >>+
        (*extend the environment with the node value and 2 subtrees*)
        extend_env id2 (TreeVal t2) >>+
        extend_env id3 (TreeVal t3) >>+
        (*and then evaluate the expression e3*)
        eval_expr e3
    | _ -> error "Expression does not evaluate to a binary tree")

  | Record(fields) ->
    let rec eval_fields = function
    (*recursive helper function that evaluate each fields in the Record*)
      | [] -> return []
      (*if the list of fields is empty, return an empty list*)
      | (id, (_, e))::rest ->
      (*
      id is the field name
      e is the expression for the field value
      rest is the remaining field in the record
      *)
        eval_expr e >>= fun v ->
        (* evaluate the expression e for the field value *)
        eval_fields rest >>= fun fields ->
        (* recursively evaluates the remaining fields int the record *)
        if List.mem_assoc id fields then
        (*
        if the field name "id" is already in teh evaluated fields
        -> raise an error
        List.mem_assoc: takes two arugments: a key and a assoc list, aka list of pairs.
        -> return true if the key is found in the list, else false
         *)
          error ("Record: duplicate fields")
        else
          return ((id, v)::fields)
        (*
        if the "id" is not in the evaluated fields
        -> add the field oto the evaluated fields
        *)
    in
    eval_fields fields >>= fun fields ->
    (* evaluates all fields in the record and
    returns a record value with the evaluated fields *)
    return (RecordVal fields)
  | Proj(e, id) ->
  (*
  e is the record expression
  id is the field name that want to project from the record
  *)
    eval_expr e >>= function
    (*evaluate the expression e*)
      | RecordVal fields ->
        (try return (List.assoc id fields)
         with Not_found -> error ("Proj : field does not exist "))
         (*
         if e is a record value
         -> try to find the field with the name "id" in "fields"
         using List.assoc (which returns the value associated with a key in
         an association list)
         if the field is found it returns the value
         if not found -> exception -> error
         *)
      | _ -> error "Expected a record"
(*  | Debug(_e) ->
    string_of_env >>= fun str ->
    print_endline str; 
    error "Debug called"
  | _ -> failwith "Not implemented yet!"
*)
(** [eval_prog e] evaluates program [e] *)
let eval_prog (AProg(_,e)) =
  eval_expr e


(** [interp s] parses [s] and then evaluates it *)
let interp (e:string) : exp_val result =
  let c = e |> parse |> eval_prog
  in run c
  


