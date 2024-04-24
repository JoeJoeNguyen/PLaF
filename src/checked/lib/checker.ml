(* Harris Hamid and Joe Nguyen *)

open ReM
open Dst
open Parser_plaf.Ast
open Parser_plaf.Parser

let rec chk_expr : expr -> texpr tea_result = function
  | Int _n -> return IntType
  | Var id -> apply_tenv id
  | IsZero(e) ->
    chk_expr e >>= fun t ->
    if t=IntType
    then return BoolType
    else error "isZero: expected argument of type int"
  | Add(e1,e2) | Sub(e1,e2) | Mul(e1,e2)| Div(e1,e2) ->
    chk_expr e1 >>= fun t1 ->
    chk_expr e2 >>= fun t2 ->
    if (t1=IntType && t2=IntType)
    then return IntType
    else error "arith: arguments must be ints"
  | ITE(e1,e2,e3) ->
    chk_expr e1 >>= fun t1 ->
    chk_expr e2 >>= fun t2 ->
    chk_expr e3 >>= fun t3 ->
    if (t1=BoolType && t2=t3)
    then return t2
    else error "ITE: condition not boolean or types of then and else do not match"
  | Let(id,e,body) ->
    chk_expr e >>= fun t ->
    extend_tenv id t >>+
    chk_expr body
  | Proc(var,Some t1,e) ->
    extend_tenv var t1 >>+
    chk_expr e >>= fun t2 ->
    return @@ FuncType(t1,t2)
  | Proc(_var,None,_e) ->
    error "proc: type declaration missing"
  | App(e1,e2) ->
    chk_expr e1 >>=
    pair_of_funcType "app: " >>= fun (t1,t2) ->
    chk_expr e2 >>= fun t3 ->
    if t1=t3
    then return t2
    else error "app: type of argument incorrect"
  | Letrec([(_id,_param,None,_,_body)],_target) | Letrec([(_id,_param,_,None,_body)],_target) ->
    error "letrec: type declaration missing"
  | Letrec([(id,param,Some tParam,Some tRes,body)],target) ->
    extend_tenv id (FuncType(tParam,tRes)) >>+
    (extend_tenv param tParam >>+
     chk_expr body >>= fun t ->
     if t=tRes
     then chk_expr target
     else error
         "LetRec: Type of recursive function does not match
declaration")


(* References *)
 | NewRef(e) ->
    chk_expr e >>= fun e1 ->
    return @@ RefType(e1)

 | DeRef(e) ->
   chk_expr e >>= fun e1 ->
   (match e1 with
     | RefType e2 -> return e2
     | _ -> error "DeRef: expectes arg of RefType")

 | SetRef(e1,e2) ->
   chk_expr e1 >>= fun e1 ->
   chk_expr e2 >>= fun e2 ->
   (match e1 with
     | RefType(e3) ->
       if e2 = e3
       then return UnitType
       else error "setRef: expected the same type"
     | _ -> error "setref: expected a reference type")

 | BeginEnd([]) -> return UnitType

 | BeginEnd(es) ->
   List.fold_right (fun e acc ->
     chk_expr e >>= fun _ -> acc) es (return BoolType)

  (* Lists *)
  | EmptyList(t) ->
    (match t with
    | Some t -> return (ListType t)
    | None -> failwith "Invalid type")

   | Cons(e1,e2) ->
    chk_expr e1 >>= fun first ->
    chk_expr e2 >>= fun second ->
    (match second with
      | ListType t ->
        if first = t
        then return (ListType t)
        else error "cons : type of head and tail do not match"
      | _ -> error "cons : type of head and tail do not match ")

 | IsEmpty(e) ->
    chk_expr e >>= fun e1 ->
    (match e1 with
    | ListType _ -> return BoolType
    | TreeType _ -> return BoolType
    | _ -> error "IsEmpty Error ")

 | Hd(e) ->
   chk_expr e >>= fun e1 ->
    (match e1 with
     | ListType e2 -> (return e2)
     | _ -> error "head error")

  | Tl(e) ->
    chk_expr e >>=  fun e1 ->
    (match e1 with
    | ListType e2 -> return (ListType e2)
    | _ -> failwith " tail error" )


  (* Trees *)
| EmptyTree(t) ->
  (match t with
  | Some t -> return (TreeType t)
  | None -> failwith "Invalid type")

  | Node (de,le,re) ->
    chk_expr de >>= fun e1 ->
    chk_expr le >>= fun e2 ->
    chk_expr re >>= fun e3 ->
      (match (e2, e3) with
      | (TreeType t1, TreeType t2) ->
        if e1 = t1 && e1 = t2
        then return (TreeType e1)
        else error "Node: expected argument of same type")

  | CaseT ( target , emptycase , id1 , id2 , id3 , nodecase ) ->
    (* evaluate target and make sure it has type Tree *)
    chk_expr target >>= fun t1 ->
    (match t1 with
    | TreeType t4 ->
      (* evaluate the empty case and get type2 *)
      chk_expr emptycase >>= fun t2 ->
      (* extend the environment with id1, id2, and id3 with the correct types *)
      extend_tenv id1 t4 >>+
      extend_tenv id2 (TreeType t4) >>+
      extend_tenv id3 (TreeType t4) >>+
      (* evaluate the node case and get type3 *)
      chk_expr nodecase >>= fun t3 ->
      (* check if type2 and type3 are equal *)
      if t2 = t3
      then return t2
      else error "CaseT: expected argument of same type"
    | _ -> error "CaseT: expected argument of type TreeType")


  | Debug(_e) ->
    string_of_tenv >>= fun str ->
    print_endline str;
    error "Debug: reached breakpoint"
  | _ -> failwith "chk_expr: implement"
and
  chk_prog (AProg(_,e)) =
  chk_expr e

(* Type-check an expression *)
let chk (e:string) : texpr result =
  let c = e |> parse |> chk_prog
  in run_teac c

let chkpp (e:string) : string result =
  let c = e |> parse |> chk_prog
  in run_teac (c >>= fun t -> return @@ string_of_texpr t)


