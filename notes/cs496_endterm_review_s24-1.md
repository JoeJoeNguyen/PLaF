# CS 496 - Endterm Review Session
### Spring 2024


## Endterm Structure 

- Evaluate and debug in explicit/implicit-refs
- Evaluate and debug using different paramater-passing methods (CB value, reference, name, need)
- Typing derivation (given typing rules)
- Write expression given a certain type 
- Extension to type checker


## Question 1

```ocaml
let a = 3
in let c = let state = newref(0)
    in proc (d) {
        begin
            setref(state, deref(state) + 1);
            deref(state)
        end
    }
in begin
    (c 0);
    (c 0);
    debug(c)
end
```

### Part 1: Ignoring the debug, what is the result of executing the above code in `explicit-refs`?

#### Answer

```ocaml
Ok (ProcVal ("d",
   BeginEnd
    [SetRef (Var "state", Add (DeRef (Var "state"), Int 1));
     DeRef (Var "state")],
   ExtendEnv ("state", RefVal 0, ExtendEnv ("a", NumVal 3, EmptyEnv))))
```


### Part 2: Describe the environment and the store at the given breakpoint (including the debug).

#### Answer

```ocaml
Env: [
    a := NumVal 3,
    c := ProcVal ("d", ...) (* same as above *)
]

Store: [
    0 -> NumVal 2
]
```





## Question 2

```ocaml
let a = 3
in let f = proc (x) {
    proc (y) {
        begin
            set y = x+x;
            debug(y)
        end
    }
}
in let b=4
in begin
    ((f (a+b)) b);
    b
end
```

### Part 1: Ignoring the debug, what is the result of executing the above code in `implicit-refs` using `call-by-value`?

#### Answer

```ocaml
Ok (NumVal 4)
```

### Part 2: Do the same, but in `call-by-name`.

#### Answer

```ocaml
Ok (NumVal 14)
```


### Part 3: Describe the environment and the store at the given breakpoint (including the debug) using `call-by-name`.

#### Answer

```ocaml
Env: [
    a := RefVal (0)
    x := RefVal (3)
    y := RefVal (2)
]

Store: [
    4 -> NumVal 3,
    2 -> ProcVal (x,Proc(y,BeginEnd(Set(y,Add(Var x,Var x)),Debug(Var y))),(a,RefVal (0))),
    3 -> NumVal 14,
    4 -> Thunk(Add(Var a,Var b),(a,RefVal (0))(f,RefVal (1))(b,RefVal (2)))
]
```


## Question 3

```ocaml
letrec f (x:int):int = 
    if zero?(x) then 0 else x + (f (x - 1))
in f
```

### Prove that the above expression is typeable using a type derivation tree.

#### Answer

![solution to q3, thank you emma!](./q3_derivation.png)


## Question 4

### For each of the types below, give an expression in the `checked` language that matches it.

1. `(bool -> int) -> bool -> int`

2. `(int -> bool -> int) -> int`


#### Answer

1. `proc(x: bool -> int) { x }`

2. `proc(x: int -> bool -> int) { ((x 2) zero?(0)) }`


## Question 5

### Implement the following cases for the `checked` type checker, which is being extended to check the type of stacks. (Note: you must do error checking for unexpected or mismatched types)


```ocaml
...
| EmptyStack(None) -> (* empty stack constructor with no given type *)
    failwith "TODO: implement me!"

| EmptyStack(Some t) -> (* empty stack constructor of type t *)
    return (StackType (t))

| Push(e1, e2) -> (* push e1 to the top of stack e2 *)
    failwith "TODO: implement me!"

| Pop(e) -> (* pop the topmost element from stack e *)
    failwith "TODO: implement me!"

| Peek(e) -> (* get the value of the topmost element without removing it *)
    failwith "TODO: implement me!"

| IsEmpty(e) -> (* check if a stack is empty *)
    failwith "TODO: implement me!"
...
```


#### Answer

```ocaml
...
| EmptyStack(None) ->
    error "emptystack: missing type"
| EmptyStack(Some t) ->
    return (StackType (t))
| Push(e1, e2) ->
    chk_expr e1 >>= fun t1 ->
    chk_expr e2 >>= fun t2 ->
    (match t2 with
    | StackType(t) -> if t = t1 
                        then return t2
                        else error "error" 
    | _ -> error "error")
| Pop(e) ->
    chk_expr e >>= fun te ->
    (match te with
    | StackType(t) -> t
    | _ -> error "error")
| Peek(e) ->
    chk_expr e >>= fun te ->
    (match te with
    | StackType(t) -> return t
    | _ -> error "error")
| IsEmpty(e) ->
    chk_expr e >>= fun te ->
    (match te with 
    | StackType(_) -> return (BoolType)
    | _ -> error "error")
...
```
