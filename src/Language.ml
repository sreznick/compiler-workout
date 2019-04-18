(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators
                         
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    (* Empty state *)
    let empty =
      let e x = failwith (Printf.sprintf "Undefined variable: %s" x) in
      {g = e; l = e; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let u x v s = fun y -> if x = y then v else s y in
      if List.mem x s.scope then {s with l = u x v s.l} else {s with g = u x v s.g}

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if List.mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let enter st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let leave st st' = {st' with g = st.g}

  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t
    (* function call    *) | Call  of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * int option
                                                            
    (* Expression evaluator
          val eval : env -> config -> t -> config
       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method
           method definition : env -> string -> int list -> config -> config
       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns resulting configuration
    *)                                                       

    let condition value = if value then 1 else 0

    let boolean value = value != 0

    let evalBinary operation left right = match operation with
        | "+"       -> left + right
        | "-"       -> left - right
        | "*"       -> left * right
        | "/"       -> left / right
        | "%"       -> left mod right
        | "=="      -> condition (left == right)
        | "!="      -> condition (left != right)
        | "<"       -> condition (left < right)
        | "<="      -> condition (left <= right)
        | ">"       -> condition (left > right)
        | ">="      -> condition (left >= right)
        | "!!"      -> condition (left != 0 || right != 0)
        | "&&"      -> condition (left != 0 && right != 0)

    (* Expression evaluator
          val eval : state -> t -> int

       Takes a state and an expression, and returns the value of the expression in
       the given state.
    *)
    let rec eval env ((state, input, output, _) as config) expression = match expression with
        | Const value -> (state, input, output, Some value)
        | Var name    -> (state, input, output, Some (State.eval state name))
        | Binop(operation, left, right) ->
                        let ((_, _, _, Some valueL) as configL) = eval env config left in
                        let (stateR, inputR, outputR, Some valueR) = eval env configL right in
                            (stateR, inputR, outputR, Some (evalBinary operation valueL valueR))
        | Call (f, args) ->
                        let folder (state, input, output, values) arg =
                                let (state', input', output', Some value') = eval env (state, input, output, None) arg in 
                                    (state', input', output', value' :: values) in
                        let stateC, inputC, outputC, valuesC = List.fold_left folder (state, input, output, []) args in
                        env#definition env f (List.rev valuesC) (stateC, inputC, outputC, None)
         
    (* Expression parser. You can use the following terminals:
         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string                                                                                                                  
    *)
    let ostapBinary op = ostap(- $(op)), (fun lhs rhs -> Binop(op, lhs, rhs))
    ostap (                                      
        expr:
             !(Ostap.Util.expr
                 (fun x -> x)
                 (Array.map (fun (assoc, ops) -> assoc, List.map ostapBinary ops)
                     [|
                             `Lefta, ["!!"];
                             `Lefta, ["&&"];
                             `Nona,  ["<="; "<"; ">="; ">"; "=="; "!="];
                             `Lefta, ["+"; "-"];
                             `Lefta, ["*"; "/"; "%"];
                     |]
                 ) term
             );
       term:
               value: DECIMAL {Const value} |
               name: IDENT "(" params:!(Util.list0 expr) ")" {Call (name, params)} |
               name: IDENT {Var name} |
               -"(" expr -")"
    )
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* Statement evaluator
         val eval : env -> config -> t -> config
       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
    (*
    let rec eval env ((st, i, o, r) as conf) k stmt = failwith "Not implemnted"
     *)

    let after k stmt = match k with
    | Skip -> stmt
    | _ -> Seq (stmt, k)

    let rec eval env ((state, input, output, result) as config) k statement = match statement with
    | Read  name                  ->
                    eval env (State.update name (List.hd input) state, List.tl input, output, None) Skip k
    | Write expr                  ->
                    let (stateW, inputW, outputW, Some valueW) = Expr.eval env config expr in
                    eval env (stateW, inputW, outputW @ [valueW], None) Skip k
    | Assign (name, expr)         ->
                    let (stateA, inputA, outputA, Some valueA) = Expr.eval env config expr in
                    eval env (State.update name valueA stateA, inputA, outputA, Some valueA) Skip k
    | Seq(first, second)          -> eval env config (after k second) first
    | Skip                        -> (
            match k with
            | Skip -> config
            | _    -> eval env config Skip k
    )
    | While(condition, body)      ->
                    let (stateW, inputW, outputW, Some valueW) = Expr.eval env config condition in
                    if Expr.boolean valueW
                    then eval env (stateW, inputW, outputW, None) (after k statement) body
                    else eval env (stateW, inputW, outputW, None) Skip k
    | If(condition, tbody, fbody) ->
                    let (stateC, inputC, outputC, Some valueC) = Expr.eval env config condition in
                           eval env (stateC, inputC, outputC, None) k (if Expr.boolean valueC then tbody else fbody)
    | Repeat(body, condition)     ->
                    eval env config (after k (While (Expr.Binop("==", condition, Expr.Const 0), body))) body
    | Call(name, actual)          ->
                    eval env (Expr.eval env config (Expr.Call (name, actual))) Skip k
    | Return result               -> (
            match result with
            | Some expression -> Expr.eval env config expression
            | _               -> (state, input, output, None)
    )

    let flatten opt = match opt with
        | Some v -> v
        | None   -> []

    (* Statement parser *)
    let ostapBinary op = ostap(- $(op)), (fun lhs rhs -> Expr.Binop(op, lhs, rhs))
    ostap (
            line: "read"   "(" x: IDENT ")"  {Read x}
                | "write"  "(" e:!(Expr.expr) ")" {Write e}
                | x: IDENT ":=" e:!(Expr.expr)    {Assign (x, e)}
                | name:IDENT "(" params:lst? ")"  {Call (name, flatten params)} 
                | "skip"   {Skip}
                | "while"  cond:!(Expr.expr) "do" body:parse "od" { While (cond, body) }
                | "if"     iff:ifParse {iff}
                | "repeat" body:parse "until" cond:!(Expr.expr) {Repeat (body, cond)}
                | "return" expr:!(Expr.expr)? {Return expr}
                | "for"    init:parse "," condition:!(Expr.expr) "," step:parse "do" body:parse "od" {
                           Seq (init, While(condition, Seq(body, step)))
                        }
                ;

            ifParse: cond:!(Expr.expr) "then" stmt1:parse stmt2:elseParse {If (cond, stmt1, stmt2)};

            lst: head:!(Expr.expr) "," tail:lst {head::tail}
               | single:!(Expr.expr)            {[single]}
               ;

            elseParse: "fi"   { Skip }
                     | "else" stmt:parse "fi" { stmt }
                     | "elif" iff:ifParse { iff };

            parse: l: line ";" rest:parse {Seq(l, rest)} | line
    )
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
          arg: IDENT;
          parse: "fun" name:IDENT "(" args:!(Util.list0 arg) ")" local: (%"local" local:!(Util.list0 arg))? "{" body:!(Stmt.parse) "}" {
                  name, (args, (Stmt.flatten local), body)
          }
        )

  end
    
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t    

(* Top-level evaluator
     eval : t -> int list -> int list
   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i =
  let module M = Map.Make (String) in
  let m          = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f args (st, i, o, r) =                                                                      
           let xs, locs, s      =  snd @@ M.find f m in
           let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
           let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
           (State.leave st'' st, i', o', r')
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
