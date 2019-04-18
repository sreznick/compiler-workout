open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string
(* conditional jump                *) | CJMP  of string * string
(* begins procedure definition     *) | BEGIN of string * string list * string list
(* end procedure definition        *) | END
(* calls a procedure               *) | CALL  of string * int * bool
(* returns from a function         *) | RET   of bool
    with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)

let rec eval env cfg prg =
        let rec eval_step (call_stack, stack, ((state, input, output) as cfg)) cmd next_cmds =
                let res = match cmd with
                | READ ->
                                next_cmds, (call_stack, (List.hd input) :: stack, (state, List.tl input, output))
                | WRITE ->
                                next_cmds, (call_stack, List.tl stack, (state, input, output @ [List.hd stack]))
                | CONST value ->
                                next_cmds, (call_stack, value :: stack, cfg)
                | LD name ->
                                next_cmds, (call_stack, (State.eval state name) :: stack, cfg)
                | ST name ->
                                let new_state = (State.update name (List.hd stack) state) in
                                next_cmds, (call_stack, List.tl stack, (new_state, input, output))
                | BINOP op ->
                                next_cmds, let rhs :: lhs :: stack' = stack in
                                (call_stack, (Language.Expr.evalBinary op lhs rhs) :: stack', cfg)
                | LABEL name ->
                                next_cmds, (call_stack, stack, cfg)
                | JMP target ->
                                (env#labeled target), (call_stack, stack, cfg)
                | CJMP (cond, target) -> (
                        match stack with
                        | head :: tail ->
                                       if cond = "z" && head = 0 || cond = "nz" && head != 0
                                       then (env#labeled target), (call_stack, tail, cfg)
                                       else next_cmds, (call_stack, tail, cfg)
                        | _ ->
                                        failwith("stack outage for CJMP")
                )
                | BEGIN (_, params, locals) ->
                                let scope = State.enter state (params @ locals) in
                                let folder (state, value::values) name = (State.update name value state, values) in
                                let state', stack' = List.fold_left folder (scope, stack) params in
                                next_cmds, (call_stack, stack', (state', input, output))
                | (RET _ | END) -> ( match call_stack with
                                     | [] -> [], ([], stack, cfg)
                                     | (next', state')::tail -> next', (tail, stack, (State.leave state state', input, output))
                )
                | CALL (target, _, _) -> (env#labeled target), ((next_cmds, state)::call_stack, stack, cfg)
                in res
        in match prg with
           | []              -> cfg
           | current :: next -> let next', state' = eval_step cfg current next in eval env state' next'

class compileContext = object(self)
        val labelId = 0
        method getLabel = ".L" ^ string_of_int labelId, {< labelId  = labelId + 1 >}
end

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], [], (State.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let rec compile_body ctx stmt =
    let rec compile_expr expr = match expr with
        | Expr.Const value          -> [CONST value]
        | Expr.Var   name           -> [LD name]
        | Expr.Binop (op, lhs, rhs) -> compile_expr lhs @ compile_expr rhs @ [BINOP op]
        | Expr.Call (name, params)  -> let computed = List.concat (List.map compile_expr (List.rev params)) in
                                              computed @ [CALL (name, List.length params, true)]
    in
    let rec compile_stmt env stmt =
           let rec compile_if env out_label if_stmt = match if_stmt with
                | Stmt.Seq(fst, snd) -> let env, fst_code = compile_stmt env fst in
                                        let env, snd_code = compile_if env out_label snd in
                                            env, fst_code @ snd_code
                | Stmt.If(cond, tcode, fcode) ->
                                let else_label, env = env#getLabel in
                                let env, then_code = compile_if env out_label tcode in
                                let env, else_code = compile_stmt env fcode in
                                env, compile_expr cond
                                                  @ [CJMP ("z", else_label)]
                                                  @ then_code
                                                  @ [JMP out_label]
                                                  @ [LABEL else_label]
                                                  @ else_code
                | other -> compile_stmt env other
           in

        match stmt with
       | Stmt.Read name                -> env, [READ; ST name]
       | Stmt.Write expr               -> env, compile_expr expr @ [WRITE]
       | Stmt.Assign(name, expr)       -> env, compile_expr expr @ [ST name]
       | Stmt.Seq(fst, snd)            -> let env, fst_code = compile_stmt env fst in
                                          let env, snd_code = compile_stmt env snd in
                                          env, fst_code @ snd_code
       | Stmt.Skip                     -> env, []
       | Stmt.While(condition, body)  -> let bodyLabel, env = env#getLabel in
                                          let condLabel, env = env#getLabel in
                                          let env, bodyCode  = compile_stmt env body in
                                          env, [JMP condLabel; LABEL bodyLabel]
                                             @ bodyCode
                                             @ [LABEL condLabel]
                                             @ compile_expr condition
                                             @ [CJMP ("nz", bodyLabel) ]
       | Stmt.If(condition, tbody, fbody) -> let outLabel, env = env#getLabel in
                                             let env, code = compile_if env outLabel @@ stmt in
                                               env, code @ [LABEL outLabel]
       | Stmt.Repeat(body, condition)     -> let body_label, env = env#getLabel in
                                             let env, body = compile_stmt env body in
                                               env, [LABEL body_label]
                                                    @ body
                                                    @ compile_expr condition
                                                    @ [CJMP ("z", body_label)]
       | Stmt.Call (name, params)        ->
                       env, List.flatten (List.map compile_expr (List.rev params)) @ [CALL (name, List.length params, false)]
       | Stmt.Return opt_result          -> env, (match opt_result with
                                                   | Some result -> (compile_expr result) @ [RET true]
                                                   | _ ->  [RET false]
                                                 )
    in
    let ctx, result = compile_stmt ctx stmt in
    let last_label, ctx = ctx#getLabel in
    ctx, result @ [LABEL last_label]


let compile_defs ctx defs =
    let compile_proc proc_ctx (name, (args, locals, body)) = (
        let result_ctx, code = compile_body proc_ctx body in
            result_ctx, ([LABEL name; BEGIN (name, args, locals)] @ code @ [END])
    )
    in
    let folder (acc_ctx, acc_code) current_def = (
        let result_ctx, current_code = compile_proc acc_ctx current_def in
            result_ctx, current_code @ acc_code
    )
    in
    List.fold_left folder (ctx, []) defs


let compile (defs, entry) =
    let ctx = new compileContext in
    let ctx, body_result = compile_body ctx entry in
    let ctx, defs_result = compile_defs ctx defs in
    let res = body_result @ [END] @ defs_result in
    res
