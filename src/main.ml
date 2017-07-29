open Bap.Std
open Bap_plugins.Std
open Core_kernel.Std
open Yojson.Basic.Util

exception Bad_user_input
exception Bad_insn of mem * int * int
exception Create_mem of Error.t
exception Trailing_data of int
exception Unknown_arch

exception Unexpected_BinOp
exception Unexpected_RelOp
exception Unexpected_Expr
exception Unexpected_Stmt

exception Unhandled_CpuExn
exception Unhandled_Special of string

module Dis = Disasm_expert.Basic

let to_binary ?(map=ident) s =
  let seps = [' '; ','; ';'] in
  let separated = List.exists seps ~f:(String.mem s) in
  let bytes = if separated
    then String.split_on_chars ~on:seps s
    else List.init (String.length s / 2) ~f:(fun n ->
        String.slice s (n * 2) (n * 2 + 2)) in
  try bytes |> List.map ~f:map |> String.concat |> Scanf.unescaped
  with Scanf.Scan_failure _ -> raise Bad_user_input

let read_input input =
  let prepend_slash_x x = "\\x" ^ x in
  match String.prefix input 2 with
    | "" | "\n" -> exit 0
    | x -> to_binary ~map:prepend_slash_x input

let create_memory arch s addr =
  let endian = Arch.endian arch in
  Memory.create endian addr @@
  Bigstring.of_string s |> function
    | Ok r -> r
    | Error e -> raise (Create_mem e)

let bad_insn addr state mem start =
  let stop = Addr.(Dis.addr state - addr |> to_int |> ok_exn) in
  raise (Bad_insn (Dis.memory state, start, stop))

let bil_of_insn lift mem insn =
  match lift mem insn with
  | Ok bil -> bil
  | Error e -> [Bil.special @@ sprintf "Lifter: %s" @@ Error.to_string_hum e]

let get_bil lift mem insn =
  bil_of_insn lift mem insn

(* My Section *)
let rec lookup_env v env =
  match env with
  | [] -> None
  | (w, e) :: env_ ->
      if v = w then Some e else lookup_env v env_

let rec remove_let_expr expr env =
  match expr with
  | Bil.Load (e, e1, endian, s) ->
      let new_e1 = remove_let_expr e1 env in
      Bil.Load (e, new_e1, endian, s)
  | Bil.Store (e, e1, e2, endian, s) ->
      let new_e1 = remove_let_expr e1 env in
      let new_e2 = remove_let_expr e2 env in
      Bil.Store (e, new_e1, new_e2, endian, s)
  | Bil.BinOp (o, e1, e2) ->
      let new_e1 = remove_let_expr e1 env in
      let new_e2 = remove_let_expr e2 env in
      Bil.BinOp (o, new_e1, new_e2)
  | Bil.UnOp (o, e) ->
      let new_e = remove_let_expr e env in
      Bil.UnOp (o, new_e)
  | Bil.Var (v) ->
      let x =
        match lookup_env v env with
        | None -> expr
        | Some (e) -> e
      in
      x
  | Bil.Int (_) -> expr
  | Bil.Cast (c, n, e) ->
      let new_e = remove_let_expr e env in
      Bil.Cast (c, n, new_e)
  | Bil.Let (v, e1, e2) ->
      remove_let_expr e2 ((v, (remove_let_expr e1 env)) :: env)
  | Bil.Unknown (_, _) -> expr
  | Bil.Ite (e1, e2, e3) ->
      let new_e1 = remove_let_expr e1 env in
      let new_e2 = remove_let_expr e2 env in
      let new_e3 = remove_let_expr e3 env in
      Bil.Ite (new_e1, new_e2, new_e3)
  | Bil.Extract (n1, n2, e) ->
      let new_e = remove_let_expr e env in
      Bil.Extract (n1, n2, new_e)
  | Bil.Concat (e1, e2) ->
      let new_e1 = remove_let_expr e1 env in
      let new_e2 = remove_let_expr e2 env in
      Bil.Concat (new_e1, new_e2)

let rec remove_let_stmt stmt =
  match stmt with
  | Bil.Types.Move (v, e) ->
      let new_e = remove_let_expr e [] in
      Bil.Types.Move (v, new_e)
  | Bil.Types.Jmp (e) ->
      let new_e = remove_let_expr e [] in
      Bil.Types.Jmp (new_e)
  | Bil.Types.Special (_) -> stmt
  | Bil.Types.While (e, sl) ->
      let new_e = remove_let_expr e [] in
      let new_sl = List.map ~f:remove_let_stmt sl in
      Bil.Types.While (new_e, new_sl)
  | Bil.Types.If (e, sl1, sl2) ->
      let new_e = remove_let_expr e [] in
      let new_sl1 = List.map ~f:remove_let_stmt sl1 in
      let new_sl2 = List.map ~f:remove_let_stmt sl2 in
      Bil.Types.If (new_e, new_sl1, new_sl2)
  | Bil.Types.CpuExn (_) -> stmt

let remove_let_bil bil =
  List.map ~f:remove_let_stmt bil

let endian_to_json endian =
  let endian_s =
    match endian with
    | LittleEndian -> "LittleEndian"
    | BigEndian -> "BigEndian"
  in
  `Assoc [("Type", `String "Endian") ; ("SubType", `String endian_s) ;
      ("Args", `List [])]

let size_to_json size =
  `Int (size |> Size.in_bits)

let unop_to_json op =
  let op_s =
    match op with
    | Bil.Types.NEG -> "NEG"
    | Bil.Types.NOT -> "NOT"
  in
  `Assoc [("Type", `String "UnOpKind") ; ("SubType", `String op_s) ;
      ("Args", `List [])]

let binop_to_json op =
  let op_s =
    match op with
    | Bil.Types.PLUS -> "ADD"
    | Bil.Types.MINUS -> "SUB"
    | Bil.Types.TIMES -> "MUL"
    | Bil.Types.DIVIDE -> "DIV"
    | Bil.Types.SDIVIDE -> "SDIV"
    | Bil.Types.MOD -> "MOD"
    | Bil.Types.SMOD -> "SMOD"
    | Bil.Types.LSHIFT -> "SHL"
    | Bil.Types.RSHIFT -> "SHR"
    | Bil.Types.ARSHIFT -> "SAR"
    | Bil.Types.AND -> "AND"
    | Bil.Types.OR -> "OR"
    | Bil.Types.XOR -> "XOR"
    | _ -> raise Unexpected_BinOp
  in
  `Assoc [("Type", `String "BinOpKind") ; ("SubType", `String op_s) ;
      ("Args", `List [])]

let relop_to_json op =
  let op_s =
    match op with
    | Bil.Types.EQ -> "EQ"
    | Bil.Types.NEQ -> "NEQ"
    | Bil.Types.LT -> "LT"
    | Bil.Types.LE -> "LE"
    | Bil.Types.SLT -> "SLT"
    | Bil.Types.SLE -> "SLE"
    | _ -> raise Unexpected_RelOp
  in
  `Assoc [("Type", `String "RelOpKind") ; ("SubType", `String op_s) ;
    ("Args", `List [])]

let var_to_json var =
  let n =
    match Var.typ var with
    | Type.Imm (n) -> n
    | Type.Mem (n, _) -> Size.in_bits n
  in
  `Assoc [("Type", `String "Reg") ; ("SubType", `String "Variable") ;
      ("Args", `List [`String (String.lowercase (Var.name var)) ; `Int n])]

let word_to_json word =
  let value = Word.string_of_value ~hex:false word in
  let size = Word.bitwidth word in
  `Assoc [("Type", `String "Imm") ; ("SubType", `String "Integer") ;
      ("Args", `List [`String value ; `Int size])]

let castkind_to_json op =
  let op_s =
    match op with
    | Bil.Types.UNSIGNED -> "ZeroExt"
    | Bil.Types.SIGNED -> "SignExt"
    | Bil.Types.HIGH -> "High"
    | Bil.Types.LOW -> "Low"
  in
  `Assoc [("Type", `String "CastFrom") ; ("SubType", `String op_s) ;
      ("Args", `List [])]

let is_binop op =
  match op with
  | Bil.Types.PLUS
  | Bil.Types.MINUS
  | Bil.Types.TIMES
  | Bil.Types.DIVIDE
  | Bil.Types.SDIVIDE
  | Bil.Types.MOD
  | Bil.Types.SMOD
  | Bil.Types.LSHIFT
  | Bil.Types.RSHIFT
  | Bil.Types.ARSHIFT
  | Bil.Types.AND
  | Bil.Types.OR
  | Bil.Types.XOR -> true
  | Bil.Types.EQ
  | Bil.Types.NEQ
  | Bil.Types.LT
  | Bil.Types.LE
  | Bil.Types.SLT
  | Bil.Types.SLE -> false

let rec build_json_expr expr =
  match expr with
  | Bil.Load (_, e1, endian, s) ->
      `Assoc [("Type", `String "Expr") ; ("SubType", `String "Load") ;
          ("Args", `List [build_json_expr e1 ; endian_to_json endian ;
                            size_to_json s])]
  | Bil.Store (_, e1, e2, endian, _) ->
      `Assoc [("Type", `String "Stmt") ; ("SubType", `String "Store") ;
          ("Args", `List [build_json_expr e1 ; endian_to_json endian ;
                            build_json_expr e2])]
  | Bil.BinOp (o, e1, e2) ->
      if is_binop o
      then
        `Assoc [("Type", `String "Expr") ; ("SubType", `String "BinOp") ;
            ("Args", `List [binop_to_json o ; build_json_expr e1 ;
                              build_json_expr e2])]
      else
        `Assoc [("Type", `String "Expr") ; ("SubType", `String "RelOp") ;
            ("Args", `List [relop_to_json o ; build_json_expr e1 ;
                              build_json_expr e2])]
  | Bil.UnOp (o, e) ->
      `Assoc [("Type", `String "Expr") ; ("SubType", `String "UnOp") ;
          ("Args", `List [unop_to_json o ; build_json_expr e])]
  | Bil.Var (v) ->
      `Assoc [("Type", `String "Expr") ; ("SubType", `String "Var") ;
          ("Args", `List [var_to_json v])]
  | Bil.Int (w) ->
      `Assoc [("Type", `String "Expr") ; ("SubType", `String "Num") ;
          ("Args", `List [word_to_json w])]
  | Bil.Cast (c, n, e) ->
      `Assoc [("Type", `String "Expr") ; ("SubType", `String "Cast") ;
          ("Args", `List [castkind_to_json c ; `Int n ; build_json_expr e])]
  | Bil.Let (v, e1, e2) -> raise Unexpected_Expr
  | Bil.Unknown (_, _) ->
      `Assoc [("Type", `String "Expr") ; ("SubType", `String "NotExpr") ;
          ("Args", `List [])]
  | Bil.Ite (e1, e2, e3) ->
      `Assoc [("Type", `String "Expr") ; ("SubType", `String "Ite") ;
          ("Args", `List [build_json_expr e1 ; build_json_expr e2 ;
                            build_json_expr e3])]
  | Bil.Extract (n1, n2, e) ->
      let c1 =
        `Assoc [("Type", `String "Expr") ; ("SubType", `String "Cast") ;
            ("Args", `List [`Assoc [("Type", `String "CastFrom") ;
                                ("SubType", `String "Low") ;
                                ("Args", `List [])] ;
                            `Int (n1 + 1) ; build_json_expr e])] in
      `Assoc [("Type", `String "Expr") ; ("SubType", `String "Cast") ;
          ("Args", `List [`Assoc [("Type", `String "CastFrom") ;
                              ("SubType", `String "High") ;
                              ("Args", `List [])] ;
                          `Int (n1 - n2 + 1) ; c1])]
  | Bil.Concat (e1, e2) ->
      `Assoc [("Type", `String "Expr") ; ("SubType", `String "BinOp") ;
          ("Args", `List [`Assoc [("Type", `String "BinOpKind") ;
                              ("SubType", `String "CONCAT") ;
                              ("Args", `List [])] ;
                          build_json_expr e1 ; build_json_expr e2])]

let rec build_json_stmt (num, idx, res) stmt =
  match stmt with
  | Bil.Types.Move (v, e) ->
      let s =
        match e with
        | Bil.Store (_, _, _, _, _) -> build_json_expr e
        | _ ->
            `Assoc [("Type", `String "Stmt") ; ("SubType", `String "Move") ;
                ("Args", `List [var_to_json v ; build_json_expr e])]
      in
      (num, idx, (s :: res))
  | Bil.Types.Jmp (e) ->
      let s =
        `Assoc [("Type", `String "Stmt") ; ("SubType", `String "End") ;
            ("Args", `List [build_json_expr e])]
      in
      (num, idx, (s :: res))
  | Bil.Types.Special (s) -> raise (Unhandled_Special s)
  | Bil.Types.While (e, sl) ->
      let e_j = build_json_expr e in
      let s1 = sprintf "Label%d" idx in
      let s2 = sprintf "Label%d" (idx + 1) in
      let lab1 =
        `Assoc [("Type", `String "Stmt") ; ("SubType", `String "label") ;
            ("Args", `List [`String s1])]
      in
      let lab2 =
        `Assoc [("Type", `String "Stmt") ; ("SubType", `String "label") ;
            ("Args", `List [`String s2])]
      in
      let s =
        `Assoc [("Type", `String "Stmt") ; ("SubType", `String "CJump") ;
            ("Args", `List [e_j ; `String s1 ; `String s2])]
      in
      let _, new_idx, sl_j =
        List.fold_left ~f:build_json_stmt ~init:(num, idx + 2, []) sl in
      let new_sl_j =
        match sl_j with
        | [] ->
            [`Assoc [("Type", `String "Stmt") ; ("SubType", `String "End") ;
                ("Args", `List [num])]]
        | (`Assoc [("Type", `String "Stmt") ; ("SubType", `String "End") ; _]) :: _ ->
            sl_j
        | _ :: _ ->
            `Assoc [("Type", `String "Stmt") ; ("SubType", `String "End") ;
                ("Args", `List [num])] :: sl_j
      in
      (num, new_idx, List.concat [(lab2 :: new_sl_j) ; (lab1 :: s :: res)])
  | Bil.Types.If (e, sl1, sl2) ->
      let e_j = build_json_expr e in
      let s1 = sprintf "Label%d" idx in
      let s2 = sprintf "Label%d" (idx + 1) in
      let lab1 =
        `Assoc [("Type", `String "Stmt") ; ("SubType", `String "Label") ;
            ("Args", `List [`String s1])]
      in
      let lab2 =
        `Assoc [("Type", `String "Stmt") ; ("SubType", `String "Label") ;
            ("Args", `List [`String s2])]
      in
      let s =
        `Assoc [("Type", `String "Stmt") ; ("SubType", `String "CJump") ;
            ("Args", `List [e_j ; `String s1 ; `String s2])]
      in
      let _, idx1, sl_j1 =
        List.fold_left ~f:build_json_stmt ~init:(num, idx + 2, []) sl1 in
      let new_sl_j1 =
        match sl_j1 with
        | [] ->
            [`Assoc [("Type", `String "Stmt") ; ("SubType", `String "End") ;
                ("Args", `List [num])]]
        | (`Assoc [("Type", `String "Stmt") ; ("SubType", `String "End") ; _]) :: _ ->
            sl_j1
        | _ :: _ ->
            `Assoc [("Type", `String "Stmt") ; ("SubType", `String "End") ;
                ("Args", `List [num])] :: sl_j1
      in
      let _, idx2, sl_j2 =
        List.fold_left ~f:build_json_stmt ~init:(num, idx1, []) sl2 in
      let new_sl_j2 =
        match sl_j2 with
        | [] ->
            [`Assoc [("Type", `String "Stmt") ; ("SubType", `String "End") ;
                ("Args", `List [num])]]
        | (`Assoc [("Type", `String "Stmt") ; ("SubType", `String "End") ; _]) :: _ ->
            sl_j2
        | _ :: _ ->
            `Assoc [("Type", `String "Stmt") ; ("SubType", `String "End") ;
                ("Args", `List [num])] :: sl_j2
      in
      (num, idx2, (List.concat [new_sl_j2 ; (lab2 :: new_sl_j1) ; (lab1 :: s :: res)]))
  | Bil.Types.CpuExn (_) -> raise Unhandled_CpuExn

let build_json_bil len bil =
  let imm =
    if Sys.argv.(1) = "32"
    then
      `Assoc [("Type", `String "Imm") ; ("SubType", `String "Integer") ;
                ("Args", `List [`Int (0x8048000 + len) ; `Int 32])]
    else
      `Assoc [("Type", `String "Imm") ; ("SubType", `String "Integer") ;
                ("Args", `List [`Int (0x401000 + len) ; `Int 64])]
  in
  let num = `Assoc [("Type", `String "Expr") ; ("SubType", `String "Num") ;
                ("Args", `List [imm])] in
  let _, _, l_rev = List.fold_left ~f:build_json_stmt ~init:(num, 0, []) bil in
  let new_l_rev =
    match l_rev with
    | [] ->
        [`Assoc [("Type", `String "Stmt") ; ("SubType", `String "End") ;
            ("Args", `List [num])]]
    | (`Assoc [("Type", `String "Stmt") ; ("SubType", `String "End") ; _]) :: _ ->
        l_rev
    | _ :: _ ->
        `Assoc [("Type", `String "Stmt") ; ("SubType", `String "End") ;
            ("Args", `List [num])] :: l_rev
  in
  `Assoc [("Type", `String "AST") ; ("SubType", `String "Stmts") ;
      ("Args", `List (List.rev new_l_rev))]

let bap_to_json arch mem insn =
  let module Target = (val target_of_arch arch) in
  let bil = get_bil Target.lift mem insn in
  let bil_wo_let = remove_let_bil bil in
  let bil_json = build_json_bil (Memory.length mem) bil_wo_let in
  printf "%s\n" (Yojson.Basic.pretty_to_string bil_json)

(* Argument Setting *)
let arch = if Sys.argv.(1) = "32"
  then
    match Arch.of_string "x86" with
    | None -> raise Unknown_arch
    | Some arch -> arch
  else
    match Arch.of_string "x86_64" with
    | None -> raise Unknown_arch
    | Some arch -> arch

let size = if Sys.argv.(1) = "32" then ":32" else ":64"
let addr = Addr.of_string
              (if Sys.argv.(1) = "32" then "0x08048000" ^ size
                                      else "0x401000" ^ size)
let input = read_input Sys.argv.(2)
let mem = create_memory arch input addr
let backend = "llvm"
let _ =
  Plugins.load ();
  Dis.with_disasm ~backend (Arch.to_string arch) ~f:(fun dis ->
    let bytes = Dis.run dis mem ~return:ident ~init:0
        ~stop_on:[`Valid] ~invalid:(bad_insn addr)
        ~hit:(fun state mem insn bytes ->
          bap_to_json arch mem insn;
          Dis.stop state bytes) in
    match String.length input - bytes with
    | 0 -> Or_error.return ()
  (*  | n -> raise (Trailing_data n) *)
    | _ -> Or_error.return ())