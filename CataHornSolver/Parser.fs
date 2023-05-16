module RedlogParser.RedTrace.Parser

open System
open Antlr4.Runtime
open Antlr4.Runtime.Tree
open Microsoft.FSharp.Core
open ProofBased
open SMTLIB2
open Utils.IntOps

let parseNumber (number: RedTraceParser.NumberContext) = number.NUM().GetText () |> Int64.Parse

let parsePower (power: RedTraceParser.PowerContext) =
  match (power.GetChild 1, power.GetChild 3) with
  | :? RedTraceParser.IdContext as id, (:? RedTraceParser.NumberContext as number) ->
    let app = Apply (UserDefinedOperation (id.GetText (), [], IntSort), [])

    let power app number =
      let rec helper app acc n =
        match n with
        | 0 -> acc
        | n -> helper app (Apply (mulOp, [ app; acc ])) (n - 1)

      helper app app (number - 1)

    power app (number.NUM().GetText () |> Int32.Parse)
  | _ -> __unreachable__ ()
  
let rec simplifyMul =
  function
    | Apply (op, [ y; x ]) 
    | Apply (op, [ x; y ]) when op = mulOp && x = Number 1 -> y
    | Apply (op, [ y; x ]) 
    | Apply (op, [ x; y ]) when op = mulOp && x = (Apply (negOp, [ Number 1 ])) ->
      Apply (negOp, [ y ])
    | otherwise -> otherwise 
    
let parseFactor (factor: RedTraceParser.FactorContext) =
  match factor.GetChild 1, factor.GetChild 3 with
  | :? RedTraceParser.PowerContext as pow, (:? RedTraceParser.NumberContext as number) ->
    let power = pow |> parsePower
    let coeff =
        match number |> parseNumber with
        | n when n < 0 -> Apply(negOp, [Number (n * -1L)])
        | n -> Number n
    
    Apply (mulOp, [ power; coeff ]) |> simplifyMul
  | _ -> __unreachable__ ()

let parseNum (num: RedTraceParser.NumContext) =
  match num.GetChild 1 with
  | :? RedTraceParser.NumberContext as number ->
    match number |> parseNumber with
    | n when n < 0 -> Apply(negOp, [Number (n * -1L)]) 
    | n -> Number n
  | _ -> __unreachable__ ()

  
let parseFactorOrNum (v: IParseTree) =
  match v with
  | :? RedTraceParser.FactorContext as factor -> factor |> parseFactor
  | :? RedTraceParser.NumContext as num -> num |> parseNum
  | _ -> __unreachable__ ()

let rec parseMul (mul: RedTraceParser.MulContext) =
  match mul.GetChild 0 with
  | :? RedTraceParser.FactorContext as factor -> parseFactor factor
  | :? RedTraceParser.PowerContext as power ->
    let power = power |> parsePower
    let factorNumMuls i n =
      let rec helper acc i n =
        match acc with
        | _ when i < n ->
          match mul.GetChild i with
          | :? RedTraceParser.FactorContext
          | :? RedTraceParser.NumContext as v -> helper (parseFactorOrNum v :: acc) (i + 1) n
          | :? RedTraceParser.MulContext as mul -> helper (parseMul mul :: acc) (i + 1) n
          | _ -> helper acc (i + 1) n
        | _ -> acc
      
      helper [] i n |> List.rev
    
    match mul.GetChild 1 with
    | :? RedTraceParser.FactorContext
    | :? RedTraceParser.NumContext as v ->
      let acc = Apply (mulOp, [ power; v |> parseFactorOrNum ]) |> simplifyMul
      
      factorNumMuls 2 mul.ChildCount
      |> List.fold (fun acc v -> Apply (addOp, [ acc; Apply (mulOp, [ power; v ]) |> simplifyMul])) acc

    | _ ->
      let acc =
        match mul.GetChild 2 with
        | :? RedTraceParser.MulContext as mul -> Apply (mulOp, [ power; parseMul mul ]) |> simplifyMul
        | _ -> __unreachable__ ()

      factorNumMuls 3 mul.ChildCount
      |> List.fold (fun acc v -> Apply (addOp, [ acc; Apply (mulOp, [ power; v ]) |> simplifyMul ])) acc
  | _ -> __unreachable__ ()

let parseNcong (ncong: RedTraceParser.NcgongContext) =
  match ncong.GetChild 2 with
  | :? RedTraceParser.FactorContext
  | :? RedTraceParser.NumContext as v -> parseFactorOrNum v
  | _ ->
    match ncong.GetChild 3 with
    | :? RedTraceParser.MulContext as mul -> parseMul mul
    | _ -> __unreachable__ ()

let rec parseBody (body: RedTraceParser.BodyContext) =
  let factorNumMuls i n =
    let rec helper acc i n =
      match acc with
      | _ when i < n ->
        match body.GetChild i with
        | :? RedTraceParser.FactorContext
        | :? RedTraceParser.NumContext as v -> helper (parseFactorOrNum v :: acc) (i + 1) n
        | :? RedTraceParser.MulContext as m -> helper (parseMul m :: acc) (i + 1) n
        | _ -> helper acc (i + 1) n
      | _ -> acc

    helper [] i n |> List.rev

  match body.GetChild 1 with
  | :? RedTraceParser.FactorContext
  | :? RedTraceParser.NumContext as v ->
    let acc = parseFactorOrNum v

    factorNumMuls 2 body.ChildCount
    |> List.fold (fun acc v -> Apply (addOp, [ acc; v ])) acc

  | _ ->
    match body.GetChild 2 with
    | :? RedTraceParser.MulContext as mul ->
      let acc = parseMul mul

      factorNumMuls 4 body.ChildCount
      |> List.fold (fun acc v -> Apply (addOp, [ acc; v ])) acc
    | _ -> __unreachable__ ()

let rec exprs (expr: RedTraceParser.ExprContext) i n =
  let rec helper acc i n =
    match acc with
    | _ when i < n ->
      match expr.GetChild i with
      | :? RedTraceParser.ExprContext as e -> helper (parseExpr e :: acc) (i + 1) n
      | _ -> helper acc (i + 1) n
    | _ -> acc

  helper [] i n |> List.rev

and parseExpr (expr: RedTraceParser.ExprContext) =
  match expr.GetChild 1 with
  | :? RedTraceParser.AndContext -> And <| exprs expr 2 expr.ChildCount
  | :? RedTraceParser.OrContext -> Or <| exprs expr 2 expr.ChildCount
  | :? RedTraceParser.NcgongContext as ncong ->
    let m = parseNcong ncong

    let l =
      match expr.GetChild 2 with
      | :? RedTraceParser.BodyContext as body -> parseBody body
      | _ -> __unreachable__ ()

    let r =
      match expr.GetChild 3 with
      | :? RedTraceParser.NilContext -> Number 0
      | _ -> __unreachable__ ()

    Not (Apply (eqOp, [ Apply (modOp, [ l; m ]); r ]))
  | :? RedTraceParser.EqualContext ->
    let l =
      match expr.GetChild 2 with
      | :? RedTraceParser.BodyContext as body -> parseBody body
      | _ -> __unreachable__ ()

    let r =
      match expr.GetChild 3 with
      | :? RedTraceParser.NilContext -> Number 0
      | _ -> __unreachable__ ()

    Apply (eqOp, [ l; r ])
  | :? RedTraceParser.GrContext ->
    let l =
      match expr.GetChild 2 with
      | :? RedTraceParser.BodyContext as body -> parseBody body
      | _ -> __unreachable__ ()

    let r =
      match expr.GetChild 3 with
      | :? RedTraceParser.NilContext -> Number 0
      | _ -> __unreachable__ ()

    Apply (grOp, [ l; r ])
  | :? RedTraceParser.LsContext ->
    let l =
      match expr.GetChild 2 with
      | :? RedTraceParser.BodyContext as body -> parseBody body
      | _ -> __unreachable__ ()

    let r =
      match expr.GetChild 3 with
      | :? RedTraceParser.NilContext -> Number 0
      | _ -> __unreachable__ ()

    Apply (lsOp, [ l; r ])

  | :? RedTraceParser.NeqContext ->
    let l =
      match expr.GetChild 2 with
      | :? RedTraceParser.BodyContext as body -> parseBody body
      | _ -> __unreachable__ ()

    let r =
      match expr.GetChild 3 with
      | :? RedTraceParser.NilContext -> Number 0
      | _ -> __unreachable__ ()

    Not (Apply (eqOp, [ l; r ]))
  | :? RedTraceParser.LeqContext ->
    let l =
      match expr.GetChild 2 with
      | :? RedTraceParser.BodyContext as body -> parseBody body
      | _ -> __unreachable__ ()

    let r =
      match expr.GetChild 3 with
      | :? RedTraceParser.NilContext -> Number 0
      | _ -> __unreachable__ ()

    Apply (leqOp, [ l; r ])
  | :? RedTraceParser.GeqContext ->
    let l =
      match expr.GetChild 2 with
      | :? RedTraceParser.BodyContext as body -> parseBody body
      | _ -> __unreachable__ ()

    let r =
      match expr.GetChild 3 with
      | :? RedTraceParser.NilContext -> Number 0
      | _ -> __unreachable__ ()

    Apply (geqOp, [ l; r ])

  | :? RedTraceParser.BallContext ->
    let head =
      match expr.GetChild 3 with
      | :? RedTraceParser.ExprContext as e -> parseExpr e
      | _ -> __unreachable__ ()

    let body =
      match expr.GetChild 4 with
      | :? RedTraceParser.ExprContext as e -> parseExpr e
      | _ -> __unreachable__ ()

    let id = 
      match expr.GetChild 2 with
        | :? RedTraceParser.IdContext as id -> id.GetText()
        | _ -> __unreachable__ ()
  
    QuantifierApplication ([ForallQuantifier [(id, IntSort)]], Hence(body, head))
  | _ -> __unreachable__ ()

let rec substituteVar oldName newName =
  function
    | Number _
    | BoolConst _
    | Let _
    | Match _
    | Ite _ as expr -> expr 
    | Ident (ident, sort) when ident = oldName -> Ident (newName, sort)
    | Ident (ident, sort) -> Ident (ident, sort)
    | Apply (UserDefinedOperation (ident, sorts, sort ), expr) 
    | Apply (ElementaryOperation (ident, sorts, sort ), expr) when ident = oldName ->
      Apply (UserDefinedOperation (newName, sorts, sort ), expr)
    | Apply (ElementaryOperation (ident, sorts, sort), exprs) 
    | Apply (UserDefinedOperation (ident, sorts, sort), exprs) ->
      Apply (UserDefinedOperation (ident, sorts, sort), List.map (substituteVar oldName newName) exprs)
    | And exprs -> And (List.map (substituteVar oldName newName) exprs)
    | Or exprs -> Or (List.map (substituteVar oldName newName) exprs)
    | Not expr -> substituteVar oldName newName expr
    | Hence (expr1, expr2) -> Hence (substituteVar oldName newName expr1, substituteVar oldName newName expr2)
    | QuantifierApplication (quantifier, expr) -> QuantifierApplication (quantifier, substituteVar oldName newName expr)
    
let rec uniqVarsInQuantifier usedNames =
  function
    | QuantifierApplication ([ForallQuantifier [(n, sort)]], body) when (usedNames |> List.contains n) ->
      let newName = "!" + n
      let body', usedNames' = uniqVarsInQuantifier (newName::usedNames) (substituteVar n newName body)
      QuantifierApplication ([ForallQuantifier [(newName, sort)]], body'), newName::usedNames'
    | QuantifierApplication ([ForallQuantifier [(n, sort)]], body) ->
      let body', usedNames' = uniqVarsInQuantifier usedNames body
      QuantifierApplication ([ForallQuantifier [(n, sort)]], body'), n::usedNames'
    | Hence (expr1, expr2) ->
      let expr2', usedNames' = uniqVarsInQuantifier usedNames expr2
      Hence (expr1, expr2'), usedNames' 
    | Or exprs ->
      let exprs', usedNames' =
        List.fold
          (fun (acc, usedNames) expr ->
            let expr', usedNames' = uniqVarsInQuantifier usedNames expr
            (expr'::acc, usedNames'))
          ([], usedNames) exprs
      Or (exprs' |> List.rev), usedNames'
    | And exprs ->
      let exprs', usedNames' =
        List.fold
          (fun (acc, usedNames) expr ->
            let expr', usedNames' = uniqVarsInQuantifier usedNames expr
            (expr'::acc, usedNames'))
          ([], usedNames) exprs
      And (exprs' |> List.rev), usedNames'
    | expr -> expr, usedNames 
      
let rec clauseHead =
  function
    | And exprs -> And (List.map clauseHead exprs)
    | Or exprs -> Or (List.map clauseHead exprs)
    | Not expr -> Not (clauseHead expr)
    | QuantifierApplication ([ForallQuantifier _], Hence(_, head)) -> clauseHead head
    | expr -> expr

let translateToSmt line =
  let lexer = RedTraceLexer (CharStreams.fromString line)
  let tokens = CommonTokenStream lexer
  let parser = RedTraceParser tokens
  let tree: RedTraceParser.ProgContext = parser.prog ()

  match tree.GetChild 1 with
  | :? RedTraceParser.ExprContext as expr ->
      parseExpr expr 
  | _ -> __unreachable__ ()