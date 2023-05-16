module Approximation

open Microsoft.FSharp.Collections
open Microsoft.Z3
open SMTLIB2.Parser
open SMTLIB2.Prelude
open Operation
open SMTLIB2


module Linearization =
  let linearization file =
    let p = Parser(false)
    let commands = p.ParseFile file

    let plus =
      makeElementaryOperationFromSorts "+" [ IntSort; IntSort ] IntSort

    let mul =
      makeElementaryOperationFromSorts "*" [ IntSort; IntSort ] IntSort

    let constants pdng (xs: _ list) =
      let _, cnsts =
        List.fold
          (fun (i, acc) _ ->
            (i - 1,
             $"c_{(i + pdng + 1)}"
             :: acc))
          (xs.Length - 1, [])
          xs

      cnsts

    let terms pdng args =
      List.map2
        (fun c (x, _) ->
          Apply (
            mul,
            [ Apply (UserDefinedOperation ($"{c}" , [], IntSort), [])
              Ident (x, IntSort) ]
          ))
        (constants pdng args)
        args

    let sum pdng =
      function
      | [] -> Apply (UserDefinedOperation ($"c_{pdng}", [], IntSort), [])
      | t :: ts ->
        Apply (
          plus,
          [ Apply (UserDefinedOperation ($"c_{pdng}", [], IntSort), [])
            List.fold (fun acc x ->
                       Apply (plus, [ x; acc ])) t ts ]
        )

    let pdng_defs =
      fun cs pdng ->
        cs
        |> List.fold
             (fun (pd, acc) (name, _, (args: operation list)) ->
               (args.Length + pd + 1,
                Definition (
                  DefineFun (
                    name.ToString (),
                    List.map (fun arg -> (arg.ToString (), IntSort)) args,
                    IntSort,
                    sum pd
                    <| List.rev (terms pd (List.map (fun x -> (opName x, ())) args))
                  )
                )
                :: acc))
             (pdng, [])
    
    let padding, dataTypes =
      let pdng, defs =
        List.fold
          (fun (pdng, acc) x ->
            match x with
            | Command (DeclareDatatype (_, cs)) ->
              let pdng', def = pdng_defs cs pdng
              (pdng', def @ acc)
            | Command (DeclareDatatypes [ _, cs ]) ->
              let pdng', def = pdng_defs cs pdng
              (pdng', def @ acc)
            | Command (DeclareDatatypes _) -> failwith "???"
            | _ -> (pdng, acc))
          (0, [])
          commands

      (pdng, defs |> List.rev)

    let padding, functions =
      let padding, functions =
        List.fold
          (fun (pdng, acc as r) cmd ->
            match cmd with
            | Command (DeclareFun (name, sorts, _)) ->
              let _, args =
                sorts
                |> List.fold
                     (fun (i, acc) _ -> (i - 1, ($"x_{i}", IntSort) :: acc))
                     (sorts.Length - 1, [])

              (pdng + args.Length + 1,
               Definition (DefineFun (name.ToString (), args, IntSort, sum pdng <| List.rev (terms pdng args)))
               :: acc)
            | _ -> r)
          (padding, [])
          commands

      (padding, functions |> List.rev)

    let asserts =
      let quantiInt =
        List.map (fun (name, _) -> name, IntSort) in

      let geq_op typ =
        Operation.makeElementaryRelationFromSorts ">=" [ typ; typ ]

      let eq_op typ =
        Operation.makeElementaryRelationFromSorts "=" [ typ; typ ]

      let rec helper smt =
        match smt with
        | Apply (UserDefinedOperation _, _) as app -> Apply (eq_op IntSort, [ app; Number 0 ])
        | And smtExprs -> And (smtExprs |> List.map (fun x -> helper x))
        | Or smtExprs -> Or (smtExprs |> List.map (fun x -> helper x))
        | Not smtExpr -> Not (helper smtExpr)
        | Hence (smtExpr1, smtExpr2) -> Hence (helper smtExpr1, helper smtExpr2)
        | QuantifierApplication (quantifier, smtExpr) ->
          QuantifierApplication (
            quantifier
            |> List.map (function
              | ForallQuantifier vars -> ForallQuantifier (quantiInt vars)
              | ExistsQuantifier vars -> ExistsQuantifier (quantiInt vars)
              | StableForallQuantifier vars -> StableForallQuantifier (quantiInt vars)),
            helper smtExpr
          )
        | _ -> smt

      commands
      |> List.fold
           (fun acc x ->
             match x with
             | Assert expr -> Assert (helper expr) :: acc
             | _ -> acc)
           []
      |> List.rev

    let asserts' =
      fun f ->
        asserts
        |> List.map (fun asrt ->
          match asrt with
          | Assert (QuantifierApplication (quantifiers, smtExpr)) ->
            (quantifiers
             |> List.fold
                  (fun acc x ->
                    match x with
                    | ForallQuantifier vars
                    | ExistsQuantifier vars
                    | StableForallQuantifier vars ->
                      acc
                      @ (vars
                         |> List.map (fun x -> Command (DeclareConst x))))
                  [],
             Assert (f smtExpr))
          | Assert expr -> ([], Assert (f expr))
          | _ -> ([], asrt))

    let skAsserts = asserts' Not

    let notSkAsserts = asserts' id

    let defConstants =
      (padding - 1)
      |> List.unfold (fun i -> if i >= 0 then Some (i, i - 1) else None)
      |> List.map (fun i -> Definition (DefineFun ($"c_{i}", [], IntSort, Number 0)))
      |> List.rev

    let decConstants =
      (padding - 1)
      |> List.unfold (fun i -> if i >= 0 then Some (i, i - 1) else None)
      |> List.map (fun i -> Command (DeclareConst ($"c_{i}", IntSort)))
      |> List.rev

    let defFunctions =
      commands |> List.filter (function | Definition (DefineFun _) -> true | _ -> false)
    
    (defFunctions, defConstants, decConstants, dataTypes, functions, asserts, skAsserts, notSkAsserts)

