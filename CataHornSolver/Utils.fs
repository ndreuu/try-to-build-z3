module ProofBased.Utils

open System
open System.Text.RegularExpressions


let flip f a b = f b a

open SMTLIB2

let inline join s (xs: string seq) = String.Join (s, xs)

module IntOps =
  let mulOp = ElementaryOperation ("*", [ IntSort; IntSort ], IntSort)
  let negOp = ElementaryOperation ("-", [ IntSort ], IntSort)
  let minusOp = ElementaryOperation ("-", [ IntSort; IntSort ], IntSort)
  let addOp = ElementaryOperation ("+", [ IntSort; IntSort ], IntSort)
  let eqOp = ElementaryOperation ("=", [ IntSort; IntSort ], BoolSort)
  let grOp = ElementaryOperation (">", [ IntSort; IntSort ], BoolSort)
  let lsOp = ElementaryOperation ("<", [ IntSort; IntSort ], BoolSort)
  let leqOp = ElementaryOperation ("<=", [ IntSort; IntSort ], BoolSort)
  let geqOp = ElementaryOperation (">=", [ IntSort; IntSort ], BoolSort)
  let modOp = ElementaryOperation ("mod", [ IntSort; IntSort ], IntSort)


let balancedBracket (str: string) =
  let rec helper depth acc =
    function
    | _ when depth = 0 -> Some acc
    | h :: tl ->
      let inc =
        match h with
        | '(' -> 1
        | ')' -> -1
        | _ -> 0

      helper (depth + inc) (h :: acc) tl
    | _ -> None

  str.Substring 1
  |> Seq.toList
  |> helper 1 []
  |> function
    | Some cs ->
      List.fold (fun acc c -> $"{c}{acc}") "" cs
      |> (fun str -> $"({str}" )
      |> Some
    | None -> None



let varsIdxs (str: string) =
  let var = Regex "a![0-9]+"

  let verIdxs =
    var.Matches str
    |> Seq.toArray
    |> Array.map (fun m -> (m.Value, m.Index + m.Value.Length + 1))
    |> Array.fold
      (fun (acc, added) (name, _ as p) ->
        match added with
        | _ when added |> List.contains name -> (acc, added)
        | _ -> (p :: acc, name :: added))
      ([], [])
    |> fst
    |> List.rev

  verIdxs
  |> List.map (fun (v, i) ->
    str.Substring i
    |> balancedBracket
    |> function
      | Some s -> (v, s)
      | None -> failwith "Wrong proof format")

let substituteVars str varsIdxs =
  let mp =
    Regex(@"\(mp").Matches str
    |> fun mps -> mps[0].Index
    |> str.Substring
    |> balancedBracket
    |> function
      | Some s -> s
      | None -> "Wrong proof format"

  varsIdxs
  |> List.rev
  |> List.fold (fun (acc: string) (var: string, value) -> acc.Replace (var, value)) mp

let clean (str: string) =
  printfn $"{str}"
  let weightStr = Regex ":weight [0-9]+\)|\(!"

  weightStr.Replace (str, String.Empty)
  |> fun str ->
    let rQuery = Regex "\(query"

    rQuery.Matches str
    |> Seq.toArray
    |> fun arr ->
        str.Substring arr[0].Index
        |> balancedBracket
        |> function
          | Some s -> str.Replace (s, "false") |> fun str -> str.Replace ("mp", "proof mp")
          | None -> "Wrong proof format"

let assertedPos str =
  Regex(@"\(asserted").Matches str
  |> Seq.toArray
  |> Array.map (fun m -> m.Index)
  |> Array.map (fun i ->
    str.Substring i
    |> balancedBracket
    |> function
      | Some s -> s
      | None -> failwith "Wrong proof format")
  |> Array.fold (fun (acc: string) a -> acc.Replace (a, "(asserted (=> false false))")) str





let proof dbg str =
  dbg ()
  assertedPos str |> fun str -> varsIdxs str |> substituteVars str |> clean
