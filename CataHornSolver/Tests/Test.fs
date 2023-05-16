module Tests.ProofBased.Test

open System.IO
open NUnit.Framework
open ProofBased
open Z3Interpreter.AST

[<TestFixture>]
type TestClass () =
  let runWithoutFuns consts defFns decFns asserts =
      Solver.solver [] Map.empty [] consts defFns decFns asserts
  
  [<Test>]
  member this.ListLenInv () =
    let file = Path.Join(TestContext.CurrentContext.TestDirectory, "Tests/Source/racer.horn.smt2")
    Assert.True((Solver.run file None) = "SAT")
    
  
  // [<Test>]
  // member this.TestDiseqInt () =
  //   let dConsts =
  //     [ Def ("c_0", [], Integer, Int 0); Def ("c_1", [], Integer, Int 0); Def ("c_2", [], Integer, Int 1) ]
  //   
  //   let dDefFuns =
  //     [ Def ("Z", [], Integer, Apply ("c_0", []))
  //       Def ("S", [ "x" ], Integer, Add (Apply ("c_1", []), Mul (Apply ("c_2", []), Var "x"))) ]
  //   
  //   let dDeclFuns = [ Decl ("diseqInt", 2) ]
  //   
  //   let dA1 =
  //     Assert (ForAll ([| "x1" |], App ("diseqInt", [| Apply ("Z", []); Apply ("S", [ Var "x1" ]) |])))
  //   
  //   let dA2 =
  //     Assert (ForAll ([| "x2" |], App ("diseqInt", [| Apply ("S", [ Var "x2" ]); Apply ("Z", []) |])))
  //   
  //   let dA3 =
  //     Assert (
  //       ForAll (
  //         [| "x3"; "y3" |],
  //         Implies (
  //           App ("diseqInt", [| Var "x3"; Var "y3" |]),
  //           App ("diseqInt", [| Apply ("S", [ Var "x3" ]); Apply ("S", [ Var "y3" ]) |])
  //         )
  //       )
  //     )
  //   
  //   let dA4 =
  //     Assert (ForAll ([| "x4" |], Implies (App ("diseqInt", [| Var "x4"; Var "x4" |]), Bool false)))
  //   runWithoutFuns dConsts dDefFuns dDeclFuns [ dA2; dA1; dA3; dA4 ] |> printfn "%O"
  //   Assert.True(runWithoutFuns dConsts dDefFuns dDeclFuns [ dA2; dA1; dA3; dA4 ] = "SAT")
  //
  // [<Test>]
  // member this.TestLastAppList () =
  //   let listConst =
  //     [ Def ("c_0", [], Integer, Int 0)
  //       Def ("c_1", [], Integer, Int 1)
  //       Def ("c_2", [], Integer, Int 1)
  //       Def ("c_3", [], Integer, Int 1) ]
  //   
  //   let listDefFuns =
  //     [ Def ("nil", [], Integer, Apply ("c_0", []))
  //       Def (
  //         "cons",
  //         [ "x"; "y" ],
  //         Integer,
  //         Add (Apply ("c_1", []),  Add (Mul (Apply ("c_2", []), Var "x"), Mul (Apply ("c_3", []), Var "y")))
  //       ) ]
  //   
  //   let listDeclFuns = [ Decl ("app", 3); Decl ("last", 2) ]
  //   
  //   let listAssert1 =
  //     Assert (ForAll ([| "ys1" |], App ("app", [| Apply ("nil", []); Var "ys1"; Var "ys1" |])))
  //   
  //   let listAssert2 =
  //     Assert (
  //       ForAll (
  //         [| "x2"; "xs2"; "ys2"; "zs2" |],
  //         Implies (
  //           App ("app", [| Var "xs2"; Var "ys2"; Var "zs2" |]),
  //           App (
  //             "app",
  //             [| Apply ("cons", [ Var "x2"; Var "xs2" ])
  //                Var "ys2"
  //                Apply ("cons", [ Var "x2"; Var "zs2" ]) |]
  //           )
  //         )
  //       )
  //     )
  //   let listAssert3 =
  //     Assert (ForAll ([| "x3" |], App ("last", [| Apply ("cons", [ Var "x3"; Apply ("nil", []) ]); Var "x3" |])))
  //   
  //   let listAssert4 =
  //     Assert (
  //       ForAll (
  //         [| "xs4"; "n4"; "x4" |],
  //         Implies (
  //           And
  //             [| Not (Eq (Var "xs4", Apply ("nil", [])))
  //                App ("last", [| Var "xs4"; Var "n4" |]) |],
  //           App ("last", [| Apply ("cons", [ Var "x4"; Var "xs4" ]); Var "n4" |])
  //         )
  //       )
  //     )
  //   
  //   let listAssert5 =
  //     Assert (
  //       ForAll (
  //         [| "ys5"; "zs5"; "m5"; "xs5"; "n5" |],
  //         Implies (
  //           And
  //             [| App ("app", [| Var "xs5"; Var "ys5"; Var "zs5" |])
  //                App ("last", [| Var "ys5"; Var "n5" |])
  //                App ("last", [| Var "zs5"; Var "m5" |])
  //                Not (Eq (Var "ys5", Apply ("nil", [])))
  //                Not (Eq (Var "n5", Var "m5")) |],
  //           Bool false
  //         )
  //       )
  //     )
  //   
  //   let actual =
  //     Process.Process.runWithTimeout
  //       1000
  //       (fun _ -> runWithoutFuns listConst listDefFuns listDeclFuns [ listAssert1; listAssert2; listAssert3; listAssert4; listAssert5 ] )
  //     
  //     
  //   Assert.True((actual = Some "SAT"))
  //   
  //   
  //
  //