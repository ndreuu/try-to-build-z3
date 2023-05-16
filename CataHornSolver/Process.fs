module Process.Process
open System.IO
open System.Threading.Tasks


open System

type ProcessResult = { 
    ExitCode : int; 
    StdOut : string; 
    StdErr : string 
}

let execute processName processArgs =
    let psi = Diagnostics.ProcessStartInfo(processName, processArgs) 
    psi.UseShellExecute <- false
    psi.RedirectStandardOutput <- true
    psi.RedirectStandardError <- true
    psi.CreateNoWindow <- true        
    let proc = Diagnostics.Process.Start(psi) 
    let output = Text.StringBuilder()
    let error = Text.StringBuilder()
    proc.OutputDataReceived.Add(fun args -> output.Append(args.Data) |> ignore)
    proc.ErrorDataReceived.Add(fun args -> error.Append(args.Data) |> ignore)
    proc.BeginErrorReadLine()
    proc.BeginOutputReadLine()
    proc.WaitForExit()
    { ExitCode = proc.ExitCode; StdOut = output.ToString(); StdErr = error.ToString() }

let runWithTimeout (timeout: int) (action: unit -> 'a) : 'a option =
  let work = Task.Run (fun () -> Some (action ()))
  let delay = Task.Delay(timeout).ContinueWith (fun t -> None)
  Task.WhenAny(work, delay).Result.Result

let foreachFleTimeout timeout dir f g =
  let files = Directory.GetFiles (dir, @"*.smt2")

  for file in files do
    runWithTimeout timeout f |> g file

