/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Lean
import HepLean.Meta.TODO.Basic
/-!

This file enables us to transverse tactics and test for conditions.

## References
The content of this file is based on the following sources (released under the Apache 2.0 license).

- https://github.com/dwrensha/tryAtEachStep/blob/main/tryAtEachStep.lean
- https://github.com/lean-dojo/LeanDojo/blob/main/src/lean_dojo/data_extraction/ExtractData.lean

Modifications have been made to the original content of these files here.

See also:
- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Memory.20increase.20in.20loops.2E
-/

open Lean Elab
open System (FilePath)

namespace transverseTactics

/-- Takes in a file and returns the infostates of commands and the corresponding
  environment before the command is processed. -/
partial def processCommands : Frontend.FrontendM (List (Environment × InfoState)) := do
  /- Very roughly, `Frontend.FrontendM (List (Environment × InfoState))` is equivalent
    to `Frontend.Context → Frontend.state → List (Environment × InfoState)`.

    The `←get` here is returning the inputted value of `Frontend.state`,
    from which we get the environment.
    -/
  let {env, ..} ← Frontend.getCommandState
  /- Processes a single command, adding it to `env`. This is done using
    `modify fun s => { s with commands := s.commands.push cmd }` as part of
    `Frontend.processCommand`. -/
  let done ← Frontend.processCommand
  /- Gets the infostate associated with the single command of the newly updated `Frontend.state`. -/
  let {infoState, ..} ← Frontend.getCommandState
  modify fun st => {st with commandState.infoState := {}}
  if done then
    return [(env, infoState)]
  else
    /- For each command, we return the environment before the command is processed,
      and the `infoState` associated with that command. -/
    return (env, infoState) :: (← processCommands)

end transverseTactics

partial def Lean.Elab.InfoTree.forInfoM (f : ContextInfo → Info → IO Unit) : InfoTree → IO Unit :=
  go none
where go (ctx? : Option ContextInfo) : InfoTree → IO Unit
  | .context i t => go (i.mergeIntoOuter? ctx?) t
  | .node i children => do
    if let some ctx := ctx? then
      f ctx i
    for t in children do
      go (i.updateContext? ctx?) t
  | .hole _ => return

TODO "Find a way to free the environment `env` in `transverseTactics`.
  This leads to memory problems when using `transverseTactics` directly in loops."
open transverseTactics in
/-- Applies `visitTacticInfo` to each tactic in a file. -/
unsafe def transverseTactics (file : FilePath)
  (visitTacticInfo : FilePath → ContextInfo → TacticInfo → CoreM Unit) : IO Unit := do
  searchPathRef.set compile_time_search_path%
  /- This is equivalent to `(IO.FS.readFile file).bind (fun fileContent => do ...)`. -/
  let fileContent ← IO.FS.readFile file
  enableInitializersExecution
  /- Get `Parser.InputContext` from file. -/
  let inputCtx := Parser.mkInputContext fileContent file.toString -- The input content of the file
  /- We parse the header. Recall that the parser is takes a string and
    outputs a Lean syntax object. -/
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  /- Recall that the elaborator turns a Lean syntax object into a Lean Expr object.
    In the below, we process the header, creating an environment with the relevant imports.
    This can be thought of as creating an import only file. -/
  if messages.hasErrors then
    for msg in messages.unreported do
      if msg.severity == .error then
        println! "ERROR: {← msg.toString}"
    throw $ IO.userError "Errors during import; aborting"
  for msg in messages.unreported do
    println! "{← msg.toString}"
  let (env, messages) ← processHeader header {} messages inputCtx
  if messages.hasErrors then
    for msg in messages.unreported do
      if msg.severity == .error then
        println! "ERROR: {← msg.toString}"
    throw $ IO.userError "Errors during import; aborting"
  /- As part of the environment header is the module name. This is not included
    in our current `env`. So we include it now. -/
  let env := env.setMainModule (← moduleNameOfFileName file none)
  /- From the environment, we create a state of the `Command` monad. -/
  let commandState := {Command.mkState env messages {} with infoState.enabled := true}
  /- We create a state of the `Frontend` monad-/
  /- Runs the `processCommands` function on the context defined by `inputCtx`, and the
  state defined by `frontendState`. -/
  let steps ← (processCommands.run {inputCtx}).run'
    {commandState, parserState, cmdPos := parserState.pos}
  /- Note that for us, each `infoState.trees` is actually of length 1. -/
  for (env, {trees, ..}) in steps do
    for t in trees do
      t.forInfoM fun
        | ctx, .ofTacticInfo i => ctx.runCoreM do
            setEnv env
            try visitTacticInfo file ctx i
            catch e => println! "caught: {←e.toMessageData.toString}"
        | _, _ => return

/-- Tests if a given `info` is `ofTacticInfo` and if so runs `visitTacticInfo`. -/
def visitInfo (file : FilePath) (env : Environment)
    (visitTacticInfo : FilePath → ContextInfo → TacticInfo → MetaM Unit) (ci : ContextInfo)
    (info : Info) (acc : List (IO Unit)) : List (IO Unit) :=
  match info with
  | .ofTacticInfo ti =>
    acc.cons <| ci.runMetaM default do
      setEnv env
      try visitTacticInfo file ci ti
      catch e => println! "caught: {←e.toMessageData.toString}"
  | _ => acc

#check Task
