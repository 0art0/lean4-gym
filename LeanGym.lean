/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam

# Lean4 Gym

An extremely bare-bones REPL for proving in Lean4.

Usage: `lean-gym <declName>` will load `Init` and start a proving environment for `declName`
which expects commands in the form of `<branchId> <tactic-string>`

It is straightforward to extend this to also take:
- module imports
- open declarations
- the current namespace

However, there is currently no way to import *until* a given declaration.
We also currently do no checking that the proof avoids circularity.

Note: unlike most RL environments, we use persistent datastructures and
so we store all active tactic states rather than relying on the user
to recompute each path on every action.

Example (circular) run of `lean-gym Nat.add_comm`:

{"goals": ["⊢ ∀ (n m : Nat), n + m = m + n"], "errors": [], "branchId": 0}
> {"runTactic": [0, "intro n m"]}
{"goals": ["n m : Nat\n⊢ n + m = m + n"], "errors": [], "branchId": 1}
> {"runTactic": [1, "rw [Nat.add_comm]"]}
{"goals": [], "errors": [], "branchId": 2}
-/
import Lean
import Std.Data.HashMap
import Mathlib
import Aesop

open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic
open Std (HashMap)

def Lean.Message.isError (msg : Lean.Message) : Bool :=
  match msg.severity with
    | .error => true
    | _ => false

def Lean.MessageLog.getErrorMessages (log : MessageLog) : MessageLog :=
  { msgs := log.msgs.filter (·.isError) }


namespace Gym

/-!

## The proof search interface

Lean gym can be initialised with any declaration from the environment.

Tactics are supplied via the `runTactic` command, which also specifies the 
goal on which the tactic is to be applied.

The tactic states are all stored in a tree structure, indexed by unique identifiers.

-/

/-- The identifiers for the branches of the proof search tree. -/
abbrev BranchId : Type := Nat

/-- The proof search context (currently just an empty structure). -/
structure Context where

/-- The proof search state. -/
structure State where
  /-- A `HashMap` of tactic states, indexed by `BranchId`s. -/
  branches : Std.HashMap BranchId Tactic.SavedState := {}
  /-- The information about the next `BranchId`. -/
  nextId   : BranchId := 0

/-- The `Gym` monad, which keeps track of the tactic states, branches, and related information. -/
abbrev GymM := ReaderT Context (StateRefT State TermElabM)

/-- A structure encapsulating important details of the theorem to be proved, 
  including the relevant imports and namespaces to use. -/
structure Problem where
  /-- The name of the declaration in the environment. -/
  decl          : Name
  -- TODO: parse these from command-line
  /-- The list of imports. -/
  imports       : List Import   := [`Init, `Mathlib, `Std] |>.map ({module := ·})
  /-- The list of namespaces to open. -/
  openDecls     : List OpenDecl := []
  /-- The current namespace of the declaration. -/
  currNamespace : Name          := Name.anonymous

/-- The commands which can be performed to modify the proof tree in a Lean gym session. -/
inductive Command
  /-- Apply the given tactic (encoded as a string) on the specified branch of the proof tree. -/
  | runTactic : BranchId → String → Command
  /-- Discard the specified branch from the proof tree. -/
  | discard   : BranchId → Command
  deriving FromJson

/-- The response of the gym on running a `Command`. -/
structure Response where
  /-- The `BranchId` of the updated goal which is in current focus (if one exists). -/
  branchId : Option BranchId := none
  /-- The goals generated after running the `Command`. -/
  goals    : Array String := #[]
  /-- The errors generated after running the `Command`. -/
  errors   : Array String := #[]
  deriving ToJson

/-- The `REPL` back-end of Lean Gym.  -/
partial def replFor (problem : Problem) : IO Unit := do
  let termElabM : TermElabM Unit := do
    let some cInfo := (← getEnv).find? problem.decl | throwError "decl {problem.decl} not found"
    if ¬ (← isProp cInfo.type) then throwError "decl {problem.decl} not a theorem"
    let mvar ← mkFreshExprMVar (some cInfo.type) (kind := MetavarKind.synthetic)
    let termState : Term.SavedState ← Term.saveState
    let tacticState : Tactic.SavedState := { term := termState, tactic := { goals := [mvar.mvarId!] }}
    let context := {}
    let state := { branches := HashMap.empty.insert 0 tacticState, nextId := 1 }
    (welcome *> repl).run context |>.run' state

  let termElabCtx : Term.Context := {
    declName? := some (problem.decl ++ "_gym_"),
    errToSorry := false
  }

  let metaM : MetaM Unit := termElabM.run' (ctx := termElabCtx)
  let coreM : CoreM Unit := metaM.run'

  let env ← importModules problem.imports {} 0
  let coreCtx   : Core.Context := { 
    currNamespace := problem.currNamespace, 
    openDecls := problem.openDecls,
    fileName := "<Gym>",
    fileMap := { source := "", positions := #[0], lines := #[1] } }
  let coreState : Core.State := { env := env }

  let ((), _) ← coreM.toIO coreCtx coreState
  pure ()

where
  /-- The welcome message for the Lean Gym REPL. -/
  welcome : GymM Unit := do
    println! "{toJson (← responseForBranch 0)}"

  /-- Retrieve the details of a given `BranchId` as a `Response`. -/
  responseForBranch (id : BranchId) : GymM Response := do
    let some savedState ← pure ((← get).branches.find? id) | throwError "invalid branch id: {id}"
    let goals ← savedState.tactic.goals.mapM fun g => do pure $ toString (← Meta.ppGoal g)
    pure { branchId := id, goals := goals.toArray }

  /-- The main REPL loop of Lean gym. -/
  repl : GymM Unit := do
    IO.print "> "
    let response ← processCmd (← (← IO.getStdin).getLine)
    println! "{toJson response}"
    repl

  /-- Interpret the given string as a `Command` and execute it. -/
  -- TODO: Use better parsing here
  processCmd (cmd : String) : GymM Response := do
    match Json.parse cmd with
    | Except.error err => pure { errors := #[s!"failed to parse json: {err}"] }
    | Except.ok cmd    =>
      match (fromJson? cmd : Except String Command) with
      | Except.ok (Command.runTactic id tactic) => runTactic id tactic
      | Except.ok (Command.discard id)          => discard id
      | Except.error err                        => pure { errors := #[s!"failed to decode json: {err}"] }

  /-- Abandon the specified branch of the search tree. -/
  discard (id : BranchId) : GymM Response := do
    modify fun s => { s with branches := s.branches.erase id }
    pure {}

  /-- Attempt to run the given tactic on the given branch of the proof search tree. -/
  runTactic (id : BranchId) (tacticString : String) : GymM Response := do
    let some savedState ←  pure ((← get).branches.find? id) | throwError "unknown 'id': {id}"
    match Parser.runParserCategory (← getEnv) `tactic tacticString "<stdin>" with
    | Except.error err => pure { errors := #[err] }
    | Except.ok stx    => do
      savedState.term.restore
      let tac : TacticM Unit := set savedState.tactic *> evalTactic stx
      let mvarId : MVarId := savedState.tactic.goals.head!
      try
        -- the main step where the tactic is executed
        let unsolvedGoals ← Tactic.run mvarId tac
        if (← getThe Core.State).messages.hasErrors then
          let messages := (← getThe Core.State).messages.getErrorMessages.toList.toArray
          pure { errors := ← (messages.map Message.data).mapM fun md => md.toString }
        else
          let nextId := (← get).nextId
          let savedState : Tactic.SavedState := { term := (← Term.saveState), tactic := { goals := unsolvedGoals}}
          modify fun s => { s with branches := s.branches.insert nextId savedState, nextId := nextId + 1 }
          responseForBranch nextId
      catch ex =>
        pure { errors := #[← ex.toMessageData.toString] }

end Gym