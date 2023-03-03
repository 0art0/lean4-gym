import Lean

open Lean Lean.Elab

set_option autoImplicit false

declare_syntax_cat gym_command
syntax tactic : gym_command
syntax num ":" tactic : gym_command
syntax "discardId" num : gym_command

#eval do
  let stx? : Except String Syntax := Parser.runParserCategory (← getEnv) `gym_command "intro n m" "input"
  match stx? with
  | .error e =>
    dbg_trace e
    return default
  | .ok stx =>
  (return stx : TermElabM Syntax)