import Lean

open Lean Lean.Elab

set_option autoImplicit false

def parseName (n : String) : Lean.Name :=
  (n.splitOn ".").foldl Lean.Name.mkStr Lean.Name.anonymous

def parseNamespaces (ns : String) : List Name :=
  if ns.front = '[' ∧ ns.back = ']' then -- check whether the string is enclosed within `[` ... `]`
    let ns' := ns.extract (ns.next ⟨0⟩) (ns.prev ns.endPos) -- extract the portion within `[` ... `]`
    ns'.split (· = ' ') |>.map parseName -- split by whitespace
  else [] -- defaults to no namespaces

-- def parseCommand (cmd : String) : 

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