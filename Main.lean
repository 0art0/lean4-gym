import LeanGym

open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic Parser

def parseName (n : String) : Lean.Name :=
  (n.splitOn ".").foldl Lean.Name.mkStr Lean.Name.anonymous

def parseNamespaces (ns : String) : List Name :=
  if ns.front = '[' ∧ ns.back = ']' then -- check whether the string is enclosed within `[` ... `]`
    let ns' := ns.extract (ns.next ⟨0⟩) (ns.prev ns.endPos) -- extract the portion within `[` ... `]`
    ns'.split (· = ' ') |>.map parseName -- split by whitespace
  else [] -- defaults to no namespaces

def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot) 
    (["build/lib", 
    "lake-packages/mathlib/build/lib/",  
    "lake-packages/std/build/lib/",
    "lake-packages/Qq/build/lib/", 
    "lake-packages/aesop/build/lib/"] |>.map System.FilePath.mk)
  let ((decl : Name), (ns : List OpenDecl)) ←
    match args with
      | [decl] => pure (parseName decl, [])
      | [decl, ns] => pure (parseName decl, parseNamespaces ns |>.map (.simple · []))
      -- namespaces are accepted as a space-separated list of identifiers enclosed within `[` ... `]`.
      | _ => IO.throwServerError "usage: \nlean-gym <decl>\nlean-gym <decl> [ns₁ ns₂ ... nsₖ]"
  let problem : Gym.Problem := { decl := decl, currNamespace := decl.getRoot, openDecls := ns }
  Gym.replFor problem