import LeanGym

open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic Parser

def parseName (n : String) : Lean.Name :=
  (n.splitOn ".").foldl Lean.Name.mkStr Lean.Name.anonymous

def parseNamespaces (ns : String) : List Name :=
  if ns.front = '[' ∧ ns.back = ']' then
    let ns' := ns.extract (ns.next ⟨0⟩) (ns.prev ns.endPos)
    ns'.split (· = ' ') |>.map parseName
  else []

def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot) 
    (["build/lib", 
    -- "lake-packages/mathlib/build/lib/",  
    -- "lake-packages/std/build/lib/",
    -- "lake-packages/Qq/build/lib/", 
    "lake-packages/aesop/build/lib/"] |>.map System.FilePath.mk)
  let ((decl : Name), (ns : List OpenDecl)) ←
    match args with
      | [decl] => pure (parseName decl, [])
      | [decl, ns] => pure (parseName decl, parseNamespaces ns |>.map (.simple · []))
      | _ => IO.throwServerError "usage: \nlean-gym <decl>\nlean-gym <decl> [ns₁ ns₂ ... nsₖ]"
  let problem : Gym.Problem := { decl := decl, currNamespace := decl.getRoot, openDecls := ns }
  Gym.replFor problem