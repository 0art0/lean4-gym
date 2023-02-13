import LeanGym

open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic

def parseName (n : String) : Lean.Name :=
  (n.splitOn ".").foldl Lean.Name.mkStr Lean.Name.anonymous

def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot) 
    (["build/lib", 
    -- "lake-packages/mathlib/build/lib/",  
    -- "lake-packages/std/build/lib/",
    -- "lake-packages/Qq/build/lib/", 
    "lake-packages/aesop/build/lib/"] |>.map System.FilePath.mk)
  let [decl] ← pure args | IO.throwServerError "usage: lean-gym <decl>"
  let decl := parseName decl
  let problem : Gym.Problem := { decl := decl, currNamespace := decl.getRoot }
  Gym.replFor problem