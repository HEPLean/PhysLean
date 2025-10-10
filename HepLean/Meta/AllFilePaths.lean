/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.Meta.TODO.Basic
import Mathlib.Lean.Expr.Basic
import Mathlib.Util.GetAllModules
/-!

## Getting an array of all file paths in HepLean.

-/

open System (FilePath)

TODO "Make this definition more functional in style. In other words, remove the for loop."

/-- The recursive function underlying `allFilePaths`. -/
partial def allFilePaths.go (prev : Array FilePath)
  (root : String) (path : FilePath) : IO (Array FilePath) := do
  let mut r := prev
  for entry in ← path.readDir do
    if ← entry.path.isDir then
      r ← go r (root ++ "/" ++ entry.fileName) entry.path
    else
      r := r.push (root ++ "/" ++ entry.fileName)
  pure r

#check FilePath.walkDir
#check getAllFiles
#check Lean.SearchPath.findAllWithExt
#check Lean.forEachModuleInDir
#check Lean.Name.updatePrefix
#check Lean.Name.updateLast
/-- Gets an array of all file paths in `HepLean`. This function differs from
`System.FilePath.walkDir` in which we collect only files with extension `.lean`.
-/
partial def allFilePaths : IO (Array FilePath) := do
  allFilePaths.go (#[] : Array FilePath) "./HepLean" ("./HepLean" : FilePath)
