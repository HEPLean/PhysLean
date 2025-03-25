/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Meta.TODO.Basic
/-!

## Getting an array of all file paths in PhysLean.

-/

open System

/-- The recursive function underlying `allFilePaths`. -/
partial def allFilePaths.go (prev : Array FilePath)
  (root : String) (path : FilePath) : IO (Array FilePath) := do
  let entries ← path.readDir
  let result ← entries.foldlM (init := prev) fun acc entry => do
    if ← entry.path.isDir then
      go acc (root ++ "/" ++ entry.fileName) entry.path
    else
      pure (acc.push (root ++ "/" ++ entry.fileName))
  pure result

/-- Gets an array of all file paths in `PhysLean`. -/
partial def allFilePaths : IO (Array FilePath) := do
  allFilePaths.go (#[] : Array FilePath) "./PhysLean" ("./PhysLean" : FilePath)
