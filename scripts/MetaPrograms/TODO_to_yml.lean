/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Meta.Basic
import PhysLean.Meta.TODO.Basic
import Mathlib.Lean.CoreM
import PhysLean.Meta.Informal.Post
import PhysLean.Meta.Informal.SemiFormal
/-!

# Turning TODOs into YAML

-/

open Lean System Meta PhysLean


/-!

## PhysLean categories.

To be moved.

-/
inductive PhysLeanCategory
  | ClassicalMechanics
  | CondensedMatter
  | Cosmology
  | Elctromagnetism
  | Mathematics
  | Meta
  | Optics
  | Particles
  | QFT
  | QuantumMechanics
  | Relativity
  | StatisticalMechanics
  | Thermodynamics
  | Other
deriving BEq, DecidableEq

def PhysLeanCategory.string :  PhysLeanCategory → String
  | ClassicalMechanics => "Classical Mechanics"
  | CondensedMatter => "Condensed Matter"
  | Cosmology => "Cosmology"
  | Elctromagnetism => "Electromagnetism"
  | Mathematics => "Mathematics"
  | Meta => "Meta"
  | Optics => "Optics"
  | Particles => "Particles"
  | QFT => "QFT"
  | QuantumMechanics => "Quantum Mechanics"
  | Relativity => "Relativity"
  | StatisticalMechanics => "Statistical Mechanics"
  | Thermodynamics => "Thermodynamics"
  | Other => "Other"

def PhysLeanCategory.emoji : PhysLeanCategory → String
  | ClassicalMechanics => "⚙️"
  | CondensedMatter => "🧊"
  | Cosmology => "🌌"
  | Elctromagnetism => "⚡"
  | Mathematics => "➗"
  | Meta => "🏛️"
  | Optics => "🔍"
  | Particles => "💥"
  | QFT => "🌊"
  | QuantumMechanics => "⚛️"
  | Relativity => "⏳"
  | StatisticalMechanics => "🎲"
  | Thermodynamics => "🔥"
  | Other => "❓"

def PhysLeanCategory.List :  List PhysLeanCategory :=
  [ PhysLeanCategory.ClassicalMechanics,
    PhysLeanCategory.CondensedMatter,
    PhysLeanCategory.Cosmology,
    PhysLeanCategory.Elctromagnetism,
    PhysLeanCategory.Mathematics,
    PhysLeanCategory.Meta,
    PhysLeanCategory.Optics,
    PhysLeanCategory.Particles,
    PhysLeanCategory.QFT,
    PhysLeanCategory.QuantumMechanics,
    PhysLeanCategory.Relativity,
    PhysLeanCategory.StatisticalMechanics,
    PhysLeanCategory.Thermodynamics,
    PhysLeanCategory.Other]

instance : ToString PhysLeanCategory where
  toString := PhysLeanCategory.string

def PhysLeanCategory.ofFileName (n : Name) : PhysLeanCategory :=
  if n.toString.startsWith "PhysLean.ClassicalMechanics"  then
    PhysLeanCategory.ClassicalMechanics
  else if n.toString.startsWith "PhysLean.CondensedMatter" then
    PhysLeanCategory.CondensedMatter
  else if n.toString.startsWith "PhysLean.Cosmology" then
    PhysLeanCategory.Cosmology
  else if n.toString.startsWith "PhysLean.Electromagnetism" then
    PhysLeanCategory.Elctromagnetism
  else if n.toString.startsWith "PhysLean.Mathematics" then
    PhysLeanCategory.Mathematics
  else if n.toString.startsWith "PhysLean.Meta" then
    PhysLeanCategory.Meta
  else if n.toString.startsWith "PhysLean.Optics" then
    PhysLeanCategory.Optics
  else if n.toString.startsWith "PhysLean.Particles" then
    PhysLeanCategory.Particles
  else if n.toString.startsWith "PhysLean.QFT" then
    PhysLeanCategory.QFT
  else if n.toString.startsWith "PhysLean.QuantumMechanics" then
    PhysLeanCategory.QuantumMechanics
  else if n.toString.startsWith "PhysLean.Relativity" then
    PhysLeanCategory.Relativity
  else if n.toString.startsWith "PhysLean.StatisticalMechanics" then
    PhysLeanCategory.StatisticalMechanics
  else if n.toString.startsWith "PhysLean.Thermodynamics" then
    PhysLeanCategory.Thermodynamics
  else
    PhysLeanCategory.Other

/-########################-/

structure FullTODOInfo where
  content : String
  fileName : Name
  name : Name
  line : Nat
  isInformalDef : Bool
  isInformalLemma : Bool
  isSemiFormalResult : Bool
  category : PhysLeanCategory
  tag : String

def FullTODOInfo.ofTODO (t : todoInfo) : FullTODOInfo :=
  {content := t.content, fileName := t.fileName, line := t.line, name := t.fileName,
   isInformalDef := false, isInformalLemma := false,
   isSemiFormalResult := false, category := PhysLeanCategory.ofFileName t.fileName,
   tag := t.tag}

unsafe def getTodoInfo : MetaM (Array FullTODOInfo) := do
  let env ← getEnv
  let todoInfo := (todoExtension.getState env)
  -- pure (todoInfo.qsort (fun x y => x.fileName.toString < y.fileName.toString)).toList
  pure (todoInfo.map FullTODOInfo.ofTODO)

unsafe def informalTODO (x : ConstantInfo) : CoreM FullTODOInfo := do
  let name := x.name
  let tag ← Informal.getTag x
  let lineNo ← Name.lineNumber name
  let docString ← Name.getDocString name
  let file ← Name.fileName name
  let isInformalDef := Informal.isInformalDef x
  let isInformalLemma := Informal.isInformalLemma x
  let category := PhysLeanCategory.ofFileName file
  return {content := docString, fileName := file, line := lineNo, name := name,
          isInformalDef := isInformalDef, isInformalLemma := isInformalLemma,
          isSemiFormalResult := false, category := category,
          tag := tag}

unsafe def allInformalTODO : CoreM (Array FullTODOInfo) := do
  let x ← AllInformal
  x.mapM informalTODO

def FullTODOInfo.ofSemiFormal (t : WantedInfo) : FullTODOInfo :=
  {content := t.content, fileName := t.fileName, line := t.line, name := t.name,
   isInformalDef := false, isInformalLemma := false,
   isSemiFormalResult := true, category := PhysLeanCategory.ofFileName t.fileName,
   tag := t.tag}

unsafe def allSemiInformal  : CoreM (Array FullTODOInfo) := do
  let env ← getEnv
  let semiInformalInfos := (wantedExtension.getState env)
  pure (semiInformalInfos.map FullTODOInfo.ofSemiFormal)

def FullTODOInfo.toYAML (todo : FullTODOInfo) : MetaM String := do
  let content := todo.content
  let contentIndent := content.replace "\n" "\n      "
  return s!"
  - file: {todo.fileName}
    githubLink: {Name.toGitHubLink todo.fileName todo.line}
    line: {todo.line}
    isInformalDef: {todo.isInformalDef}
    isInformalLemma: {todo.isInformalLemma}
    isSemiFormalResult: {todo.isSemiFormalResult}
    category: {todo.category}
    name: {todo.name}
    tag: {todo.tag}
    content: |
      {contentIndent}"

unsafe def allTODOs : MetaM (List FullTODOInfo) := do
  let todos ← getTodoInfo
  let informalTODOs ← allInformalTODO
  let semiInformal ← allSemiInformal
  let all := todos ++ informalTODOs ++ semiInformal
  return  (all.qsort (fun x y => x.fileName.toString < y.fileName.toString
    ∨ (x.fileName.toString = y.fileName.toString ∧ x.line < y.line))).toList

unsafe def categoriesToYML : MetaM String := do
  let todos ← allTODOs
  let mut cat := "Category:\n"
  for c in PhysLeanCategory.List do
    let num := (todos.filter (fun x => x.category == c)).length
    cat := cat ++
    s!"
  - name: \"{c}\"
    num: {num}
    emoji: \"{c.emoji}\""
  return cat ++ "\n"

unsafe def todosToYAML : MetaM String := do
  let todos ← allTODOs
  /- Check no dulicate tags-/
  let tags := todos.map (fun x => x.tag)
  if !tags.Nodup then
    let duplicates := tags.filter (fun tag => tags.count tag > 1) |>.eraseDups
    println! duplicates
    panic! s!"Duplicate tags found: {duplicates}"
  /- End of check. -/
  let todosYAML ← todos.mapM FullTODOInfo.toYAML
  return "TODOItem:\n" ++ String.intercalate "\n" todosYAML

unsafe def fullTODOYML : MetaM String := do
  let cat ← categoriesToYML
  let todos ← todosToYAML
  return cat ++ todos
unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  println! "Generating TODO list."
  let ymlString ← CoreM.withImportModules #[`PhysLean] (fullTODOYML).run'
  println! ymlString
  let fileOut : System.FilePath := {toString := "./docs/_data/TODO.yml"}
  if "mkFile" ∈ args then
    IO.println (s!"TODOList file made.")
    IO.FS.writeFile fileOut ymlString
  pure 0
