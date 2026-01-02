/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Comparator.ExportedEnv
import Comparator.Utils

namespace Comparator

namespace Compare

structure Context where
  challenge : ExportedEnv
  solution : ExportedEnv
  challengeNames : Std.HashSet Lean.Name

structure State where
  worklist : Array Lean.Name
  checked : Std.HashSet Lean.Name
  typeMismatches : Array Lean.Name
  bodyMismatches : Array Lean.Name

abbrev CompareM := ReaderT Context <| StateT State <| Except String

deriving instance BEq for Lean.QuotKind
deriving instance BEq for Lean.QuotVal
deriving instance BEq for Lean.InductiveVal
deriving instance BEq for Lean.ConstantInfo

def addWorklist (n : Lean.Name) : CompareM Unit := do
  if !(← get).checked.contains n then
    modify fun s => { s with worklist := s.worklist.push n }

partial def loop : CompareM Unit := do
  if (← get).worklist.isEmpty then
    return ()

  let target ← modifyGet fun s => (s.worklist.back!, { s with worklist := s.worklist.pop })
  if (← get).checked.contains target then
    loop
  else
    let some solutionConst := (← read).solution.constMap[target]?
      | throw s!"Const not found in target '{target}'"

    if let some challengeConst := (← read).challenge.constMap[target]? then
      -- Solution constant values don't need to match, since the challenges are expected to be axioms
      if (← read).challengeNames.contains target then
        if challengeConst.toConstantVal != solutionConst.toConstantVal then
          modify fun s => { s with typeMismatches := s.typeMismatches.push target }
      else
        if challengeConst != solutionConst then
          modify fun s => { s with bodyMismatches := s.bodyMismatches.push target }

    runForUsedConsts solutionConst addWorklist

    modify fun s => { s with checked := s.checked.insert target }
    loop

end Compare

structure CompareResult where
  typeMismatches : Array Lean.Name
  bodyMismatches : Array Lean.Name

def compareAt (challenge solution : ExportedEnv) (names : Array Lean.Name) (allChallengeNames : Array Lean.Name)
    (validChallengeKinds : Array String := #["axiom", "theorem"])
    (ignoreChallengeBodyKinds : Array String := #["axiom", "theorem"])
    : Except String CompareResult := do
  let mut challengeNames : Std.HashSet Lean.Name := {}

  for name in names do
    if !allChallengeNames.contains name then
      throw s!"Challenge must be in {allChallengeNames}: '{name}'"

  for name in allChallengeNames do
    let some challengeConst := challenge.constMap[name]?
      | throw s!"Const not found in challenge: '{name}'"

    let kind := Utils.constantKindName challengeConst

    if !validChallengeKinds.contains kind then
      throw s!"Challenge must be {validChallengeKinds} not {kind}: '{name}'"

    if ignoreChallengeBodyKinds.contains kind then
      challengeNames := challengeNames.insert name

  let prog := do
    names.forM Compare.addWorklist
    Compare.loop
  let (_, state) ← prog.run { challenge, solution, challengeNames } |>.run { worklist := #[], checked := {}, typeMismatches := #[], bodyMismatches := #[] }
  return { typeMismatches := state.typeMismatches, bodyMismatches := state.bodyMismatches }

end Comparator
