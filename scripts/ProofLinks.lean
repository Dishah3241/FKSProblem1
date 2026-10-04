/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import Lean
import scripts.StatementProof

/-!
# Audit proofs of reader-facing standalone claims

The Mathlib-only and dependency-only statement modules at the roots of their trees and under
`Examples/` deliberately define propositions without importing their proofs. This audit discovers
every closed proposition in those modules and requires an exact entry in the module's final
formal-proof block and a theorem named `Claim.proof` in the sibling `FooProof` module. It also
checks that the kernel-checked theorem concludes with exactly that proposition applied to the same
parameters. Files under `Support/` are proof plumbing and are deliberately excluded.

A frozen question may instead be an open claim: its formal-proof line is
``* `Claim` → open: <reason>`` with a non-empty reason, and its declaration docstring begins with
"Open problem" (case-insensitively). One marker without the other is a violation; an open claim
must have no `Claim.proof`; and every statement module must retain at least one proved, linked
claim. Open claims remain subject to the separate fidelity audit.

An externally refuted question with no local proof instead begins its docstring with "Refuted
elsewhere" and uses ``* `Claim` → refuted-elsewhere: YYYY-MM-DD <URL>``. The date is the evidence
check date; the HTTPS URL must pin a full commit SHA in a GitHub or GitLab repository URL.
Encode GitLab's dash separator as `/%2D/` inside a Lean comment. This checks the record's
syntax, not the external proof. It cannot coexist with an
open mark or a local `Claim.proof`, and does not count as a proved linked claim.

Consequently, adding or removing an isolated claim without updating its proof block, or deleting or
renaming its proof, fails the audit. Predicate definitions with a mathematical input, such as
`IsReduced x`, are terminology rather than closed claims and are not selected. Run this executable
after `lake build`.
-/

open Lean

private structure ClaimFamily where
  statementModule : Name
  statementFile : System.FilePath
  proofModule : Name
  proofExists : Bool

private def isolatedDirs : Array System.FilePath := #[
  "FKSProblem1/Standalone/Mathlib",
]

private def pathToModule (path : System.FilePath) : Name :=
  (path.withExtension "").components.foldl (fun name part => Name.mkStr name part) Name.anonymous

private partial def collectLeanFiles
    (directory : System.FilePath) : IO (Array System.FilePath) := do
  let mut files := #[]
  for entry in (← directory.readDir) do
    if ← entry.path.isDir then
      if !entry.path.components.contains "Support" then
        files := files ++ (← collectLeanFiles entry.path)
    else if entry.path.extension == some "lean" then
      files := files.push entry.path
  return files

private def isProofFile (path : System.FilePath) : Bool :=
  path.toString.endsWith "Proof.lean"

private def discoverClaimFamilies : IO
    (Array ClaimFamily × Array Name × Array Name) := do
  let mut files := #[]
  for directory in isolatedDirs do
    files := files ++ (← collectLeanFiles directory)
  let modules := files.map pathToModule
  let proofModules := (files.filter isProofFile).map pathToModule
  let statementFiles := files.filter (!isProofFile ·)
  let families := statementFiles.map fun statementFile =>
    let statementModule := pathToModule statementFile
    let proofModule := Name.mkStr statementModule.getPrefix
      (statementModule.getString! ++ "Proof")
    {
      statementModule
      statementFile
      proofModule
      proofExists := proofModules.contains proofModule
    }
  let orphanProofs := proofModules.filter fun proofModule =>
    !families.any (·.proofModule == proofModule)
  return (families, modules, orphanProofs)

private def declarationType : ConstantInfo → Expr
  | .axiomInfo value | .defnInfo value | .thmInfo value | .opaqueInfo value |
      .ctorInfo value | .recInfo value | .inductInfo value => value.type
  | .quotInfo value => value.type

/-- A closed proposition may quantify over types and typeclass instances, but has no mathematical
input such as a series or an omnific integer. -/
private def isClosedProposition : Expr → Bool
  | .forallE _ domain body binderInfo =>
      (domain.isSort || binderInfo.isInstImplicit) && isClosedProposition body
  | .sort .zero => true
  | _ => false

private def expectedProofName (claim : Name) : Name := Name.mkStr claim "proof"

private def proofLine (claim proof : Name) : String :=
  s!"* `{claim.getString!}` → `{claim.getString!}.{proof.getString!}`"

private def openPrefix (claim : Name) : String :=
  s!"* `{claim.getString!}` → open: "

private def openReason? (block : String) (claim : Name) : Option String := Id.run do
  let marker := openPrefix claim
  for line in block.splitOn "\n" do
    if line.startsWith marker then
      let reason := ((line.splitOn marker)[1]?.getD "").trimAscii.toString
      if !reason.isEmpty then
        return some reason
  return none

private def refutedPrefix (claim : Name) : String :=
  s!"* `{claim.getString!}` → refuted-elsewhere:"

private def refutedRecord? (block : String) (claim : Name) : Option String := Id.run do
  let marker := refutedPrefix claim
  for line in block.splitOn "\n" do
    if line.startsWith marker then
      return some (((line.splitOn marker)[1]?.getD "").trimAscii.toString)
  return none

private def isEvidenceDate (date : String) : Bool :=
  match date.splitOn "-" with
  | [year, month, day] => Id.run do
      if year.length != 4 || month.length != 2 || day.length != 2 ||
          ![year, month, day].all (fun s => s.toList.all Char.isDigit) then
        return false
      let some y := year.toNat? | return false
      let some m := month.toNat? | return false
      let some d := day.toNat? | return false
      let leap := y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)
      let days := if m == 2 then (if leap then 29 else 28)
        else if [4, 6, 9, 11].contains m then 30 else 31
      return y > 0 && m > 0 && m ≤ 12 && d > 0 && d ≤ days
  | _ => false

private def isFullCommit (sha : String) : Bool :=
  sha.length == 40 &&
    sha.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F'))

private def isCommitPinnedUrl (url : String) : Bool :=
  if url.toList.any (fun c => c == '?' || c == '#') then false else
  match url.splitOn "/" with
  | "https:" :: "" :: "github.com" :: owner :: repo :: kind :: sha :: rest =>
      !owner.isEmpty && !repo.isEmpty && isFullCommit sha &&
        (kind == "commit" || (kind == "blob" || kind == "raw") && !rest.isEmpty)
  | "https:" :: "" :: "gitlab.com" :: owner :: repo :: separator :: kind :: sha :: rest =>
      ["-", "%2D", "%2d"].contains separator &&
        !owner.isEmpty && !repo.isEmpty && isFullCommit sha &&
        (kind == "commit" || (kind == "blob" || kind == "raw") && !rest.isEmpty)
  | "https:" :: "" :: "raw.githubusercontent.com" :: owner :: repo :: sha :: rest =>
      !owner.isEmpty && !repo.isEmpty && isFullCommit sha && !rest.isEmpty
  | _ => false

private def validRefutedRecord (record : String) : Bool :=
  match record.splitOn " " with
  | [date, url] => isEvidenceDate date && isCommitPinnedUrl url
  | _ => false

private def containsText (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

/-- The docstring *begins* with the words "open problem", case-insensitively. A proved claim may
mention an open problem later in its docstring (for example "the `d = 3` case of an open problem")
without being taken for an open claim. -/
private def saysOpenProblem (doc : String) : Bool :=
  let words : List String :=
    ((doc.toLower.split (fun (c : Char) => !c.isAlphanum)).toList.map (·.toString)).filter
      (!·.isEmpty)
  words.take 2 == ["open", "problem"]

private def saysRefutedElsewhere (doc : String) : Bool :=
  let words : List String :=
    ((doc.toLower.split (fun (c : Char) => !c.isAlphanum)).toList.map (·.toString)).filter
      (!·.isEmpty)
  words.take 2 == ["refuted", "elsewhere"]

private def audit (families : Array ClaimFamily) (orphanProofs : Array Name) :
    CoreM (Array (Name × Name) × Array (Name × String) × Array (Name × String) × Array String) := do
  let environment ← getEnv
  let moduleNames := environment.allImportedModuleNames
  let mut links := #[]
  let mut opens := #[]
  let mut refuted := #[]
  let mut violations := orphanProofs.map fun proofModule =>
    s!"{proofModule} has no `Foo` statement sibling"
  for family in families do
    let claims := environment.constants.fold (init := #[]) fun claims claim info => Id.run do
      let some checkedInfo := environment.checked.get.find? claim | claims
      let isClaimDeclaration := match checkedInfo with
        | .defnInfo _ | .inductInfo _ => true
        | _ => false
      if !isClaimDeclaration then
        return claims
      let some index := environment.getModuleIdxFor? claim | claims
      let some moduleName := moduleNames[index.toNat]? | claims
      if moduleName == family.statementModule &&
          isClosedProposition (declarationType info) then
        claims.push claim
      else
        claims
    if claims.isEmpty then
      violations := violations.push
        s!"{family.statementModule} is reader-facing but states no closed proposition"
      continue
    if !family.proofExists then
      violations := violations.push
        s!"{family.statementModule} has closed claims but no sibling {family.proofModule}"
    let source ← IO.FS.readFile family.statementFile
    let proofBlock := source.splitOn "## Formal proof"
    let block := if proofBlock.length == 2 then proofBlock[1]! else ""
    let mut expectedLines := #[]
    let mut provedCount := 0
    for claim in claims do
      let reason? := openReason? block claim
      let record? := refutedRecord? block claim
      let doc? ← findDocString? environment claim
      let docSaysOpen := saysOpenProblem (doc?.getD "")
      let docSaysRefuted := saysRefutedElsewhere (doc?.getD "")
      if reason?.isSome != docSaysOpen then
        violations := violations.push s!"{claim}: open marker and docstring disagree"
      if record?.isSome != docSaysRefuted then
        violations := violations.push s!"{claim}: refuted marker and docstring disagree"
      if record?.isSome && (reason?.isSome || docSaysOpen) then
        violations := violations.push s!"{claim}: open mark conflicts with refuted record"
      if let some record := record? then
        expectedLines := expectedLines.push (refutedPrefix claim ++ " " ++ record)
        if !validRefutedRecord record then
          violations := violations.push
            s!"{claim}: refuted evidence requires YYYY-MM-DD and a commit-pinned HTTPS URL"
        if (environment.checked.get.find? (expectedProofName claim)).isSome then
          violations := violations.push
            s!"{claim} is marked refuted elsewhere but has a local proof"
        if docSaysRefuted && validRefutedRecord record then
          refuted := refuted.push (claim, record)
      if let some reason := reason? then
        expectedLines := expectedLines.push (openPrefix claim ++ reason)
        if (environment.checked.get.find? (expectedProofName claim)).isSome then
          violations := violations.push
            s!"{claim} is marked open but has a proof; link it instead"
        if docSaysOpen then
          opens := opens.push (claim, reason)
      else if record?.isNone then
        expectedLines := expectedLines.push (proofLine claim (expectedProofName claim))
        provedCount := provedCount + 1
    if provedCount == 0 then
      let claimNames := String.intercalate ", " (claims.toList.map toString)
      violations := violations.push
        s!"{family.statementModule}: no proved linked claim ({claimNames})"
    match proofBlock with
    | [_before, block] =>
        if !containsText block s!"`{family.proofModule.getString!}`" then
          violations := violations.push
            s!"{family.statementFile}: formal-proof block omits sibling {family.proofModule}"
        for expected in expectedLines do
          if !containsText block expected then
            violations := violations.push
              s!"{family.statementFile}: formal-proof block omits `{expected}`"
        for line in block.splitOn "\n" do
          if line.startsWith "* `" && !expectedLines.contains line then
            violations := violations.push
              s!"{family.statementFile}: stale formal-proof line `{line}`"
    | _ =>
        violations := violations.push
          s!"{family.statementFile}: expected exactly one `## Formal proof` block"
    for claim in claims do
      let some info := environment.checked.get.find? claim | continue
      if (openReason? block claim).isSome || (refutedRecord? block claim).isSome then
        continue
      let proof := expectedProofName claim
      let some proofInfo := environment.checked.get.find? proof
        | violations := violations.push s!"{claim} has no proof {proof}"
          continue
      if StatementProof.isExactProofType claim (declarationType info)
          (declarationType proofInfo) then
        links := links.push (claim, proof)
      else
        violations := violations.push s!"{proof} does not prove {claim}"
  return (links, opens, refuted, violations)

/-- Import the proof modules with environment extensions initialized. The resulting environment is
kept until this short-lived process exits, as initializer results may point into its regions. -/
private unsafe def withImportedEnv {α} (modules : Array Name) (action : CoreM α) : IO α := do
  enableInitializersExecution
  initSearchPath (← findSysroot)
  let imports := modules.map fun module => ({ module } : Import)
  let environment ← importModules imports {} (trustLevel := 1024)
    (leakEnv := true) (loadExts := true)
  Prod.fst <$> Core.CoreM.toIO
    (ctx := { fileName := "<proof-links>", fileMap := default })
    (s := { env := environment }) action

public unsafe def main : IO UInt32 := do
  let (families, modules, orphanProofs) ← discoverClaimFamilies
  let (links, opens, refuted, violations) ← withImportedEnv modules (audit families orphanProofs)
  if !violations.isEmpty then
    IO.eprintln s!"proof-links: {violations.size} violation(s):"
    for violation in violations do
      IO.eprintln s!"  {violation}"
    return 1
  if links.isEmpty then
    IO.eprintln "proof-links: discovered no isolated claims."
    return 1
  for (claim, proof) in links do
    IO.println s!"{claim} ← {proof}"
  for (claim, reason) in opens do
    IO.println s!"open: {claim} ({reason})"
  for (claim, record) in refuted do
    IO.println s!"refuted-elsewhere: {claim} ({record}; no local proof)"
  let total := links.size + opens.size + refuted.size
  IO.println (s!"proof-links: verified {total} automatically discovered isolated claims " ++
    s!"({links.size} linked, {opens.size} open, {refuted.size} refuted elsewhere).")
  return 0
