import Lean

open Lean

def main : IO Unit := do
  let contents ← IO.FS.readFile "lake-manifest.json"
  let manifest ← match Json.parse contents with
    | .ok value => pure value
    | .error message => throw <| IO.userError message
  let packages : Array Json := (manifest.getObjValAs? (Array Json) "packages").toOption.getD #[]
  for entry in packages do
    let name : String := (entry.getObjValAs? String "name").toOption.getD ""
    let rev : String := (entry.getObjValAs? String "rev").toOption.getD ""
    let dir := ".lake/packages/" ++ name
    let out ← IO.Process.output {cmd := "git", args := #["-C", dir, "rev-parse", "HEAD"]}
    if out.exitCode != 0 then throw <| IO.userError s!"Cannot read locked package {name}: {out.stderr}"
    let actual := out.stdout.trimAscii.toString
    if actual != rev then throw <| IO.userError s!"Revision mismatch for {name}: expected {rev}, got {actual}"
  IO.println s!"PASS: {packages.size} mathlib packages match lake-manifest.json"
