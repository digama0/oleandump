import OLeanDump
import Qq

open IO System Process Lean Qq

def main (args : List String) : IO Unit := do
  match args with
  | [] =>
    println "Usage: ... filename [mod ...]"
    exit 1
  | file :: mods =>
    let cnt ← IO.FS.readBinFile file
    let ({ useGmp, leanVersion, githash, base, objs, root }, _last) ← IO.ofExcept <| parseOLean.run cnt
    IO.println s!"useGmp = {useGmp}"
    IO.println s!"leanVersion = {leanVersion}"
    IO.println s!"githash = {githash}"
    initSearchPath (← findSysroot)
    let opts := ({} : Options)
    let mods := if mods.isEmpty then #[`Lean] else mods.toArray.map String.toName
    let env ← importModules (mods.map ({ module := · })) opts
    let ctx : Core.Context := { fileName := "<input>", fileMap := ⟨"", #[0]⟩ }
    discard <| Core.CoreM.toIO (ctx := ctx) (s := { env }) <| Meta.MetaM.run do
      objs.main base root
