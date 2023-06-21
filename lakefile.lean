import Lake
open Lake DSL

package oleandump

lean_lib OLeanDump

require Qq from git "https://github.com/gebner/quote4" @ "master"

@[default_target]
lean_exe oleandump where
  root := `Main
  supportInterpreter := true
