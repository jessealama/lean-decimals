import Lake
open Lake DSL

package «lean-deccimal128» where
  -- add package configuration options here

lean_lib «LeanDeccimal128» where
  -- add library configuration options here

@[default_target]
lean_exe «lean-deccimal128» where
  root := `Main
