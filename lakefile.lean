import Lake
open Lake DSL

package "lean-concrete-semantics" where
  -- add package configuration options here

lean_lib «LeanConcreteSemantics» where
  -- add library configuration options here

@[default_target]
lean_exe "lean-concrete-semantics" where
  root := `Main

require aesop from git "https://github.com/leanprover-community/aesop" @ "v4.11.0"
