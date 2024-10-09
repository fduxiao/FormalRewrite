import Lake
open Lake DSL

meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"

package «FormalRewrite» where
  -- add package configuration options here

lean_lib «FormalRewrite» where
  -- add library configuration options here

@[default_target]
lean_exe «formal-rewrite» where
  root := `Main
