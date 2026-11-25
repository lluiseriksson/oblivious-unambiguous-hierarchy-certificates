import Lake
open Lake DSL

package «ObliviousUnambiguousHierarchy» where
  moreLeanArgs := #["-j", "1"]

@[default_target]
lean_lib «ObliviousUnambiguousHierarchy» where
