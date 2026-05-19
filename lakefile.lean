import Lake
open Lake DSL

package rsfzig where
  leanOptions := #[]

@[default_target]
lean_lib RSFFormalization where
  srcDir := "."

lean_lib RSF_Acceptance where
  srcDir := "."
