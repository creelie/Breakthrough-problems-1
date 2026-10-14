import Lake
open Lake DSL

package WormaldTournament where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.34.1"

/-- Wormald's Hessian determinant for regular tournaments: the algebraic core -/
@[default_target]
lean_lib WormaldTournament
