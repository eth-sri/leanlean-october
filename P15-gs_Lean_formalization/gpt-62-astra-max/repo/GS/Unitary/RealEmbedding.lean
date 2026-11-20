module

public import GS.Core
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section
noncomputable section
open Matrix
namespace GS.Isometric
variable (𝕜 : Type*) [RCLike 𝕜] {n : ℕ}
abbrev extendReal : Mat n →+* Square 𝕜 n := (algebraMap ℝ 𝕜).mapMatrix
lemma extend_unitary {A : Mat n} (h : Orthogonal A) : IsU (extendReal 𝕜 A) := by
  have eq : (extendReal 𝕜 A)ᴴ = extendReal 𝕜 Aᴴ := by ext; simp [extendReal,conjTranspose_apply,RCLike.star_def]
  apply IsU.of_left; rw [eq,← map_mul,show Aᴴ * A = 1 from h.1,map_one]
end GS.Isometric
