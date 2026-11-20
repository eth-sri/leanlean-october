module

public import GS.Geodesics.OrbitBlock
public import GS.Geodesics.ShuffleCondition

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Matrix-orbit geodesics for the scalar shuffle

Here `k₁` is the number of right-layer blocks, and `b₁` is their size.
The exact original permutation is used. The inequality `b₂ ≤ k₁` is proved
sufficient, without assuming an injectivity, stabilizer or connection claim.

All statements concern the real orthogonal family with independent blocks.
No sharing constraint or special-unitary interpretation is introduced.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.Extensions GS.Continuation GS.LieAction GS.CayleyCharts
open GS.ManifoldCompletion GS.OverlapGeometry
open scoped Topology Manifold
namespace GS.Geodesics

section FixedDimension
variable (b₁ k₁ b₂ : ℕ)
local notation "rblock" => (fun i : Fin (k₁*b₁) => Fin.val i / b₁)
local notation "lblock" => (fun i : Fin (k₁*b₁) => Fin.val i / b₂)
local notation "shuffle" => scalarShuffle k₁ b₁
local instance : NormedSpace ℝ (HorizontalModel rblock lblock shuffle) :=
  Submodule.normedSpace _
local instance : ChartedSpace (HorizontalModel rblock lblock shuffle)
    (MatrixOrbit rblock lblock (permMatrix shuffle)) :=
  overlapChartedSpace rblock lblock shuffle
local instance : IsManifold (𝓘(ℝ, HorizontalModel rblock lblock shuffle)) ⊤
    (MatrixOrbit rblock lblock (permMatrix shuffle)) :=
  overlapIsManifold rblock lblock shuffle

end FixedDimension

section RegularBlocks
variable {n : ℕ} (b₁ k₁ b₂ k₂ : ℕ) (hN₁ : n = k₁*b₁)
local notation "rblock" => (fun i : Fin n => Fin.val i / b₁)
local notation "lblock" => (fun i : Fin n => Fin.val i / b₂)
local notation "shuffle" => scalarShuffleOfSize hN₁
local instance : NormedSpace ℝ (HorizontalModel rblock lblock shuffle) :=
  Submodule.normedSpace _
local instance : ChartedSpace (HorizontalModel rblock lblock shuffle)
    (MatrixOrbit rblock lblock (permMatrix shuffle)) :=
  overlapChartedSpace rblock lblock shuffle
local instance : IsManifold (𝓘(ℝ, HorizontalModel rblock lblock shuffle)) ⊤
    (MatrixOrbit rblock lblock (permMatrix shuffle)) :=
  overlapIsManifold rblock lblock shuffle

end RegularBlocks
end GS.Geodesics
