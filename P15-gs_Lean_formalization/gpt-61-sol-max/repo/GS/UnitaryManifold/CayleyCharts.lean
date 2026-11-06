
import GS.UnitaryManifold.CayleySmooth
import GS.UnitaryManifold.BlockGroup
import Mathlib.Topology.OpenPartialHomeomorph.Basic



/-!
# Explicit open charts on the existing `GS.UnitaryManifold.BlockU`

No topology is transferred to BlockU. Both sets below use the original subtype
topology. The coordinate target is an OPEN subset of a finite-dimensional real
vector space, not the variety defined by unitarity equations.

The atlas ingredients are given by actual `Homeomorph`s and `ContDiffAt`
theorems. The mathlib ChartedSpace/IsManifold structures built from these charts are
installed in `GS.UnitaryManifold.CayleyAtlas`.

All constructions use the original complex matrix topology and real calculus.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS.UnitaryGeometry
namespace GS.UnitaryManifold
variable  {block : Fin n → ℕ}

variable (Q U : BlockU block)

def chartSource : Set (BlockU block) :=
  {U | admissible (Q.valᴴ * U.val)}

variable (x : Model block)

variable (X : CMat n)

/-- Defined on the ambient matrix space. On the chart source the projection
is the identity on its input; this extension makes smoothness unambiguous. -/
def chartMap  : Model block :=
  modelProjection block (cayley (Q.valᴴ * X))

/-- Reconstruction is an actual rational matrix formula. -/
def chartInv  : CMat n :=
  Q.val * cayley x.val

theorem chartSource_open : IsOpen (chartSource Q) :=
  admissible_open.preimage
    (continuous_matrix_product continuous_const continuous_subtype_val)



@[simp] theorem base_mem_chartSource : Q ∈ chartSource Q := by
  change admissible (Q.valᴴ * Q.val)
  rw [Q.property.2.1]
  exact admissible_one

/-- This membership calculation, not an assumption of a tangent structure,
justifies removing modelProjection in chart identities. -/
theorem centered_cayley_mem_model (hU : U ∈ chartSource Q) :
    cayley (Q.valᴴ * U.val) ∈ modelSpace block := ⟨cayley_supported block _ (Q.property.1.conjTranspose.mul U.property.1) hU,
    cayley_isSkew _ (Q.property.2.conjTranspose.mul U.property.2) hU⟩

theorem chartMap_val (hU : U ∈ chartSource Q) :
    (chartMap Q U.val).val = cayley (Q.valᴴ * U.val) :=
  modelProjection_val_of_mem block _ (centered_cayley_mem_model Q U hU)

theorem chartInv_supported  : CSupported block (chartInv Q x) :=
  Q.property.1.mul (cayley_supported block x.val x.property.1 (admissible_model x))

theorem chartInv_unitary  : Unitary (chartInv Q x) :=
  Q.property.2.mul (cayley_unitary x.val x.property.2 (admissible_model x))



theorem centered_chartInv  :
    Q.valᴴ * chartInv Q x = cayley x.val := by
  simp only [chartInv, ← Matrix.mul_assoc, Q.property.2.1, Matrix.one_mul]



theorem chartMap_chartInv  : chartMap Q (chartInv Q x) = x := by simp_all [cayley_involutive,centered_chartInv,chartMap,admissible_model,modelProjection_inclusion]

theorem chartInv_chartMap (hU : U ∈ chartSource Q) :
    chartInv Q (chartMap Q U.val) = U.val := by
  unfold chartInv
  rw [chartMap_val Q U hU, cayley_involutive _ hU]
  simp only [← Matrix.mul_assoc, Q.property.2.2, Matrix.one_mul]

@[simp] theorem chartInv_zero : chartInv Q 0 = Q.val := by
  simp [chartInv]

@[simp] theorem chartMap_base : chartMap Q Q.val = 0 := by
  simp [chartMap, Q.property.2.1]

/-- Smoothness is in an open ambient matrix neighbourhood of the point. -/
theorem chartMap_smooth_at 
    (hX : admissible (Q.valᴴ * X)) : ContDiffAt ℝ ⊤ (chartMap Q) X := (modelProjection block).contDiff.contDiffAt.comp X
    (smooth_cayley_comp_at (smooth_mul_at contDiffAt_const contDiffAt_id) hX)

/-- Reconstruction is smooth on the entire skew-Hermitian coordinate space. -/
theorem chartInv_smooth : ContDiff ℝ ⊤ (chartInv Q) :=
  contDiff_iff_contDiffAt.mpr fun x =>
    smooth_mul_at contDiffAt_const
      (smooth_cayley_comp_at (modelInclusion block).contDiff.contDiffAt (admissible_model x))

/-- Total reconstruction; skew-Hermitian parameters need no domain restriction. -/
def blockChartInverse  : BlockU block :=
  ⟨chartInv Q x, chartInv_supported Q x,
    chartInv_unitary Q x⟩



theorem continuous_blockChartInverse :
    Continuous (blockChartInverse Q) := (chartInv_smooth Q).continuous.subtype_mk _

/-- A genuine Cayley partial homeomorphism in the inherited matrix topology. -/
def blockPartialChart :
    OpenPartialHomeomorph (BlockU block) (Model block) where
  toFun U := chartMap Q U.val
  invFun := blockChartInverse Q
  source := chartSource Q
  target := Set.univ
  map_source' _ _ := Set.mem_univ _
  map_target' x hx := by
    change admissible (Q.valᴴ * chartInv Q x)
    rw [centered_chartInv]
    exact admissible_cayley x.val (admissible_model x)
  left_inv' U hU := by
    apply Subtype.ext
    exact chartInv_chartMap Q U hU
  right_inv' x hx := chartMap_chartInv Q x
  open_source := chartSource_open Q
  open_target := isOpen_univ
  continuousOn_toFun := by
    intro U hU
    exact ((chartMap_smooth_at Q U.val hU).continuousAt.comp
      continuous_subtype_val.continuousAt).continuousWithinAt
  continuousOn_invFun := (continuous_blockChartInverse Q).continuousOn





end GS.UnitaryManifold
