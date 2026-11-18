module

public import GS.UnitaryManifold.CayleySmooth
public import GS.UnitaryManifold.BlockGroup
public import Mathlib.Topology.OpenPartialHomeomorph.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS.UnitaryGeometry
namespace GS.UnitaryManifold
variable {𝕂 : Type} [RCLike 𝕂] {n : ℕ} {block : Fin n → ℕ}

def kParameterDomain (𝕂 : Type) [RCLike 𝕂] {n : ℕ} (block : Fin n → ℕ) : Set (KModel 𝕂 block) :=
  {x | admissible x.val}

abbrev parameterDomain {n : ℕ} (block : Fin n → ℕ) := kParameterDomain ℂ block

def chartSource (Q : KBlockU 𝕂 block) : Set (KBlockU 𝕂 block) :=
  {U | admissible (Q.valᴴ * U.val)}

def chartMap (Q : KBlockU 𝕂 block) (X : Matrix (Fin n) (Fin n) 𝕂) : KModel 𝕂 block :=
  kModelProjection 𝕂 block (cayley (Q.valᴴ * X))

def chartInv (Q : KBlockU 𝕂 block) (x : KModel 𝕂 block) : Matrix (Fin n) (Fin n) 𝕂 :=
  Q.val * cayley x.val

theorem parameterDomain_open (block : Fin n → ℕ) : IsOpen (kParameterDomain 𝕂 block) :=
  admissible_open.preimage (kModelInclusion 𝕂 block).continuous

theorem chartSource_open (Q : KBlockU 𝕂 block) : IsOpen (chartSource Q) :=
  admissible_open.preimage (continuous_matrix_product continuous_const continuous_subtype_val)

@[simp] theorem base_mem_chartSource (Q : KBlockU 𝕂 block) : Q ∈ chartSource Q := by
  change admissible (Q.valᴴ * Q.val); rw [Q.property.2.1]; exact admissible_one

theorem centered_cayley_mem_model (Q U : KBlockU 𝕂 block) (hU : U ∈ chartSource Q) :
    cayley (Q.valᴴ * U.val) ∈ kModelSpace 𝕂 block :=
  ⟨cayley_supported block _ (Q.property.1.conjTranspose.mul U.property.1) hU,
   cayley_isSkew _ (Q.property.2.conjTranspose.mul U.property.2) hU⟩

theorem chartMap_val (Q U : KBlockU 𝕂 block) (hU : U ∈ chartSource Q) :
    (chartMap Q U.val).val = cayley (Q.valᴴ * U.val) :=
  modelProjection_val_of_mem block _ (centered_cayley_mem_model Q U hU)

theorem chartMap_mem_domain (Q U : KBlockU 𝕂 block) (hU : U ∈ chartSource Q) :
    chartMap Q U.val ∈ kParameterDomain 𝕂 block := by
  change admissible (chartMap Q U.val).val; rw [chartMap_val Q U hU]; exact admissible_cayley _ hU

theorem chartInv_supported (Q : KBlockU 𝕂 block) (x : KModel 𝕂 block)
    (hx : x ∈ kParameterDomain 𝕂 block) : KSSupported block (chartInv Q x) :=
  Q.property.1.mul (cayley_supported block x.val x.property.1 hx)

theorem chartInv_unitary (Q : KBlockU 𝕂 block) (x : KModel 𝕂 block)
    (hx : x ∈ kParameterDomain 𝕂 block) : GS.KUnitary (chartInv Q x) :=
  Q.property.2.mul (cayley_unitary x.val x.property.2 hx)

theorem centered_chartInv (Q : KBlockU 𝕂 block) (x : KModel 𝕂 block) :
    Q.valᴴ * chartInv Q x = cayley x.val := by
  simp only [chartInv, ← Matrix.mul_assoc, Q.property.2.1, Matrix.one_mul]

theorem chartMap_chartInv (Q : KBlockU 𝕂 block) (x : KModel 𝕂 block)
    (hx : x ∈ kParameterDomain 𝕂 block) : chartMap Q (chartInv Q x) = x := by
  unfold chartMap; rw [centered_chartInv, cayley_involutive x.val hx]
  exact modelProjection_inclusion block x

theorem chartInv_chartMap (Q U : KBlockU 𝕂 block) (hU : U ∈ chartSource Q) :
    chartInv Q (chartMap Q U.val) = U.val := by
  unfold chartInv; rw [chartMap_val Q U hU, cayley_involutive _ hU]
  simp only [← Matrix.mul_assoc, Q.property.2.2, Matrix.one_mul]

@[simp] theorem chartInv_zero (Q : KBlockU 𝕂 block) : chartInv Q 0 = Q.val := by simp [chartInv]

@[simp] theorem chartMap_base (Q : KBlockU 𝕂 block) : chartMap Q Q.val = 0 := by
  simp [chartMap, Q.property.2.1]

theorem chartMap_smooth_at (Q : KBlockU 𝕂 block) (X : Matrix (Fin n) (Fin n) 𝕂)
    (hX : admissible (Q.valᴴ * X)) : ContDiffAt ℝ ⊤ (chartMap Q) X :=
  (kModelProjection 𝕂 block).contDiff.contDiffAt.comp X
    (smooth_cayley_comp_at (smooth_mul_at contDiffAt_const contDiffAt_id) hX)

theorem chartInv_smooth_at (Q : KBlockU 𝕂 block) (x : KModel 𝕂 block)
    (hx : x ∈ kParameterDomain 𝕂 block) : ContDiffAt ℝ ⊤ (chartInv Q) x :=
  smooth_mul_at contDiffAt_const
    (smooth_cayley_comp_at (kModelInclusion 𝕂 block).contDiff.contDiffAt hx)

theorem chartInv_smooth (Q : KBlockU 𝕂 block) : ContDiff ℝ ⊤ (chartInv Q) :=
  contDiff_iff_contDiffAt.mpr fun x => chartInv_smooth_at Q x (admissible_model x)

def blockChartInverse (Q : KBlockU 𝕂 block) (x : KModel 𝕂 block) : KBlockU 𝕂 block :=
  ⟨chartInv Q x, chartInv_supported Q x (admissible_model x),
   chartInv_unitary Q x (admissible_model x)⟩

theorem continuous_blockChartInverse (Q : KBlockU 𝕂 block) :
    Continuous (blockChartInverse Q) := (chartInv_smooth Q).continuous.subtype_mk _

def blockPartialChart (Q : KBlockU 𝕂 block) :
    OpenPartialHomeomorph (KBlockU 𝕂 block) (KModel 𝕂 block) where
  toFun U := chartMap Q U.val
  invFun := blockChartInverse Q
  source := chartSource Q
  target := kParameterDomain 𝕂 block
  map_source' U hU := chartMap_mem_domain Q U hU
  map_target' x hx := by
    change admissible (Q.valᴴ * chartInv Q x); rw [centered_chartInv]; exact admissible_cayley x.val hx
  left_inv' U hU := Subtype.ext (chartInv_chartMap Q U hU)
  right_inv' x hx := chartMap_chartInv Q x hx
  open_source := chartSource_open Q
  open_target := parameterDomain_open block
  continuousOn_toFun U hU :=
    ((chartMap_smooth_at Q U.val hU).continuousAt.comp continuous_subtype_val.continuousAt).continuousWithinAt
  continuousOn_invFun := (continuous_blockChartInverse Q).continuousOn

end GS.UnitaryManifold
