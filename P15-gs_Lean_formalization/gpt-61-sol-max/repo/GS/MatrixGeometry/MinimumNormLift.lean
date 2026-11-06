import GS.MatrixGeometry.Base

import GS.MatrixGeometry.Projection
import Mathlib.Analysis.InnerProductSpace.ProdL2



/-!
# The canonical minimum-physical-norm lift of a shared tangent

The metric on generators is the sum of the Frobenius norms of the two
expanded physical matrices. Repeated blocks therefore carry their actual
multiplicities. No inner product is installed on the entrywise matrix norm.
Instead the kernel projection is constructed in a genuine L2 product of
Frobenius coordinate spaces. Subtracting that projection gives the unique
horizontal lift. All matrices X are allowed; smooth dependence on X is proved
separately on each fixed shared orbit.
-/


noncomputable section
open GS.MatrixBase InnerProductSpace
namespace GS.MatrixGeometry
variable {𝕜 : Type} [RCLike 𝕜]
variable  {right left : Pattern 𝕜 n}
variable (X Z : KMat 𝕜 n)
variable (v : PairGenerator right left)


/-- The physical, multiplicity-weighted pairing; not the chart-coordinate norm. -/
def generatorInner (w : PairGenerator right left) : ℝ :=
  cFrobInner v.1.val w.1.val + cFrobInner v.2.val w.2.val

def generatorEnergy : ℝ := generatorInner v v





@[simp] theorem generatorEnergy_eq_zero_iff :
    generatorEnergy v = 0 ↔ v = 0 :=
by
  change cFrobSq v.1.val + cFrobSq v.2.val = 0 ↔ v = 0
  rw [add_eq_zero_iff_of_nonneg (cFrobSq_nonneg _) (cFrobSq_nonneg _),
    cFrobSq_eq_zero_iff,cFrobSq_eq_zero_iff]
  simp only [Prod.ext_iff,Subtype.ext_iff,Prod.fst_zero,Prod.snd_zero,Submodule.coe_zero]

abbrev GeneratorHilbert (𝕜 : Type) [RCLike 𝕜] (n : ℕ) := WithLp 2 (CFrobCoordinates 𝕜 n × CFrobCoordinates 𝕜 n)

/-- Linear encoding preserving the physical pairing, with no change to the
existing topology or norm instances on shared generators. -/
def generatorEncoding (right left : Pattern 𝕜 n) :
    PairGenerator right left →ₗ[ℝ] GeneratorHilbert 𝕜 n :=
  let L := (encodeCFrob.comp (sharedSkewSpace left.size left.label).subtype).comp
    (LinearMap.fst ℝ (Generator left) (Generator right))
  let R := (encodeCFrob.comp (sharedSkewSpace right.size right.label).subtype).comp
    (LinearMap.snd ℝ (Generator left) (Generator right))
  (WithLp.linearEquiv 2 ℝ (CFrobCoordinates 𝕜 n × CFrobCoordinates 𝕜 n)).symm.toLinearMap.comp
    (L.prod R)

theorem generatorEncoding_inner (w : PairGenerator right left) :
    ⟪generatorEncoding right left v, generatorEncoding right left w⟫_ℝ =
      generatorInner v w := by
  change ⟪encodeCFrob v.1.val, encodeCFrob w.1.val⟫_ℝ +
    ⟪encodeCFrob v.2.val, encodeCFrob w.2.val⟫_ℝ = _
  rw [encodeCFrob_inner, encodeCFrob_inner]
  rfl

theorem generatorInner_sub_left (u v w : PairGenerator right left) :
    generatorInner (u - v) w = generatorInner u w - generatorInner v w := by
  simp only [← generatorEncoding_inner, map_sub, inner_sub_left]

def encodedPointKernel : Submodule ℝ (GeneratorHilbert 𝕜 n) :=
  (pointMap right left X).ker.map (generatorEncoding right left)

private def projectedGenerator :=
  (encodedPointKernel (right := right) (left := left) X).orthogonalProjection
    (generatorEncoding right left v)

def kernelPart : PairGenerator right left := (projectedGenerator X v).property.choose

private theorem kernelPart_mem : pointMap right left X (kernelPart X v) = 0 :=
  (projectedGenerator X v).property.choose_spec.1

private theorem encode_kernelPart :
    generatorEncoding right left (kernelPart X v) = (projectedGenerator X v : GeneratorHilbert 𝕜 n) :=
  (projectedGenerator X v).property.choose_spec.2

/-- Orthogonality to the full shared synthesis kernel in the real physical metric. -/
def IsHorizontal : Prop :=
  ∀ k : PairGenerator right left, pointMap right left X k = 0 → generatorInner v k = 0

private theorem sub_kernelPart_horizontal :
    IsHorizontal X (v - kernelPart X v) := by
  intro k hk
  have hk' : generatorEncoding right left k ∈
      encodedPointKernel   X := ⟨k, hk, rfl⟩
  have h := Submodule.orthogonalProjectionFn_inner_eq_zero
    (K := encodedPointKernel   X)
    (generatorEncoding right left v) (generatorEncoding right left k) hk'
  rw [Submodule.starProjection_apply] at h
  rw [← generatorEncoding_inner, map_sub, encode_kernelPart]
  exact h

theorem horizontal_lift_unique (w : PairGenerator right left) (hv : IsHorizontal X v) (hw : IsHorizontal X w)
    (h : pointMap right left X v = pointMap right left X w) : v = w := by
  have hk : pointMap right left X (v - w) = 0 := by aesop
  apply sub_eq_zero.mp
  apply (generatorEnergy_eq_zero_iff (v - w)).mp
  change generatorInner (v - w) (v - w) = 0
  rw [generatorInner_sub_left, hv _ hk, hw _ hk, sub_self]

/-- Existence is derived from finite-dimensional orthogonal projection. -/
theorem exists_horizontal_lift :
    ∃ v : PairGenerator right left,
      pointMap right left X v = pointProjection right left X Z ∧ IsHorizontal X v := by
  obtain ⟨v, hv⟩ := pointProjection_mem   X Z
  refine ⟨v - kernelPart X v, ?_, sub_kernelPart_horizontal X v⟩
  rw [map_sub, kernelPart_mem, sub_zero]
  exact hv

def selectedLift (right left : Pattern 𝕜 n) (X Z : KMat 𝕜 n) := Classical.choose (exists_horizontal_lift (right := right) (left := left) X Z)

private theorem selectedLift_synthesis :
    pointMap right left X (selectedLift right left X Z) = pointProjection right left X Z :=
  (Classical.choose_spec (exists_horizontal_lift   X Z)).1

private theorem selectedLift_horizontal :
    IsHorizontal X (selectedLift right left X Z) :=
  (Classical.choose_spec (exists_horizontal_lift   X Z)).2

/-- The canonical minimum-physical-norm lift of the projected ambient vector.
It is linear and continuous in Z; it is NOT asserted smooth across arbitrary
ambient rank changes in X. -/
def minimumNormLift (right left : Pattern 𝕜 n) (X : KMat 𝕜 n) :
    KMat 𝕜 n →L[ℝ] PairGenerator right left :=
  ({ toFun := selectedLift right left X
     map_add' := by
       intro Z W
       apply horizontal_lift_unique X
       · exact selectedLift_horizontal X (Z + W)
       · intro k hk
         rw [← generatorEncoding_inner, map_add, inner_add_left,
           generatorEncoding_inner, generatorEncoding_inner, selectedLift_horizontal X Z k hk,
           selectedLift_horizontal X W k hk, add_zero]
       · simp only [map_add, selectedLift_synthesis]
     map_smul' := by
       intro a Z
       apply horizontal_lift_unique X
       · exact selectedLift_horizontal X (a • Z)
       · intro k hk
         rw [← generatorEncoding_inner, map_smul, inner_smul_left,
           generatorEncoding_inner, selectedLift_horizontal X Z k hk, mul_zero]
       · simp only [map_smul, selectedLift_synthesis, RingHom.id_apply]
   } : KMat 𝕜 n →ₗ[ℝ] PairGenerator right left).toContinuousLinearMap

theorem minimumNormLift_synthesis :
    pointMap right left X (minimumNormLift right left X Z) =
      pointProjection right left X Z := selectedLift_synthesis X Z

theorem minimumNormLift_horizontal :
    IsHorizontal X (minimumNormLift right left X Z) := selectedLift_horizontal X Z

theorem minimumNormLift_unique (hv : pointMap right left X v = pointProjection right left X Z)
    (hh : IsHorizontal X v) : v = minimumNormLift right left X Z :=
  horizontal_lift_unique X v _ hh (minimumNormLift_horizontal X Z)
    (hv.trans (minimumNormLift_synthesis X Z).symm)

/-- Removing the ambient normal component does not change the selected generators. -/
@[simp] theorem minimumNormLift_projected :
    minimumNormLift right left X (pointProjection right left X Z) =
      minimumNormLift right left X Z := by
  apply minimumNormLift_unique X Z
  · rw [minimumNormLift_synthesis, pointProjection_idempotent]
  · exact minimumNormLift_horizontal X _

end GS.MatrixGeometry
