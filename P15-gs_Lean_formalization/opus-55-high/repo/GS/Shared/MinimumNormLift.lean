module

public import GS.Shared.Projection
public import Mathlib.Analysis.InnerProductSpace.ProdL2

@[expose] public section


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
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS InnerProductSpace
namespace GS.Shared
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} {right left : Pattern 𝕜 n}

/-- The physical, multiplicity-weighted pairing; not the chart-coordinate norm. -/
def generatorInner (v w : PairGenerator right left) : ℝ :=
  frob v.1.val w.1.val + frob v.2.val w.2.val

def generatorEnergy (v : PairGenerator right left) : ℝ := generatorInner v v


section
variable (u v w : PairGenerator right left)
theorem generatorInner_add_left :
    generatorInner (u + v) w = generatorInner u w + generatorInner v w := by
  simp only [generatorInner, Prod.fst_add, Prod.snd_add, Submodule.coe_add,
    frob_add_left]
  ring

theorem generatorInner_sub_left :
    generatorInner (u - v) w = generatorInner u w - generatorInner v w := by
  change frob (u.1.val - v.1.val) w.1.val +
    frob (u.2.val - v.2.val) w.2.val = _
  rw [frob_sub_left, frob_sub_left]
  unfold generatorInner
  ring

end

theorem generatorInner_smul_left (a : ℝ) (v w : PairGenerator right left) :
    generatorInner (a • v) w = a * generatorInner v w := by
  change frob (a • v.1.val) w.1.val + frob (a • v.2.val) w.2.val = _
  rw [frob_smul_left, frob_smul_left]
  unfold generatorInner
  ring



@[simp] theorem generatorEnergy_eq_zero_iff (v : PairGenerator right left) :
    generatorEnergy v = 0 ↔ v = 0 :=
by
  constructor
  · intro h
    change frob v.1.val v.1.val + frob v.2.val v.2.val = 0 at h
    have h₁ : frob v.1.val v.1.val = 0 := by
      linarith [frob_self_nonneg v.1.val, frob_self_nonneg v.2.val]
    have h₂ : frob v.2.val v.2.val = 0 := by
      linarith [frob_self_nonneg v.1.val, frob_self_nonneg v.2.val]
    apply Prod.ext <;> apply Subtype.ext
    · exact (frob_self_eq_zero _).mp h₁
    · exact (frob_self_eq_zero _).mp h₂
  · rintro rfl
    simp [generatorEnergy, generatorInner, frob]

abbrev GeneratorHilbert (𝕜 : Type*) [RCLike 𝕜] (n : ℕ) := WithLp 2 (W 𝕜 n × W 𝕜 n)

/-- Linear encoding preserving the physical pairing, with no change to the
existing topology or norm instances on shared generators. -/
def generatorEncoding (right left : Pattern 𝕜 n) :
    PairGenerator right left →ₗ[ℝ] GeneratorHilbert 𝕜 n :=
  (WithLp.linearEquiv 2 ℝ (W 𝕜 n × W 𝕜 n)).symm.toLinearMap.comp
    ((((sharedSkewSpace left.size left.label).subtype.comp (LinearMap.fst ℝ _ _)).prod
      ((sharedSkewSpace right.size right.label).subtype.comp (LinearMap.snd ℝ _ _)) :
        PairGenerator right left →ₗ[ℝ] W 𝕜 n × W 𝕜 n))

theorem generatorEncoding_inner (v w : PairGenerator right left) :
    ⟪generatorEncoding right left v, generatorEncoding right left w⟫_ℝ =
      generatorInner v w := rfl

def encodedPointKernel (X : 𝕄) : Submodule ℝ (GeneratorHilbert 𝕜 n) :=
  (pointMap right left X).ker.map (generatorEncoding right left)

section
variable (X : 𝕄) (v : PairGenerator right left)
theorem exists_encoded_kernel_projection :
    ∃ k : PairGenerator right left,
      pointMap right left X k = 0 ∧ generatorEncoding right left k =
        ((encodedPointKernel (right := right) (left := left) X).orthogonalProjection
          (generatorEncoding right left v) : GeneratorHilbert 𝕜 n) :=
  ((encodedPointKernel (right := right) (left := left) X).orthogonalProjection
    (generatorEncoding right left v)).property

def kernelPart :
    PairGenerator right left := Classical.choose (exists_encoded_kernel_projection X v)

private theorem kernelPart_mem :
    pointMap right left X (kernelPart X v) = 0 :=
  (Classical.choose_spec (exists_encoded_kernel_projection X v)).1

private theorem encode_kernelPart :
    generatorEncoding right left (kernelPart X v) =
      ((encodedPointKernel (right := right) (left := left) X).orthogonalProjection
        (generatorEncoding right left v) : GeneratorHilbert 𝕜 n) :=
  (Classical.choose_spec (exists_encoded_kernel_projection X v)).2

/-- Orthogonality to the full shared synthesis kernel in the real physical metric. -/
def IsHorizontal : Prop :=
  ∀ k : PairGenerator right left, pointMap right left X k = 0 → generatorInner v k = 0

private theorem sub_kernelPart_horizontal :
    IsHorizontal X (v - kernelPart X v) := by
  intro k hk
  have hk' : generatorEncoding right left k ∈
      encodedPointKernel (right := right) (left := left) X := ⟨k, hk, rfl⟩
  have h := Submodule.orthogonalProjectionFn_inner_eq_zero
    (K := encodedPointKernel (right := right) (left := left) X)
    (generatorEncoding right left v) (generatorEncoding right left k) hk'
  rw [← generatorEncoding_inner, map_sub, encode_kernelPart]
  exact h

end

theorem horizontal_lift_unique (X : 𝕄) (v w : PairGenerator right left)
    (hv : IsHorizontal X v) (hw : IsHorizontal X w)
    (h : pointMap right left X v = pointMap right left X w) : v = w := by
  have hk : pointMap right left X (v - w) = 0 := by grind
  apply sub_eq_zero.mp
  apply (generatorEnergy_eq_zero_iff (v - w)).mp
  change generatorInner (v - w) (v - w) = 0
  rw [generatorInner_sub_left, hv _ hk, hw _ hk, sub_self]

/-- Existence is derived from finite-dimensional orthogonal projection. -/
theorem exists_horizontal_lift (X Z : 𝕄) :
    ∃ v : PairGenerator right left,
      pointMap right left X v = pointProjection right left X Z ∧ IsHorizontal X v := by
  obtain ⟨v, hv⟩ := pointProjection_mem (right := right) (left := left) X Z
  refine ⟨v - kernelPart X v, ?_, sub_kernelPart_horizontal X v⟩
  rw [map_sub, kernelPart_mem, sub_zero]
  grind

def selectedLift (right left : Pattern 𝕜 n) (X Z : 𝕄) : PairGenerator right left :=
  Classical.choose (exists_horizontal_lift (right := right) (left := left) X Z)

section
variable (X Z : 𝕄)
private theorem selectedLift_synthesis :
    pointMap right left X (selectedLift right left X Z) = pointProjection right left X Z :=
  (Classical.choose_spec (exists_horizontal_lift (right := right) (left := left) X Z)).1

private theorem selectedLift_horizontal :
    IsHorizontal X (selectedLift right left X Z) :=
  (Classical.choose_spec (exists_horizontal_lift (right := right) (left := left) X Z)).2

end

/-- The canonical minimum-physical-norm lift of the projected ambient vector.
It is linear and continuous in Z; it is NOT asserted smooth across arbitrary
ambient rank changes in X. -/
def minimumNormLift (right left : Pattern 𝕜 n) (X : 𝕄) :
    𝕄 →L[ℝ] PairGenerator right left :=
  ({ toFun := selectedLift right left X
     map_add' := by
       intro Z W
       apply horizontal_lift_unique X
       · exact selectedLift_horizontal X (Z + W)
       · intro k hk
         rw [generatorInner_add_left, selectedLift_horizontal X Z k hk,
           selectedLift_horizontal X W k hk, add_zero]
       · simp only [map_add, selectedLift_synthesis]
     map_smul' := by
       intro a Z
       apply horizontal_lift_unique X
       · exact selectedLift_horizontal X (a • Z)
       · intro k hk
         rw [generatorInner_smul_left, selectedLift_horizontal X Z k hk, mul_zero]
       · simp only [map_smul, selectedLift_synthesis, RingHom.id_apply]
   } : 𝕄 →ₗ[ℝ] PairGenerator right left).toContinuousLinearMap

section
variable (X Z : 𝕄)
theorem minimumNormLift_synthesis :
    pointMap right left X (minimumNormLift right left X Z) =
      pointProjection right left X Z := selectedLift_synthesis X Z

theorem minimumNormLift_horizontal :
    IsHorizontal X (minimumNormLift right left X Z) := selectedLift_horizontal X Z

theorem minimumNormLift_unique (v : PairGenerator right left)
    (hv : pointMap right left X v = pointProjection right left X Z)
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

end

end GS.Shared
