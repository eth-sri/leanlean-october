module

public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Matrix
public import GS.Unitary.Support
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.ProperSpace.Real

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open Matrix GS.UnitaryGeometry
open scoped BigOperators
namespace GS.UnitaryManifold
variable {𝕂 : Type} [RCLike 𝕂] {n : ℕ}

abbrev KBlockU (𝕂 : Type) [RCLike 𝕂] {n : ℕ} (block : Fin n → ℕ) :=
  {A : Matrix (Fin n) (Fin n) 𝕂 // KSSupported block A ∧ GS.KUnitary A}

abbrev BlockU {n : ℕ} (block : Fin n → ℕ) := KBlockU ℂ block

instance blockUGroup (block : Fin n → ℕ) : Group (KBlockU 𝕂 block) where
  one := ⟨1, KSSupported.one, GS.KUnitary.one⟩
  mul A B := ⟨A.val * B.val, A.property.1.mul B.property.1, A.property.2.mul B.property.2⟩
  inv A := ⟨A.valᴴ, A.property.1.conjTranspose, A.property.2.conjTranspose⟩
  mul_assoc A B C := Subtype.ext (Matrix.mul_assoc A.val B.val C.val)
  one_mul A := Subtype.ext (Matrix.one_mul A.val)
  mul_one A := Subtype.ext (Matrix.mul_one A.val)
  inv_mul_cancel A := Subtype.ext A.property.2.1

@[simp] theorem blockU_one_val (block : Fin n → ℕ) :
    ((1 : KBlockU 𝕂 block) : Matrix (Fin n) (Fin n) 𝕂) = 1 := rfl

theorem continuous_matrix_product {X : Type*} [TopologicalSpace X]
    {A B : X → Matrix (Fin n) (Fin n) 𝕂} (hA : Continuous A) (hB : Continuous B) :
    Continuous (fun x => A x * B x) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.mul_apply]
  exact continuous_finsetSum _ fun k _ =>
    (((continuous_apply k).comp ((continuous_apply i).comp hA)).mul
      ((continuous_apply j).comp ((continuous_apply k).comp hB)))

theorem continuous_matrix_conjTranspose {X : Type*} [TopologicalSpace X]
    {A : X → Matrix (Fin n) (Fin n) 𝕂} (hA : Continuous A) :
    Continuous (fun x => (A x)ᴴ) :=
  continuous_pi fun i => continuous_pi fun j =>
    ((continuous_apply i).comp ((continuous_apply j).comp hA)).star

instance blockUContinuousMul (block : Fin n → ℕ) : ContinuousMul (KBlockU 𝕂 block) where
  continuous_mul := Continuous.subtype_mk
    (continuous_matrix_product (continuous_subtype_val.comp continuous_fst)
      (continuous_subtype_val.comp continuous_snd)) _

instance blockUContinuousInv (block : Fin n → ℕ) : ContinuousInv (KBlockU 𝕂 block) where
  continuous_inv := Continuous.subtype_mk
    (continuous_matrix_conjTranspose continuous_subtype_val) _

instance blockUTopologicalGroup (block : Fin n → ℕ) : IsTopologicalGroup (KBlockU 𝕂 block) where

theorem closed_supported (block : Fin n → ℕ) :
    IsClosed {A : Matrix (Fin n) (Fin n) 𝕂 | KSSupported block A} := by
  simp only [KSSupported, Set.setOf_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq ((continuous_apply j).comp (continuous_apply i)) continuous_const

theorem closed_unitary : IsClosed {A : Matrix (Fin n) (Fin n) 𝕂 | GS.KUnitary A} := by
  change IsClosed ({A : Matrix (Fin n) (Fin n) 𝕂 | Aᴴ * A = 1} ∩ {A | A * Aᴴ = 1})
  exact (isClosed_eq (continuous_matrix_product
      (continuous_matrix_conjTranspose continuous_id) continuous_id) continuous_const).inter
    (isClosed_eq (continuous_matrix_product continuous_id
      (continuous_matrix_conjTranspose continuous_id)) continuous_const)

theorem unitary_entry_bound {A : Matrix (Fin n) (Fin n) 𝕂} (hA : GS.KUnitary A) (i j : Fin n) :
    ‖A i j‖ ≤ 1 := by
  have hg := congrArg RCLike.re (congrFun (congrFun hA.1 j) j)
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, ↓reduceIte,
    RCLike.one_re, map_sum] at hg
  have hs : ‖A i j‖ ^ 2 ≤ 1 := by
    rw [← hg]
    have hterm (k : Fin n) : RCLike.re (star (A k j) * A k j) = ‖A k j‖ ^ 2 := by
      rw [RCLike.star_def, RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]
    simp_rw [hterm]
    exact Finset.single_le_sum (fun k _ => sq_nonneg ‖A k j‖) (Finset.mem_univ i)
  nlinarith [norm_nonneg (A i j)]

theorem compact_blockU_set (block : Fin n → ℕ) :
    IsCompact {A : Matrix (Fin n) (Fin n) 𝕂 | KSSupported block A ∧ GS.KUnitary A} := by
  have : ProperSpace 𝕂 := FiniteDimensional.proper ℝ 𝕂
  have hb : IsCompact {A : Matrix (Fin n) (Fin n) 𝕂 | ∀ i j, A i j ∈ Metric.closedBall (0 : 𝕂) 1} :=
    isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => isCompact_closedBall (0 : 𝕂) 1
  exact hb.of_isClosed_subset ((closed_supported block).inter closed_unitary) fun A hA i j => by
    simpa [Metric.mem_closedBall, dist_zero_right] using unitary_entry_bound hA.2 i j

instance blockUCompactSpace (block : Fin n → ℕ) : CompactSpace (KBlockU 𝕂 block) :=
  isCompact_iff_compactSpace.mp (compact_blockU_set block)

abbrev KFactorGroup (𝕂 : Type) [RCLike 𝕂] {n : ℕ} (block₁ block₂ : Fin n → ℕ) :=
  KBlockU 𝕂 block₂ × KBlockU 𝕂 block₁

abbrev FactorGroup {n : ℕ} (block₁ block₂ : Fin n → ℕ) := KFactorGroup ℂ block₁ block₂

end GS.UnitaryManifold
