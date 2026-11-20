module

public import RequestProject.CoreSignedCollapse
public import RequestProject.GenerationStepFinsupp
public import RequestProject.BlockFamilyBlockwiseFinsupp
public import RequestProject.ExponentCorrection

@[expose] public section

/-! Core collapse and Hurewicz reflection for arbitrary cell sets.  Only the
individual chains are finitely supported.  Core H2 vanishing is expressed by
injectivity of the genuine finitely supported exponent-sum map.
Pending Lean verification; no finiteness of the core or family is assumed. -/

noncomputable section
open scoped Classical

namespace FiniteChains

open BlockFamily

variable {A B M J : Type} [DecidableEq A] [DecidableEq B]

theorem expMatrix_augmentation (ρ : J → FreeGroup A)
    (v : J →₀ MonoidAlgebra ℤ _) :
    expMatrix ρ (v.mapRange (augPres ρ) (map_zero _)) =
      (coverSecondBoundary _ ρ v).mapRange (augPres ρ) (map_zero _) := by
  have hadd {I : Type} (x y : I →₀ MonoidAlgebra ℤ _) :
      (x + y).mapRange (augPres ρ) (map_zero _) =
        x.mapRange (augPres ρ) (map_zero _) + y.mapRange (augPres ρ) (map_zero _) := by
    ext i : 1
    exact map_add (augPres ρ) _ _
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp_all
  | single j a =>
      simp only [Finsupp.mapRange_single, expMatrix, coverSecondBoundary,
        Finsupp.linearCombination_single]
      ext i : 1
      change augPres ρ a * expVec _ i =
        augPres ρ (a * foxMatrixPres ρ i j)
      rw [map_mul, augPres_foxMatrixPres, expVec_apply]
      rfl

variable (core : M → FreeGroup A) (extra : J → FreeGroup (A ⊕ B))

/-- Core rows of a supported chain on retained core cells are unchanged. -/
theorem corePres_expMatrix_retained (c : M →₀ ℤ) (a : A) :
    expMatrix (corePres core extra) (Finsupp.mapDomain Sum.inl c) (Sum.inl a) =
      expMatrix core c a := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [Finsupp.mapDomain_add, map_add, Finsupp.add_apply, hc, hd]
  | single m n =>
      simp [Finsupp.mapDomain_single, expMatrix, Finsupp.linearCombination_single, Finsupp.smul_apply, smul_eq_mul, expVec_apply, expSum_map_inl]

section

variable (hcore : Function.Injective (expMatrix core))
include hcore

/-- Injectivity on supported core chains reflects vanishing when the extra
coordinates vanish.  This is the actual H2 injection used by terminal B3. -/
theorem corePres_expMatrix_kernel_reflect
    (c : (M ⊕ J) →₀ ℤ) (hc : expMatrix (corePres core extra) c = 0)
    (hextra : ∀ j, c (Sum.inr j) = 0) : c = 0 := by
  let d := c.comapDomain Sum.inl Sum.inl_injective.injOn
  have he : Finsupp.mapDomain Sum.inl d = c := by
    apply Finsupp.mapDomain_comapDomain Sum.inl Sum.inl_injective c
    rintro (m | j) h <;> simp_all
  have hd : expMatrix core d = 0 := by
    ext a
    rw [← corePres_expMatrix_retained core extra d a, he, hc]
    rfl
  simp_all

theorem corePres_fsAugmentation_reflect
    (v : (M ⊕ J) →₀ MonoidAlgebra ℤ _)
    (hv : FSIsFoxCycle _ v)
    (hextra : ∀ j, augPres _ (v (Sum.inr j)) = 0) :
    ∀ j, augPres (corePres core extra) (v j) = 0 := by
  let c := v.mapRange (augPres (corePres core extra)) (map_zero _)
  have hc : expMatrix (corePres core extra) c = 0 := by
    rw [expMatrix_augmentation]
    rw [hv, Finsupp.mapRange_zero]
  intro j
  exact congrArg (fun c : (M ⊕ J) →₀ ℤ => c j) (corePres_expMatrix_kernel_reflect core extra hcore c hc hextra)

end

namespace CoreSignedCollapse

variable (core : M → FreeGroup A) (extra : J → FreeGroup (A ⊕ B))
  (target : J → FreeGroup B) (rev : J → Bool)
  (hword : ∀ j, dropCore (extra j) = if rev j then (target j)⁻¹ else target j)

variable (v : (M ⊕ J) →₀ MonoidAlgebra ℤ (PresGroup (corePres core extra)))

/-- The supported signed collapse has support contained in the extra part
of the original chain's support. -/
def cellsFS :=
  Finsupp.onFinset (v.comapDomain Sum.inr Sum.inr_injective.injOn).support
    (fun j => if rev j then -coefficientMap core extra target rev hword (v (Sum.inr j))
      else coefficientMap core extra target rev hword (v (Sum.inr j))) (by
    aesop)

omit [DecidableEq A] [DecidableEq B] in
@[simp] theorem cellsFS_apply (j : J) :
    cellsFS core extra target rev hword v j =
      if rev j then -coefficientMap core extra target rev hword (v (Sum.inr j))
        else coefficientMap core extra target rev hword (v (Sum.inr j)) := rfl

omit [DecidableEq A] [DecidableEq B] in
@[simp] theorem cellsFS_zero : cellsFS core extra target rev hword 0 = 0 := by
  ext j : 1
  simp [cellsFS_apply]

omit [DecidableEq A] [DecidableEq B] in
theorem cellsFS_add (v w : (M ⊕ J) →₀ MonoidAlgebra ℤ _) :
    cellsFS core extra target rev hword (v + w) =
      cellsFS core extra target rev hword v + cellsFS core extra target rev hword w := by
  ext j : 1
  cases h : rev j <;> simp [cellsFS_apply, h, map_add, add_comm]

omit [DecidableEq A] [DecidableEq B] in
@[simp] theorem cellsFS_single_core (m : M)
    (a : MonoidAlgebra ℤ _) :
    cellsFS core extra target rev hword (Finsupp.single (Sum.inl m) a) = 0 := by
  ext j : 1
  simp [cellsFS_apply]

omit [DecidableEq A] [DecidableEq B] in
@[simp] theorem cellsFS_single_extra (j : J)
    (a : MonoidAlgebra ℤ _) :
    cellsFS core extra target rev hword (Finsupp.single (Sum.inr j) a) =
      Finsupp.single j (if rev j then -coefficientMap core extra target rev hword a
        else coefficientMap core extra target rev hword a) := by
  ext k : 1
  by_cases h : j = k
  · subst k
    simp [cellsFS_apply]
  · simp [cellsFS_apply, Ne.symm h]

variable (v : (M ⊕ J) →₀ MonoidAlgebra ℤ (PresGroup (corePres core extra)))

theorem cellsFS_boundary_apply (b : B) :
    coverSecondBoundary _ target (cellsFS core extra target rev hword v) b =
      coefficientMap core extra target rev hword
        (coverSecondBoundary (relSub (corePres core extra)) (corePres core extra) v
          (Sum.inr b)) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [cellsFS_add, map_add, Finsupp.add_apply, hv, hw]
  | single j a =>
      cases j with
      | inl m =>
          simp_all [cellsFS_single_core, fsCoverSecondBoundary_apply, matrix_core]
      | inr j =>
          simp_all [cellsFS_single_extra, fsCoverSecondBoundary_apply, matrix_extra]

theorem cellsFS_cycle
    (hv : FSIsFoxCycle _ v) :
    FSIsFoxCycle target (cellsFS core extra target rev hword v) := by
  ext b : 1; rw [cellsFS_boundary_apply, hv, Finsupp.zero_apply, map_zero]; rfl

variable (hcore : Function.Injective (expMatrix core))
include hcore

theorem hurewiczFS_reflect
    (v : (M ⊕ J) →₀ MonoidAlgebra ℤ _)
    (hv : FSIsFoxCycle _ v)
    (hz : ∀ j, augPres target (cellsFS core extra target rev hword v j) = 0) :
    ∀ j, augPres _ (v j) = 0 := by
  apply corePres_fsAugmentation_reflect core extra hcore v hv
  intro j
  have ha : augPres target
      (coefficientMap core extra target rev hword (v (Sum.inr j))) =
      augPres _ _ :=
    augQ_mapDomain _ _
  cases he : rev j <;> simpa [cellsFS_apply, he, map_neg, ha] using (hz j)

include hword in
theorem fsIsCockcroft
    (htarget : FSIsCockcroft target) : FSIsCockcroft (corePres core extra) := by
  intro v hv
  exact hurewiczFS_reflect core extra target rev hword hcore v hv
    (htarget _ (cellsFS_cycle core extra target rev hword v hv))

end CoreSignedCollapse
end FiniteChains
