module

public import RequestProject.LocalConformalHardySubspace
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# The actual positive Fourier Hilbert basis

The orthogonal complement of the full nonpositive space has the standard
positive-frequency basis. Finite linear combinations in this basis, or
the full standard basis, have genuinely finite Fourier support.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set
open scoped InnerProductSpace

variable {n : ℤ} {b : L2Z}

theorem stdBasisZ_mem_nonpositive (hn : n ≤ 0) :
    stdBasisZ n ∈ nonpositiveFourierSubspace := by
  intro k hk
  have hkn : k ≠ n := by omega
  simp [stdBasisZ_apply, hkn]

theorem nonpositive_orthogonal_coefficient_eq_zero
    (b : nonpositiveFourierSubspaceᗮ) {n : ℤ} (hn : n ≤ 0) :
    (b : L2Z) n = 0 := by
  simpa [stdBasisZ_apply, lp.inner_single_left] using (Submodule.mem_orthogonal _ _).mp b.property (stdBasisZ n)
    (stdBasisZ_mem_nonpositive hn)

theorem stdBasisZ_mem_nonpositive_orthogonal (hn : 0 < n) :
    stdBasisZ n ∈ nonpositiveFourierSubspaceᗮ := by
  have heq : posProj (stdBasisZ n) = stdBasisZ n := by
    apply lp.ext
    funext k
    by_cases hkn : k = n
    all_goals simp [posProj, hn, stdBasisZ_apply, hkn]
  rw [← heq]
  exact posProj_mem_nonpositive_orthogonal _

def positiveFourierVector (n : {n : ℤ // 0 < n}) :
    nonpositiveFourierSubspaceᗮ :=
  ⟨stdBasisZ n, stdBasisZ_mem_nonpositive_orthogonal n.property⟩

theorem orthonormal_positiveFourierVector :
    Orthonormal ℂ positiveFourierVector := (stdBasisZ.orthonormal.comp Subtype.val Subtype.val_injective).codRestrict
    nonpositiveFourierSubspaceᗮ
    (fun n => stdBasisZ_mem_nonpositive_orthogonal n.property)

theorem positiveFourierVector_span_orthogonal_eq_bot :
    (Submodule.span ℂ (range positiveFourierVector))ᗮ = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro b hb
  apply Subtype.ext
  apply lp.ext
  funext n
  by_cases hn : 0 < n
  · have h := (Submodule.mem_orthogonal _ _).mp hb
      (positiveFourierVector ⟨n, hn⟩)
      (Submodule.subset_span (⟨⟨n, hn⟩, rfl⟩))
    change ⟪stdBasisZ n, b⟫_ℂ = 0 at h
    simp_all [stdBasisZ_apply, lp.inner_single_left]
  · exact nonpositive_orthogonal_coefficient_eq_zero b (le_of_not_gt hn)

def positiveFourierHilbertBasis :
    HilbertBasis {n : ℤ // 0 < n} ℂ nonpositiveFourierSubspaceᗮ :=
  HilbertBasis.mkOfOrthogonalEqBot orthonormal_positiveFourierVector
    positiveFourierVector_span_orthogonal_eq_bot

@[simp] theorem positiveFourierHilbertBasis_apply (n : {n : ℤ // 0 < n}) :
    positiveFourierHilbertBasis n = positiveFourierVector n := congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot
    orthonormal_positiveFourierVector positiveFourierVector_span_orthogonal_eq_bot) n

/-- The linear subspace of sequences having genuinely finite support. -/
def finiteFourierSubmodule : Submodule ℂ L2Z where
  carrier := {b | (Function.support (b : ℤ → ℂ)).Finite}
  zero_mem' := Set.finite_empty.subset fun n hn => hn (by simp)
  add_mem' := by
    intro b d hb hd
    refine (hb.union hd).subset ?_
    intro n hn
    by_contra h
    have hb0 : b n = 0 := by
      simp_all
    have hd0 : d n = 0 := by
      simp_all
    exact hn (by simp_all)
  smul_mem' := by
    intro a b hb
    refine hb.subset ?_
    norm_num

theorem stdBasisZ_mem_finiteFourierSubmodule (n : ℤ) :
    stdBasisZ n ∈ finiteFourierSubmodule := by
  refine (finite_singleton n).subset ?_
  intro k hk
  by_contra hkn
  simp_all [stdBasisZ_apply]

theorem finite_support_of_mem_span_stdBasisZ (hb : b ∈ Submodule.span ℂ (range stdBasisZ)) :
    (Function.support b).Finite := by
  apply (show Submodule.span ℂ (range stdBasisZ) ≤ finiteFourierSubmodule from ?_) hb
  apply Submodule.span_le.mpr
  rintro _ ⟨n, rfl⟩
  exact stdBasisZ_mem_finiteFourierSubmodule n

theorem finite_support_of_mem_span_positiveFourierHilbertBasis
    {b : nonpositiveFourierSubspaceᗮ}
    (hb : b ∈ Submodule.span ℂ (range positiveFourierHilbertBasis)) :
    (Function.support (b : ℤ → ℂ)).Finite := by
  have hle : Submodule.span ℂ (range positiveFourierHilbertBasis) ≤
      finiteFourierSubmodule.comap nonpositiveFourierSubspaceᗮ.subtype := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    rw [positiveFourierHilbertBasis_apply]
    exact stdBasisZ_mem_finiteFourierSubmodule n
  exact hle hb

theorem isSobolevSeq_of_finite_fourier_support (s : ℝ) {b : L2Z}
    (hb : (Function.support b).Finite) :
    IsSobolevSeq s b := by
  apply summable_of_finite_support
  refine hb.subset ?_
  intro n hn
  simp_all

end PolyaNeumann

end
