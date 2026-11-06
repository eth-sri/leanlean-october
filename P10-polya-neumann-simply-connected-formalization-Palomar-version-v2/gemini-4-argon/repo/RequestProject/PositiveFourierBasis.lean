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


noncomputable section

namespace PolyaNeumann

open Set
open scoped InnerProductSpace

theorem stdBasisZ_mem_nonpositive_orthogonal  (hn : 0 < n) :
    stdBasisZ n ∈ nonpositiveFourierSubspaceᗮ := by
  rw [← (show posProj (stdBasisZ n) = stdBasisZ n by
    apply lp.ext
    funext k
    by_cases hkn : k = n
    · subst k
      simp [posProj, hn]
    · simp [posProj, stdBasisZ_apply, hkn])]
  exact posProj_mem_nonpositive_orthogonal _

def positiveFourierVector (n : {n : ℤ // 0 < n}) :
    nonpositiveFourierSubspaceᗮ :=
  ⟨stdBasisZ n, stdBasisZ_mem_nonpositive_orthogonal n.property⟩

theorem orthonormal_positiveFourierVector :
    Orthonormal ℂ positiveFourierVector := by
  exact (stdBasisZ.orthonormal.comp Subtype.val Subtype.val_injective).codRestrict
    nonpositiveFourierSubspaceᗮ
    (fun n => stdBasisZ_mem_nonpositive_orthogonal n.property)

theorem positiveFourierVector_span_orthogonal_eq_bot :
    (Submodule.span ℂ (range positiveFourierVector))ᗮ = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro b hb
  apply Subtype.ext
  apply lp.ext
  funext n
  change (b : L2Z) n = 0
  by_cases hn : 0 < n
  · have h := (Submodule.mem_orthogonal _ _).mp hb
      (positiveFourierVector ⟨n, hn⟩)
      (Submodule.subset_span (show positiveFourierVector ⟨n, hn⟩ ∈
        range positiveFourierVector from ⟨⟨n, hn⟩, rfl⟩))
    change ⟪stdBasisZ n, b⟫_ℂ = 0 at h
    simpa [stdBasisZ_apply, lp.inner_single_left] using h
  · exact (by
    simpa [stdBasisZ_apply, lp.inner_single_left] using ((Submodule.mem_orthogonal _ _).mp b.property (stdBasisZ n) (by
      intro k hk
      simp [stdBasisZ_apply, show k ≠ n by omega])))

def positiveFourierHilbertBasis :
    HilbertBasis {n : ℤ // 0 < n} ℂ nonpositiveFourierSubspaceᗮ :=
  HilbertBasis.mkOfOrthogonalEqBot orthonormal_positiveFourierVector
    positiveFourierVector_span_orthogonal_eq_bot

def finiteFourierSubmodule : Submodule ℂ L2Z where
  carrier := {b | (Function.support (b : ℤ → ℂ)).Finite}
  zero_mem' := Set.finite_empty.subset fun n hn => hn (by simp)
  add_mem' := by
    intro b d hb hd
    refine (hb.union hd).subset ?_
    intro n hn
    by_contra h
    have hb0 : b n = 0 := by
      by_contra hb0
      exact h (Or.inl hb0)
    have hd0 : d n = 0 := by
      by_contra hd0
      exact h (Or.inr hd0)
    exact hn (by simp [hb0, hd0])
  smul_mem' := by
    intro a b hb
    refine hb.subset ?_
    intro n hn
    by_contra hb0
    exact hn (by simp [not_not.mp hb0])

theorem stdBasisZ_mem_finiteFourierSubmodule n :
    stdBasisZ n ∈ finiteFourierSubmodule := by
  refine (finite_singleton n).subset ?_
  intro k hk
  by_contra hkn
  exact hk (by simp [stdBasisZ_apply, show k ≠ n by simpa using hkn])

theorem finite_support_of_mem_span_stdBasisZ 
    (hb : b ∈ Submodule.span ℂ (range stdBasisZ)) :
    (Function.support (b : ℤ → ℂ)).Finite := by
  apply (show Submodule.span ℂ (range stdBasisZ) ≤ finiteFourierSubmodule from ?_) hb
  apply Submodule.span_le.mpr
  rintro _ ⟨n, rfl⟩
  exact stdBasisZ_mem_finiteFourierSubmodule n

theorem finite_support_of_mem_span_positiveFourierHilbertBasis
    
    (hb : b ∈ Submodule.span ℂ (range positiveFourierHilbertBasis)) :
    (Function.support ((b : L2Z) : ℤ → ℂ)).Finite := by
  exact (show Submodule.span ℂ (range positiveFourierHilbertBasis) ≤ finiteFourierSubmodule.comap nonpositiveFourierSubspaceᗮ.subtype by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    change (positiveFourierHilbertBasis n : L2Z) ∈ finiteFourierSubmodule
    have h_inl n : positiveFourierHilbertBasis n = positiveFourierVector n := by
      exact congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot
        orthonormal_positiveFourierVector positiveFourierVector_span_orthogonal_eq_bot) n
    rw [h_inl]
    exact stdBasisZ_mem_finiteFourierSubmodule n) hb

theorem isSobolevSeq_of_finite_fourier_support s 
    (hb : (Function.support b).Finite) :
    IsSobolevSeq s (b : ℤ → ℂ) := by
  apply summable_of_finite_support
  refine hb.subset ?_
  intro n hn
  by_contra hb0
  exact hn (by simp [not_not.mp hb0])

end PolyaNeumann

end
