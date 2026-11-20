module

public import RequestProject.LocalConformalHardySubspace
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-! Finitely supported Fourier sequences form a submodule containing the standard basis. -/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set
open scoped InnerProductSpace

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
    simp

theorem stdBasisZ_mem_finiteFourierSubmodule (n : ℤ) :
    stdBasisZ n ∈ finiteFourierSubmodule := by
  refine (finite_singleton n).subset ?_
  intro k hk
  by_contra hkn
  have hkn' : k ≠ n := by assumption
  exact hk (by simp [stdBasisZ_apply, hkn'])

theorem finite_support_of_mem_span_stdBasisZ {b : L2Z}
    (hb : b ∈ Submodule.span ℂ (range stdBasisZ)) :
    (Function.support (b : ℤ → ℂ)).Finite := by
  apply (show Submodule.span ℂ (range stdBasisZ) ≤ finiteFourierSubmodule from ?_) hb
  apply Submodule.span_le.mpr
  rintro _ ⟨n, rfl⟩
  exact stdBasisZ_mem_finiteFourierSubmodule n

theorem isSobolevSeq_of_finite_fourier_support (s : ℝ) {b : L2Z}
    (hb : (Function.support (b : ℤ → ℂ)).Finite) :
    IsSobolevSeq s (b : ℤ → ℂ) := by
  apply summable_of_finite_support
  refine hb.subset ?_
  intro n hn
  simp_all

end PolyaNeumann

end
